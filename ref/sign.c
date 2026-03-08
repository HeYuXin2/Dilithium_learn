#include <stdint.h>
#include "params.h"
#include "sign.h"
#include "packing.h"
#include "polyvec.h"
#include "poly.h"
#include "randombytes.h"
#include "symmetric.h"
#include "fips202.h"
#include <stdio.h>

/*************************************************
* Name:        crypto_sign_keypair
*
* Description: Generates public and private key.
*
* Arguments:   - uint8_t *pk: pointer to output public key (allocated
*                             array of CRYPTO_PUBLICKEYBYTES bytes)
*              - uint8_t *sk: pointer to output private key (allocated
*                             array of CRYPTO_SECRETKEYBYTES bytes)
*
* Returns 0 (success)
**************************************************/
//生成公钥和私钥
int crypto_sign_keypair(uint8_t *pk, uint8_t *sk) {
  uint8_t seedbuf[2*SEEDBYTES + CRHBYTES];  //种子缓冲区
  uint8_t tr[TRBYTES];            //公钥哈希值  
  const uint8_t *rho, *rhoprime, *key;    
  polyvecl mat[K];                 //l*k多项式矩阵
  polyvecl s1, s1hat;           //长度为l短向量s1, s1的NTT变换  
  polyveck s2, t1, t0;           //长度为k短向量s2, 公钥t1, t0

  /* Get randomness for rho, rhoprime and key */
  randombytes(seedbuf, SEEDBYTES);  //生成随机种子
  seedbuf[SEEDBYTES+0] = K;       
  seedbuf[SEEDBYTES+1] = L;       //种子末尾加上K和L以区分不同安全等级
  shake256(seedbuf, 2*SEEDBYTES + CRHBYTES, seedbuf, SEEDBYTES+2);  //种子拓展函数，34位拓展到128位
  rho = seedbuf;                     //rho:前32字节指针
  rhoprime = rho + SEEDBYTES;     //rhoprime:中间64字节指针
  key = rhoprime + CRHBYTES;      //key:后32字节指针

  /* Expand matrix */
  polyvec_matrix_expand(mat, rho);  //根据矩阵种子rho生成多项式矩阵

  /* Sample short vectors s1 and s2 */
  /*平均采样多项式，来自随机种子rhoprime和随机噪声，保证了参数选择的平均性和可复现性
  s1长度为L，s2长度为K,系数在[-ETA，ETA]范围内,共256系数，每个系数占3个字节，但后续可压缩至3比特
  随机字节流由steam128函数生成，是shake128的一个变种，使用rhoprime作为种子，并通过不同的nonce值确保生成不同的多项式
  */
  polyvecl_uniform_eta(&s1, rhoprime, 0); //根据rhoprime和nonce=0生成长度为L的多项式向量s1
  polyveck_uniform_eta(&s2, rhoprime, L); //根据rhoprime和nonce=L生成长度为K的多项式向量s2

  /* Matrix-vector multiplication */
  s1hat = s1;                 //复制s1到s1hat
  polyvecl_ntt(&s1hat);     //对s1hat中的每个多项式进行NTT变换
  polyvec_matrix_pointwise_montgomery(&t1, mat, &s1hat);  //计算矩阵mat和向量s1hat的乘积，结果存储在t1中
  polyveck_reduce(&t1);       //对t1中的每个多项式系数进行模q约减
  polyveck_invntt_tomont(&t1);  //对t1中的每个多项式进行逆NTT变换并转换回常规表示

  /* Add error vector s2 */
  polyveck_add(&t1, &t1, &s2);  //将短向量s2加到t1上

  /* Extract t1 and write public key */
  polyveck_caddq(&t1);        //将t1中的系数约减到[-q/2,q/2]范围内
  /*将t1分解为高位t1，t1长10bit，t0为后14bit，截取高位的目的是为了压缩公钥*/
  polyveck_power2round(&t1, &t0, &t1);  //将t1分解为高位t1和低位t0
  pack_pk(pk, rho, &t1);      //将公钥打包存储到pk中

  /* Compute H(rho, t1) and write secret key */
  shake256(tr, TRBYTES, pk, CRYPTO_PUBLICKEYBYTES);   //计算公钥的哈希值tr，约束到64位
  pack_sk(sk, rho, tr, key, &t0, &s1, &s2);           //将私钥打包存储到sk中,s1和s2的系数在这一步会从3字节压缩到3比特

  return 0;
}

/*************************************************
* Name:        crypto_sign_signature_internal
*
* Description: Computes signature. Internal API.
*
* Arguments:   - uint8_t *sig:   pointer to output signature (of length CRYPTO_BYTES)
*              - size_t *siglen: pointer to output length of signature
*              - uint8_t *m:     pointer to message to be signed
*              - size_t mlen:    length of message
*              - uint8_t *pre:   pointer to prefix string
*              - size_t prelen:  length of prefix string
*              - uint8_t *rnd:   pointer to random seed
*              - uint8_t *sk:    pointer to bit-packed secret key
*
* Returns 0 (success)
**************************************************/
int crypto_sign_signature_internal(uint8_t *sig,
                                   size_t *siglen,
                                   const uint8_t *m,
                                   size_t mlen,
                                   const uint8_t *pre,
                                   size_t prelen,
                                   const uint8_t rnd[RNDBYTES],
                                   const uint8_t *sk)
{
  unsigned int n;
  uint8_t seedbuf[2*SEEDBYTES + TRBYTES + 2*CRHBYTES];   //种子缓冲区
  uint8_t *rho, *tr, *key, *mu, *rhoprime;               //指向种子缓冲区不同部分的指针
  uint16_t nonce = 0;
  polyvecl mat[K], s1, y, z;          //多项式矩阵mat, 长度为L的多项式向量s1, y, z
  polyveck t0, s2, w1, w0, h;     //长度为K的多项式向量t0, s2, w1, w0, h
  poly cp;                      //挑战多项式cp
  keccak_state state;             //SHAKE256状态变量

  rho = seedbuf;                 //rho:前32字节指针
  tr = rho + SEEDBYTES;         //tr:中间64字节指针
  key = tr + TRBYTES;       //key:后32字节指针
  mu = key + SEEDBYTES;        //mu:后64字节指针
  rhoprime = mu + CRHBYTES;   //rhoprime:后64字节指针
  unpack_sk(rho, tr, key, &t0, &s1, &s2, sk); //从私钥sk中解包出各个部分

  /* Compute mu = CRH(tr, pre, msg) */
  shake256_init(&state);            
  shake256_absorb(&state, tr, TRBYTES);     //tr是公钥的哈希值，用于绑定签名和公钥
  shake256_absorb(&state, pre, prelen);     //pre是上下文信息，用于区分相同信息下不同的签名场景
  shake256_absorb(&state, m, mlen);         //m是要签名的消息
  shake256_finalize(&state);
  shake256_squeeze(mu, CRHBYTES, &state);   //mu是消息摘要，结合tr和消息内容生成，确保签名与消息内容绑定

  /* Compute rhoprime = CRH(key, rnd, mu) */
  shake256_init(&state);
  shake256_absorb(&state, key, SEEDBYTES);  //key是私钥中的随机种子，用于生成签名的随机部分，保证了每次签名的唯一性和安全性
  shake256_absorb(&state, rnd, RNDBYTES);   //rnd是外部提供的随机数，可以增加签名的随机性，防止重放攻击
  shake256_absorb(&state, mu, CRHBYTES);    //加上μ一起进行哈希
  shake256_finalize(&state);
  shake256_squeeze(rhoprime, CRHBYTES, &state);   //哈希后得到rhoprime，用于后续生成签名的随机多项式向量y

  /* Expand matrix and transform vectors */
  polyvec_matrix_expand(mat, rho);  //根据矩阵种子rho生成多项式矩阵
  polyvecl_ntt(&s1);           //对s1中的每个多项式进行NTT变换
  polyveck_ntt(&s2);         //对s2中的每个多项式进行NTT变换
  polyveck_ntt(&t0);         //对t0中的每个多项式进行NTT变换

rej:
  /* Sample intermediate vector y */
  polyvecl_uniform_gamma1(&y, rhoprime, nonce++); //根据rhoprime和nonce生成长度为L的随机多项式向量y，系数取值在[-Gamma+1,Gamma]

  /* Matrix-vector multiplication */
  z = y;                   //复制y到z
  polyvecl_ntt(&z);        //对z中的每个多项式进行NTT变换
  polyvec_matrix_pointwise_montgomery(&w1, mat, &z);  //计算矩阵mat和向量z的乘积，结果存储在w1中
  polyveck_reduce(&w1);      //对w1中的每个多项式系数进行模q约减
  polyveck_invntt_tomont(&w1);  //对w1中的每个多项式进行逆NTT变换并转换回常规表示,w1即为承诺

  /* Decompose w and call the random oracle */
  polyveck_caddq(&w1);      //将w1中的系数约减到[-q/2,q/2]范围内
  polyveck_decompose(&w1, &w0, &w1);  //将w1分解为高位w1和低位w0，w1长6bit?截取高位的目的是为了压缩承诺
  polyveck_pack_w1(sig, &w1); //将w1打包存储到sig中，将所有高6位系数?打包成紧凑的字节流

  shake256_init(&state);  
  shake256_absorb(&state, mu, CRHBYTES);
  shake256_absorb(&state, sig, K*POLYW1_PACKEDBYTES);
  shake256_finalize(&state);
  shake256_squeeze(sig, CTILDEBYTES, &state); //HASH(mu,w1)得到挑战值
  poly_challenge(&cp, sig); //根据sig中的挑战值生成挑战多项式cp
  poly_ntt(&cp);               //对cp进行NTT变换

  /* Compute z, reject if it reveals secret */
  polyvecl_pointwise_poly_montgomery(&z, &cp, &s1); //计算cp和s1的点乘，结果存储在z中
  polyvecl_invntt_tomont(&z);  //对z中的每个多项式进行逆NTT变换并转换回常规表示
  polyvecl_add(&z, &z, &y);     //将y加到z上
  polyvecl_reduce(&z);      //对z中的每个多项式系数进行模q约减
  if(polyvecl_chknorm(&z, GAMMA1 - BETA)){
    printf("\nz norm too big");
    goto rej;
  }     
  //检查z的系数是否超出范围，若超出则重新采样

  /* Check that subtracting cs2 does not change high bits of w and low bits
   * do not reveal secret information */
  polyveck_pointwise_poly_montgomery(&h, &cp, &s2);   //计算cp和s2的点乘，结果存储在h中
  polyveck_invntt_tomont(&h);         //对h中的每个多项式进行逆NTT变换并转换回常规表示
  polyveck_sub(&w0, &w0, &h);       //将h从w0中减去，即保证在不改变高位w1的前提下，使得验签时能正常验证
  polyveck_reduce(&w0);     //对w0中的每个多项式系数进行模q约减
  if(polyveck_chknorm(&w0, GAMMA2 - BETA))  {
    printf("\nw0 too big");
    goto rej;
  }
  //检查w0的系数是否超出范围，若超出则重新采样

  /* Compute hints for w1 */
  polyveck_pointwise_poly_montgomery(&h, &cp, &t0);   //
  polyveck_invntt_tomont(&h); 
  polyveck_reduce(&h);     
  if(polyveck_chknorm(&h, GAMMA2)){
    printf("\nh too big");
    goto rej;
  }  //验证h是否为短向量
    //检查h的系数是否超出范围，若超出则重新采样

  polyveck_add(&w0, &w0, &h);   //将h加回w0中，对w0进行修正，使得验签时能正常验证
  n = polyveck_make_hint(&h, &w0, &w1); //根据w0和w1生成提示h，并返回提示的数量n
  if(n > OMEGA){
    printf("\nhint too much");
    goto rej;
  } //检查提示的数量是否超过OMEGA，若超过则重新采样
  

  /* Write signature */
  pack_sig(sig, sig, &z, &h); //将z和h打包存储到sig中，sig的前32字节存储挑战值，后面存储z和h
  printf("\nsign success!");
  *siglen = CRYPTO_BYTES;     //设置输出签名长度
  return 0;
}

/*************************************************
* Name:        crypto_sign_signature
*
* Description: Computes signature.
*
* Arguments:   - uint8_t *sig:   pointer to output signature (of length CRYPTO_BYTES)
*              - size_t *siglen: pointer to output length of signature
*              - uint8_t *m:     pointer to message to be signed
*              - size_t mlen:    length of message
*              - uint8_t *ctx:   pointer to contex string
*              - size_t ctxlen:  length of contex string
*              - uint8_t *sk:    pointer to bit-packed secret key
*
* Returns 0 (success) or -1 (context string too long)
**************************************************/
//计算签名函数，需要加密信息和上下文信息，内部调用crypto_sign_signature_internal函数实现签名计算
int crypto_sign_signature(uint8_t *sig,
                          size_t *siglen,
                          const uint8_t *m,
                          size_t mlen,
                          const uint8_t *ctx,
                          size_t ctxlen,
                          const uint8_t *sk)
{
  size_t i;
  uint8_t pre[257]; //前缀缓冲区，包含一个字节的标志位和一个字节的上下文长度，以及最多255字节的上下文信息
  uint8_t rnd[RNDBYTES];  //随机数缓冲区，用于生成签名的随机部分

  if(ctxlen > 255)  //上下文信息长度不能超过255字节
    return -1;

  /* Prepare pre = (0, ctxlen, ctx) */
  pre[0] = 0;
  pre[1] = ctxlen;
  for(i = 0; i < ctxlen; i++)
    pre[2 + i] = ctx[i];

#ifdef DILITHIUM_RANDOMIZED_SIGNING //如果启用随机化签名，则生成随机数rnd，否则将rnd置零
  randombytes(rnd, RNDBYTES);
#else
  for(i=0;i<RNDBYTES;i++)
    rnd[i] = 0;
#endif

  crypto_sign_signature_internal(sig,siglen,m,mlen,pre,2+ctxlen,rnd,sk);  //调用内部签名函数计算签名
  return 0;
}

/*************************************************
* Name:        crypto_sign
*
* Description: Compute signed message.
*
* Arguments:   - uint8_t *sm: pointer to output signed message (allocated
*                             array with CRYPTO_BYTES + mlen bytes),
*                             can be equal to m
*              - size_t *smlen: pointer to output length of signed
*                               message
*              - const uint8_t *m: pointer to message to be signed
*              - size_t mlen: length of message
*              - const uint8_t *ctx: pointer to context string
*              - size_t ctxlen: length of context string
*              - const uint8_t *sk: pointer to bit-packed secret key
*
* Returns 0 (success) or -1 (context string too long)
**************************************************/
//计算带有消息的签名函数，输出包含签名和消息的组合
int crypto_sign(uint8_t *sm,
                size_t *smlen,
                const uint8_t *m,
                size_t mlen,
                const uint8_t *ctx,
                size_t ctxlen,
                const uint8_t *sk)
{
  int ret;
  size_t i;

  for(i = 0; i < mlen; ++i)
    sm[CRYPTO_BYTES + mlen - 1 - i] = m[mlen - 1 - i];
  ret = crypto_sign_signature(sm, smlen, sm + CRYPTO_BYTES, mlen, ctx, ctxlen, sk); //计算签名并将签名存储在sm的前CRYPTO_BYTES字节中，消息存储在后面
  *smlen += mlen;
  return ret;
}

/**
 * 名称：my_crypto_sign
 * 描述：重写签名函数，学习用
 * 参数：与前文一致
 * 返回值：与前文一致
 */
int my_crypto_sign(uint8_t *sm,
                size_t *smlen,
                const uint8_t *m,
                size_t mlen,
                const uint8_t *ctx,
                size_t ctxlen,
                const uint8_t *sk)
{
  uint8_t pre[257];
  uint8_t rnd[RNDBYTES];
  uint8_t buf[2*SEEDBYTES + TRBYTES + 2*CRHBYTES + CTILDEBYTES];
  uint16_t nonce = 0;
  uint8_t *tr, *rho, *key, *miu, *yseed, *c;
  polyveck t0, s2, w, w1, w0, h;
  polyvecl s1, y, mat[K], z;
  poly cp;
  keccak_state state;
  tr = buf;
  miu = tr + TRBYTES;
  key = miu + CRHBYTES;
  yseed = key + SEEDBYTES;
  rho = yseed + CRHBYTES;
  c = rho + SEEDBYTES;
  size_t i;
  
  if(ctxlen > 255)
    return -1;

  //sm为消息加签名的存储区，先复制消息部分再将签名存储在前面
  for(i=0;i<mlen;++i)
    sm[CRYPTO_BYTES + i] = m[i];
  pre[0] = 0;
  pre[1] = ctxlen;
  for(i = 0; i < ctxlen; ++i)
    pre[2+i] = ctx[i];
  //随机化签名启用
#ifdef DILITHIUM_RANDOMIZED_SIGNING 
  randombytes(rnd,RNDBYTES);
#else
  for(i = 0; i < RNDBYTES; ++i)
    rnd[i] = 0;
#endif
  unpack_sk(rho, tr, key, &t0, &s1, &s2, sk); //从私钥sk中解包出各个部分
  //生成消息摘要
  shake256_init(&state);
  shake256_absorb(&state, tr, TRBYTES);
  shake256_absorb(&state, pre, 2+ctxlen);
  shake256_absorb(&state, m, mlen);
  shake256_finalize(&state);
  shake256_squeeze(miu, CRHBYTES, &state);

  //生成随机向量y的种子
  shake256_init(&state);
  shake256_absorb(&state, key, SEEDBYTES);
  shake256_absorb(&state, rnd, RNDBYTES);
  shake256_absorb(&state, miu, CRHBYTES);
  shake256_finalize(&state);
  shake256_squeeze(yseed, CRHBYTES, &state);

  //提前将一些多项式ntt处理，避免反复进行ntt
  polyvec_matrix_expand(mat, rho);
  polyvecl_ntt(&s1);
  polyveck_ntt(&s2);
  polyveck_ntt(&t0);
rej:
  //计算承诺
  polyvecl_uniform_gamma1(&y, yseed, nonce++);
  z = y;
  polyvecl_ntt(&z);
  polyvec_matrix_pointwise_montgomery(&w, mat, &z);
  polyveck_reduce(&w);
  polyveck_invntt_tomont(&w);
  polyveck_caddq(&w);

  //生成挑战值,以及挑战多项式
  polyveck_decompose(&w1, &w0, &w);
  polyveck_pack_w1(sm, &w1);
  shake256_init(&state);
  shake256_absorb(&state, miu, CRHBYTES);
  shake256_absorb(&state, sm, K*POLYW1_PACKEDBYTES);
  shake256_finalize(&state);
  shake256_squeeze(c, CTILDEBYTES, &state);
  poly_challenge(&cp, c);

  //计算响应z
  poly_ntt(&cp);
  polyvecl_pointwise_poly_montgomery(&z, &cp, &s1);
  polyvecl_reduce(&z);
  polyvecl_invntt_tomont(&z);
  polyvecl_add(&z, &z, &y);
  polyvecl_reduce(&z);

  //响应z的系数检查
  if(polyvecl_chknorm(&z, GAMMA1 - BETA)){
    printf("\nz norm error");
    goto rej;
  }
    
  //计算提示h，对w0进行修正,减去cs2
  polyveck_pointwise_poly_montgomery(&h, &cp, &s2);
  polyveck_reduce(&h);
  polyveck_invntt_tomont(&h);
  polyveck_sub(&w0, &w0, &h);
  polyveck_reduce(&w0);
  if(polyveck_chknorm(&w0, GAMMA2 - BETA)){
    printf("\nw0 too big");
    goto rej;
  }  //检查系数是为了防止溢出到高位？
    

  //修正加上ct0
  polyveck_pointwise_poly_montgomery(&h, &cp, &t0);
  // polyveck_reduce(&h);
  polyveck_invntt_tomont(&h);
  if(polyveck_chknorm(&h, GAMMA2)){
    printf("\n h too big");
    goto rej;
  }
  polyveck_add(&w0, &w0, &h);

  //生成提示并检查提示数量
  i = polyveck_make_hint(&h, &w0, &w1);
  if(i > OMEGA){
    printf("\nhint too much");
    goto rej;
  }
    
  //打包签名并加上签名长度
  pack_sig(sm, c, &z, &h);
  printf("\nsign success!");
  *smlen = CRYPTO_BYTES;
  *smlen += mlen; //更新签名消息组合的长度
  return 0;
}

/*************************************************
* Name:        crypto_sign_verify_internal
*
* Description: Verifies signature. Internal API.
*
* Arguments:   - uint8_t *m: pointer to input signature
*              - size_t siglen: length of signature
*              - const uint8_t *m: pointer to message
*              - size_t mlen: length of message
*              - const uint8_t *pre: pointer to prefix string
*              - size_t prelen: length of prefix string
*              - const uint8_t *pk: pointer to bit-packed public key
*
* Returns 0 if signature could be verified correctly and -1 otherwise
**************************************************/
//验证签名的内部API
int crypto_sign_verify_internal(const uint8_t *sig,
                                size_t siglen,
                                const uint8_t *m,
                                size_t mlen,
                                const uint8_t *pre,
                                size_t prelen,
                                const uint8_t *pk)
{
  unsigned int i;
  uint8_t buf[K*POLYW1_PACKEDBYTES];
  uint8_t rho[SEEDBYTES];
  uint8_t mu[CRHBYTES];
  uint8_t c[CTILDEBYTES];
  uint8_t c2[CTILDEBYTES];
  poly cp;
  polyvecl mat[K], z;
  polyveck t1, w1, h;
  keccak_state state;

  if(siglen != CRYPTO_BYTES)  //验证签名长度
    return -1;

  unpack_pk(rho, &t1, pk);
  if(unpack_sig(c, &z, &h, sig))  //从输入的签名sig中解包出挑战c，向量z和提示h，如果解包失败则返回-1
    return -1;
  if(polyvecl_chknorm(&z, GAMMA1 - BETA)) //检查z的系数是否超出范围，若超出则返回-1
    return -1;

  /* Compute CRH(H(rho, t1), pre, msg) */
  shake256(mu, TRBYTES, pk, CRYPTO_PUBLICKEYBYTES);
  shake256_init(&state);
  shake256_absorb(&state, mu, TRBYTES);
  shake256_absorb(&state, pre, prelen);
  shake256_absorb(&state, m, mlen);
  shake256_finalize(&state);
  shake256_squeeze(mu, CRHBYTES, &state); //获取消息摘要μ

  /* Matrix-vector multiplication; compute Az - c2^dt1 */
  /*计算w1 = Az-c(t1*2^d)*/
  poly_challenge(&cp, c);
  polyvec_matrix_expand(mat, rho);

  polyvecl_ntt(&z);
  polyvec_matrix_pointwise_montgomery(&w1, mat, &z);

  poly_ntt(&cp);
  polyveck_shiftl(&t1);
  polyveck_ntt(&t1);
  polyveck_pointwise_poly_montgomery(&t1, &cp, &t1);

  polyveck_sub(&w1, &w1, &t1);
  polyveck_reduce(&w1);
  polyveck_invntt_tomont(&w1);

  /* Reconstruct w1 */
  /*使用提示重建w1*/
  polyveck_caddq(&w1);
  polyveck_use_hint(&w1, &w1, &h);
  polyveck_pack_w1(buf, &w1);

  /* Call random oracle and verify challenge */
  /*用消息摘要μ和重建的w1计算预测的挑战c2*/
  shake256_init(&state);
  shake256_absorb(&state, mu, CRHBYTES);
  shake256_absorb(&state, buf, K*POLYW1_PACKEDBYTES);
  shake256_finalize(&state);
  shake256_squeeze(c2, CTILDEBYTES, &state);
  /*验证挑战是否相同，相同则验签成功，不同则失败*/
  for(i = 0; i < CTILDEBYTES; ++i)
    if(c[i] != c2[i])
      return -1;

  return 0;
}

/*************************************************
* Name:        crypto_sign_verify
*
* Description: Verifies signature.
*
* Arguments:   - uint8_t *m: pointer to input signature
*              - size_t siglen: length of signature
*              - const uint8_t *m: pointer to message
*              - size_t mlen: length of message
*              - const uint8_t *ctx: pointer to context string
*              - size_t ctxlen: length of context string
*              - const uint8_t *pk: pointer to bit-packed public key
*
* Returns 0 if signature could be verified correctly and -1 otherwise
**************************************************/
//验证签名的API，包含上下文信息
int crypto_sign_verify(const uint8_t *sig,
                       size_t siglen,
                       const uint8_t *m,
                       size_t mlen,
                       const uint8_t *ctx,
                       size_t ctxlen,
                       const uint8_t *pk)
{
  size_t i;
  uint8_t pre[257];

  if(ctxlen > 255)
    return -1;

  pre[0] = 0;
  pre[1] = ctxlen;
  for(i = 0; i < ctxlen; i++)
    pre[2 + i] = ctx[i];

  return crypto_sign_verify_internal(sig,siglen,m,mlen,pre,2+ctxlen,pk);
}

/*************************************************
* Name:        crypto_sign_open
*
* Description: Verify signed message.
*
* Arguments:   - uint8_t *m: pointer to output message (allocated
*                            array with smlen bytes), can be equal to sm
*              - size_t *mlen: pointer to output length of message
*              - const uint8_t *sm: pointer to signed message
*              - size_t smlen: length of signed message
*              - const uint8_t *ctx: pointer to context tring
*              - size_t ctxlen: length of context string
*              - const uint8_t *pk: pointer to bit-packed public key
*
* Returns 0 if signed message could be verified correctly and -1 otherwise
**************************************************/
int crypto_sign_open(uint8_t *m,
                     size_t *mlen,
                     const uint8_t *sm,
                     size_t smlen,
                     const uint8_t *ctx,
                     size_t ctxlen,
                     const uint8_t *pk)
{
  size_t i;

  if(smlen < CRYPTO_BYTES)
    goto badsig;

  *mlen = smlen - CRYPTO_BYTES;
  if(crypto_sign_verify(sm, CRYPTO_BYTES, sm + CRYPTO_BYTES, *mlen, ctx, ctxlen, pk))
    goto badsig;
  else {
    /* All good, copy msg, return 0 */
    for(i = 0; i < *mlen; ++i)
      m[i] = sm[CRYPTO_BYTES + i];
    return 0;
  }

badsig:
  /* Signature verification failed */
  *mlen = 0;
  for(i = 0; i < smlen; ++i)
    m[i] = 0;

  return -1;
}

