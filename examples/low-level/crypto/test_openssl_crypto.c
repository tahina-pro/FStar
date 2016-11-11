#include "testutils.h"
#include <time.h>
#include <openssl/evp.h>
#include <sodium.h>

#define PLAINLEN (16*1024)
#define AADLEN (12)
#define NONCELEN 24
#define KEYLEN 32
#define IVLEN 12

uint8_t nonce[NONCELEN] = {
  0x00, 0x01, 0x02, 0x03,
  0x04, 0x05, 0x06, 0x07,
  0x08, 0x09, 0x10, 0x11,
  0x12, 0x13, 0x14, 0x15,
  0x16, 0x17, 0x18, 0x19,
  0x20, 0x21, 0x22, 0x23,
};

uint8_t key[KEYLEN] = {
  0x85, 0xd6, 0xbe, 0x78,
  0x57, 0x55, 0x6d, 0x33,
  0x7f, 0x44, 0x52, 0xfe,
  0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a,
  0xfb, 0x0d, 0xb2, 0xfd,
  0x4a, 0xbf, 0xf6, 0xaf,
  0x41, 0x49, 0xf5, 0x1b
};

uint8_t sk[KEYLEN] = {
  0x85, 0xd6, 0xbe, 0x78,
  0x57, 0x55, 0x6d, 0x33,
  0x7f, 0x44, 0x52, 0xfe,
  0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a,
  0xfb, 0x0d, 0xb2, 0xfd,
  0x4a, 0xbf, 0xf6, 0xaf,
  0x41, 0x49, 0xf5, 0x1c
};

uint8_t aad[AADLEN] = {
  0x50, 0x51, 0x52, 0x53,
  0xc0, 0xc1, 0xc2, 0xc3,
  0xc4, 0xc5, 0xc6, 0xc7
};

uint8_t ivBuffer[IVLEN] = {
  0x07, 0x00, 0x00, 0x00,
  0x40, 0x41, 0x42, 0x43,
  0x44, 0x45, 0x46, 0x47
};

#define ROUNDS 1000

#define AES_GCM 0
#define CHACHA_POLY 1

void print_results(char *txt, double t1, unsigned long long d1, int rounds, int plainlen){
  printf("%s Testing 2^14 bytes block computations\n", txt);
  printf("%s %.2fcycles/byte\n", txt, (double)d1/plainlen/rounds);
  printf("%s user time: %f (%fns/byte)\n", txt, t1, t1*1000000/plainlen/rounds);
}

int openssl_aead_encrypt(unsigned char *plaintext, int plaintext_len, unsigned char *aad,
                         int aad_len, unsigned char *key, unsigned char *iv,
                         unsigned char *ciphertext, unsigned char *tag, int cipher){
  EVP_CIPHER_CTX *ctx;
  int len;
  int ciphertext_len;
  /* Create and initialise the context */
  if(!(ctx = EVP_CIPHER_CTX_new())) return EXIT_FAILURE;
  /* Initialise the encryption operation. */
  if (cipher == AES_GCM) {
    if(1 != EVP_EncryptInit_ex(ctx, EVP_aes_256_gcm(), NULL, NULL, NULL))
      return EXIT_FAILURE;
  } else {
    if(1 != EVP_EncryptInit_ex(ctx, EVP_chacha20_poly1305(), NULL, NULL, NULL))
      return EXIT_FAILURE;
  }

  clock_t c1, c2;
  double t1, t2;
  unsigned long long a,b,d1,d2;
  c1 = clock();
  a = rdtsc();
  for (int j = 0; j < ROUNDS; j++){
    if(1 != EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_IVLEN, 16, NULL))
      return EXIT_FAILURE;
    if(1 != EVP_EncryptInit_ex(ctx, NULL, NULL, key, iv)) return EXIT_FAILURE;
    if(1 != EVP_EncryptUpdate(ctx, NULL, &len, aad, aad_len))
      return EXIT_FAILURE;
    if(1 != EVP_EncryptUpdate(ctx, ciphertext, &len, plaintext, plaintext_len))
      return EXIT_FAILURE;
    ciphertext_len = len;
    if(1 != EVP_EncryptFinal_ex(ctx, ciphertext + len, &len)) return EXIT_FAILURE;
    ciphertext_len += len;
    if(1 != EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_GET_TAG, 16, tag))
      return EXIT_FAILURE;
  }
  b = rdtsc();
  c2 = clock();
  d1 = b - a;
  t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  print_results(cipher == AES_GCM ? "[Openssl-AES256GCM]" : "[Openssl-CHACHA20POLY1305]", t1, d1, ROUNDS, PLAINLEN);
  EVP_CIPHER_CTX_free(ctx);
  return ciphertext_len;
}


void test_sodium_poly1305(unsigned char* plain, unsigned char* cipher){
  clock_t c1, c2;
  double t1, t2;
  unsigned long long a,b,d1,d2;
  c1 = clock();
  a = rdtsc();
  for (int j = 0; j < ROUNDS; j++) crypto_onetimeauth(cipher, plain, PLAINLEN, key);
  b = rdtsc();
  c2 = clock();
  d1 = b - a;
  t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  print_results("[Libsodium-POLY1305]", t1, d1, ROUNDS, PLAINLEN);
}


void test_sodium_chacha20(unsigned char* plain, unsigned char* cipher){
  clock_t c1, c2;
  double t1, t2;
  unsigned long long a,b,d1,d2;
  c1 = clock();
  a = rdtsc();
  for (int j = 0; j < ROUNDS; j++) crypto_stream_chacha20_ietf_xor(cipher, plain, PLAINLEN, nonce, key);
  b = rdtsc();
  c2 = clock();
  d1 = b - a;
  t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  print_results("[Libsodium-CHACHA20]", t1, d1, ROUNDS, PLAINLEN);
}


void test_sodium_aeadchachapoly(unsigned char* plain, unsigned char* cipher){
  clock_t c1, c2;
  double t1, t2;
  unsigned long long a,b,d1,d2, cipher_len;
  c1 = clock();
  a = rdtsc();
  for (int j = 0; j < ROUNDS; j++) crypto_aead_chacha20poly1305_ietf_encrypt(cipher, &cipher_len,
                                          plain, PLAINLEN,
                                          aad, AADLEN,
                                          NULL, nonce, key);

  b = rdtsc();
  c2 = clock();
  d1 = b - a;
  t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  print_results("[Libsodium-CHACHA20POLY1305]", t1, d1, ROUNDS, PLAINLEN);
}


void test_crypto_aead(){
  void *plain = malloc(PLAINLEN), *cipher = malloc(PLAINLEN+16);
  uint8_t mac[16];
  openssl_aead_encrypt(plain, PLAINLEN, aad, AADLEN, key, ivBuffer, cipher, mac, AES_GCM);
  openssl_aead_encrypt(plain, PLAINLEN, aad, AADLEN, key, ivBuffer, cipher, mac, CHACHA_POLY);
  test_sodium_poly1305(plain, cipher);
  test_sodium_chacha20(plain, cipher);
  test_sodium_aeadchachapoly(plain, cipher);
}


int main(){
  test_crypto_aead();
  return EXIT_SUCCESS;
}
