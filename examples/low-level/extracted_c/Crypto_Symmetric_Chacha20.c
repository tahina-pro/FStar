#include "Crypto_Symmetric_Chacha20.h"

uint32_t Crypto_Symmetric_Chacha20_keylen = (uint32_t )32;

uint32_t Crypto_Symmetric_Chacha20_blocklen = (uint32_t )64;

uint32_t Crypto_Symmetric_Chacha20_ivlen = (uint32_t )12;

void
Crypto_Symmetric_Chacha20_line(uint32_t *m, uint32_t a, uint32_t b, uint32_t d, uint32_t s)
{
  uint32_t _0_37 = m[a];
  uint32_t _0_36 = m[b];
  uint32_t _0_38 = _0_37 + _0_36;
  m[a] = _0_38;
  uint32_t _0_40 = m[d];
  uint32_t _0_39 = m[a];
  uint32_t _0_41 = _0_40 ^ _0_39;
  uint32_t _0_42 = Buffer_Utils_op_Less_Less_Less(_0_41, s);
  m[d] = _0_42;
}

void
Crypto_Symmetric_Chacha20_quarter_round(
  uint32_t *m,
  uint32_t a,
  uint32_t b,
  uint32_t c,
  uint32_t d
)
{
  Crypto_Symmetric_Chacha20_line(m, a, b, d, (uint32_t )16);
  Crypto_Symmetric_Chacha20_line(m, c, d, b, (uint32_t )12);
  Crypto_Symmetric_Chacha20_line(m, a, b, d, (uint32_t )8);
  Crypto_Symmetric_Chacha20_line(m, c, d, b, (uint32_t )7);
  return;
}

void Crypto_Symmetric_Chacha20_column_round(uint32_t *m)
{
  Crypto_Symmetric_Chacha20_quarter_round(m,
    (uint32_t )0,
    (uint32_t )4,
    (uint32_t )8,
    (uint32_t )12);
  Crypto_Symmetric_Chacha20_quarter_round(m,
    (uint32_t )1,
    (uint32_t )5,
    (uint32_t )9,
    (uint32_t )13);
  Crypto_Symmetric_Chacha20_quarter_round(m,
    (uint32_t )2,
    (uint32_t )6,
    (uint32_t )10,
    (uint32_t )14);
  Crypto_Symmetric_Chacha20_quarter_round(m,
    (uint32_t )3,
    (uint32_t )7,
    (uint32_t )11,
    (uint32_t )15);
  return;
}

void Crypto_Symmetric_Chacha20_diagonal_round(uint32_t *m)
{
  Crypto_Symmetric_Chacha20_quarter_round(m,
    (uint32_t )0,
    (uint32_t )5,
    (uint32_t )10,
    (uint32_t )15);
  Crypto_Symmetric_Chacha20_quarter_round(m,
    (uint32_t )1,
    (uint32_t )6,
    (uint32_t )11,
    (uint32_t )12);
  Crypto_Symmetric_Chacha20_quarter_round(m,
    (uint32_t )2,
    (uint32_t )7,
    (uint32_t )8,
    (uint32_t )13);
  Crypto_Symmetric_Chacha20_quarter_round(m,
    (uint32_t )3,
    (uint32_t )4,
    (uint32_t )9,
    (uint32_t )14);
  return;
}

void Crypto_Symmetric_Chacha20_rounds(uint32_t *m)
{
  Crypto_Symmetric_Chacha20_column_round(m);
  Crypto_Symmetric_Chacha20_diagonal_round(m);
  Crypto_Symmetric_Chacha20_column_round(m);
  Crypto_Symmetric_Chacha20_diagonal_round(m);
  Crypto_Symmetric_Chacha20_column_round(m);
  Crypto_Symmetric_Chacha20_diagonal_round(m);
  Crypto_Symmetric_Chacha20_column_round(m);
  Crypto_Symmetric_Chacha20_diagonal_round(m);
  Crypto_Symmetric_Chacha20_column_round(m);
  Crypto_Symmetric_Chacha20_diagonal_round(m);
  Crypto_Symmetric_Chacha20_column_round(m);
  Crypto_Symmetric_Chacha20_diagonal_round(m);
  Crypto_Symmetric_Chacha20_column_round(m);
  Crypto_Symmetric_Chacha20_diagonal_round(m);
  Crypto_Symmetric_Chacha20_column_round(m);
  Crypto_Symmetric_Chacha20_diagonal_round(m);
  Crypto_Symmetric_Chacha20_column_round(m);
  Crypto_Symmetric_Chacha20_diagonal_round(m);
  Crypto_Symmetric_Chacha20_column_round(m);
  Crypto_Symmetric_Chacha20_diagonal_round(m);
  return;
}

void Crypto_Symmetric_Chacha20_fill(uint32_t *m, uint32_t i, uint32_t len, uint8_t *src)
{
  if (len != (uint32_t )0)
  {
    uint32_t _0_43 = Buffer_Utils_uint32_of_bytes(src + (uint32_t )0);
    m[i] = _0_43;
    uint32_t len0 = len - (uint32_t )1;
    Crypto_Symmetric_Chacha20_fill(m, i + (uint32_t )1, len0, src + (uint32_t )4);
    return;
  }
  else
    return;
}

void
Crypto_Symmetric_Chacha20_chacha20_init(
  uint32_t *m,
  uint8_t *key,
  uint8_t *iv,
  uint32_t counter
)
{
  m[(uint32_t )0] = (uint32_t )0x61707865;
  m[(uint32_t )1] = (uint32_t )0x3320646e;
  m[(uint32_t )2] = (uint32_t )0x79622d32;
  m[(uint32_t )3] = (uint32_t )0x6b206574;
  Crypto_Symmetric_Chacha20_fill(m, (uint32_t )4, (uint32_t )8, key);
  m[(uint32_t )12] = counter;
  Crypto_Symmetric_Chacha20_fill(m, (uint32_t )13, (uint32_t )3, iv);
  return;
}

void Crypto_Symmetric_Chacha20_add(uint32_t *m, uint32_t *m0, uint32_t i)
{
  uint32_t _0_45 = m[i];
  uint32_t _0_44 = m0[i];
  uint32_t _0_46 = _0_45 + _0_44;
  m[i] = _0_46;
}

void Crypto_Symmetric_Chacha20_sum_matrixes(uint32_t *m, uint32_t *m0)
{
  Crypto_Symmetric_Chacha20_add(m, m0, (uint32_t )0);
  Crypto_Symmetric_Chacha20_add(m, m0, (uint32_t )1);
  Crypto_Symmetric_Chacha20_add(m, m0, (uint32_t )2);
  Crypto_Symmetric_Chacha20_add(m, m0, (uint32_t )3);
  Crypto_Symmetric_Chacha20_add(m, m0, (uint32_t )4);
  Crypto_Symmetric_Chacha20_add(m, m0, (uint32_t )5);
  Crypto_Symmetric_Chacha20_add(m, m0, (uint32_t )6);
  Crypto_Symmetric_Chacha20_add(m, m0, (uint32_t )7);
  Crypto_Symmetric_Chacha20_add(m, m0, (uint32_t )8);
  Crypto_Symmetric_Chacha20_add(m, m0, (uint32_t )9);
  Crypto_Symmetric_Chacha20_add(m, m0, (uint32_t )10);
  Crypto_Symmetric_Chacha20_add(m, m0, (uint32_t )11);
  Crypto_Symmetric_Chacha20_add(m, m0, (uint32_t )12);
  Crypto_Symmetric_Chacha20_add(m, m0, (uint32_t )13);
  Crypto_Symmetric_Chacha20_add(m, m0, (uint32_t )14);
  Crypto_Symmetric_Chacha20_add(m, m0, (uint32_t )15);
  return;
}

void Crypto_Symmetric_Chacha20_chacha20_update(uint8_t *output, uint32_t *state, uint32_t len)
{
  uint32_t *m = state + (uint32_t )0;
  uint32_t *m0 = state + (uint32_t )16;
  memcpy(m0, m, (uint32_t )16 * sizeof m[0]);
  Crypto_Symmetric_Chacha20_rounds(m);
  Crypto_Symmetric_Chacha20_sum_matrixes(m, m0);
  Buffer_Utils_bytes_of_uint32s(output, m, len);
  return;
}

void
Crypto_Symmetric_Chacha20_chacha20(
  uint8_t *output,
  uint8_t *key,
  uint8_t *n,
  uint32_t counter,
  uint32_t len
)
{
  uint32_t state[32] = { 0 };
  uint32_t *m = state + (uint32_t )0;
  Crypto_Symmetric_Chacha20_chacha20_init(m, key, n, counter);
  Crypto_Symmetric_Chacha20_chacha20_update(output, state, len);
}

void
Crypto_Symmetric_Chacha20_prf(uint8_t *x0, uint8_t *x1, uint8_t *x2, uint32_t x3, uint32_t x4)
{
  Crypto_Symmetric_Chacha20_chacha20(x0, x1, x2, x3, x4);
  return;
}

void
Crypto_Symmetric_Chacha20_counter_mode(
  uint8_t *key,
  uint8_t *iv,
  uint32_t counter,
  uint32_t len,
  uint8_t *plaintext,
  uint8_t *ciphertext
)
{
  if (len == (uint32_t )0)
    return;
  else if (len < (uint32_t )64)
  {
    uint8_t *cipher = ciphertext + (uint32_t )0;
    uint8_t *plain = plaintext + (uint32_t )0;
    Crypto_Symmetric_Chacha20_prf(cipher, key, iv, counter, len);
    Buffer_Utils_xor_bytes_inplace(cipher, plain, len);
    return;
  }
  else
  {
    uint8_t *cipher = ciphertext + (uint32_t )0;
    uint8_t *plain = plaintext + (uint32_t )0;
    Crypto_Symmetric_Chacha20_prf(cipher, key, iv, counter, (uint32_t )64);
    Buffer_Utils_xor_bytes_inplace(cipher, plain, (uint32_t )64);
    uint32_t len0 = len - (uint32_t )64;
    uint8_t *ciphertext0 = ciphertext + (uint32_t )64;
    uint8_t *plaintext0 = plaintext + (uint32_t )64;
    Crypto_Symmetric_Chacha20_counter_mode(key,
      iv,
      counter + (uint32_t )1,
      len0,
      plaintext0,
      ciphertext0);
    return;
  }
}

