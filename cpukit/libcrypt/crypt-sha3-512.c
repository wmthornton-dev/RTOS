/*-
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Copyright (c) 2025 RTEMS (http://www.rtems.org/)
 * Developed (d) 2025 Wayne Michael Thornton (WMT) for RTEMS Project as
 * An Open Source Contribution.
 * 
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

/*
 * SHA-3 (Keccak) password hashing for RTEMS libcrypt
 * Format: $SHA3$512$[rounds=R$][salt]$[hash]
 */

/* Based on:
 * SHA3-512-based crypt implementation. Released into the Public Domain by
 * Keccak team: Guido Bartoni, Joan Daemeo, Michaël Peeters, Giles Van Assche.
 * Their reference code and specifications are released into the Public Domain
 * and widely used as the basis for open-source SHA-3 implementations. 
 */

#include <string.h>
#include <stdint.h>
#include <stdio.h>
#include <crypt.h>
#include <stdbool.h>
#include <stdlib.h>

#define SHA3_512_RATE 72
#define SHA3_512_DIGEST_SIZE 64
#define SALT_LEN_MAX 16
#define ROUNDS_DEFAULT 5000
#define ROUNDS_MIN 1000
#define ROUNDS_MAX 999999999

static const char sha3_512_salt_prefix[] = "$SHA3$512$";
static const char sha3_512_rounds_prefix[] = "rounds=";

/* --- Begin Keccak-f[1600] implementation --- */
#define ROL64(a, o) (((a) << (o)) | ((a) >> (64 - (o))))
static const uint64_t keccakf_rndc[24] = {
    0x0000000000000001ULL,0x0000000000008082ULL,0x800000000000808aULL,
    0x8000000080008000ULL,0x000000000000808bULL,0x0000000080000001ULL,
    0x8000000080008081ULL,0x8000000000008009ULL,0x000000000000008aULL,
    0x0000000000000088ULL,0x0000000080008009ULL,0x000000008000000aULL,
    0x000000008000808bULL,0x800000000000008bULL,0x8000000000008089ULL,
    0x8000000000008003ULL,0x8000000000008002ULL,0x8000000000000080ULL,
    0x000000000000800aULL,0x800000008000000aULL,0x8000000080008081ULL,
    0x8000000000008080ULL,0x0000000080000001ULL,0x8000000080008008ULL
};
static const int keccakf_rotc[24] = {
    1,3,6,10,15,21,28,36,45,55,2,14,27,41,56,8,25,43,62,18,39,61,20,44
};
static const int keccakf_piln[24] = {
    10,7,11,17,18,3,5,16,8,21,24,4,15,23,19,13,12,2,20,14,22,9,6,1
};
static void keccak_f1600(uint64_t st[25]) {
    int i, j, r;
    uint64_t t, bc[5];
    for (r = 0; r < 24; r++) {
        for (i = 0; i < 5; i++)
            bc[i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20];
        for (i = 0; i < 5; i++) {
            t = bc[(i + 4) % 5] ^ ROL64(bc[(i + 1) % 5], 1);
            for (j = 0; j < 25; j += 5)
                st[j + i] ^= t;
        }
        t = st[1];
        for (i = 0; i < 24; i++) {
            j = keccakf_piln[i];
            bc[0] = st[j];
            st[j] = ROL64(t, keccakf_rotc[i]);
            t = bc[0];
        }
        for (j = 0; j < 5; j++)
            bc[j] = st[j * 5];
        for (i = 0; i < 5; i++) {
            for (j = 0; j < 5; j++)
                st[j * 5 + i] ^= (~st[((j + 1) % 5) * 5 + i]) & st[((j + 2) % 5) * 5 + i];
        }
        st[0] ^= keccakf_rndc[r];
    }
}

void sha3_init(sha3_ctx_t *ctx) {
    memset(ctx->state, 0, sizeof(ctx->state));
    ctx->rate = SHA3_512_RATE;
    ctx->capacity = 1600 - 2 * (SHA3_512_RATE * 8);
    ctx->pos = 0;
}

void sha3_update(sha3_ctx_t *ctx, const void *data, size_t len) {
    const uint8_t *d = (const uint8_t *)data;
    while (len--) {
        ((uint8_t *)ctx->state)[ctx->pos++] ^= *d++;
        if (ctx->pos >= ctx->rate) {
            keccak_f1600(ctx->state);
            ctx->pos = 0;
        }
    }
}

void sha3_final(sha3_ctx_t *ctx, uint8_t *out, size_t outlen) {
    ((uint8_t *)ctx->state)[ctx->pos] ^= 0x06;
    ((uint8_t *)ctx->state)[ctx->rate - 1] ^= 0x80;
    keccak_f1600(ctx->state);
    memcpy(out, ctx->state, outlen);
}

/* Use global _crypt_b64_from_24bit from crypt.h */

char *crypt_sha3_512_r(const char *key, const char *salt, struct crypt_data *data) {
    unsigned long srounds = ROUNDS_DEFAULT;
    int n;
    uint8_t digest[SHA3_512_DIGEST_SIZE];
    sha3_ctx_t ctx;
    size_t salt_len, key_len, cnt, rounds;
    char *cp, *endp;
    const char *num;
    bool rounds_custom = false;
    char *buffer = data->buffer;
    int buflen = (int)sizeof(data->buffer);

    rounds = ROUNDS_DEFAULT;
    rounds_custom = false;

    if (strncmp(sha3_512_salt_prefix, salt, sizeof(sha3_512_salt_prefix) - 1) == 0)
        salt += sizeof(sha3_512_salt_prefix) - 1;

    if (strncmp(salt, sha3_512_rounds_prefix, sizeof(sha3_512_rounds_prefix) - 1) == 0) {
        num = salt + sizeof(sha3_512_rounds_prefix) - 1;
        srounds = strtoul(num, &endp, 10);
        if (*endp == '$') {
            salt = endp + 1;
            rounds = srounds < ROUNDS_MIN ? ROUNDS_MIN : (srounds > ROUNDS_MAX ? ROUNDS_MAX : srounds);
            rounds_custom = true;
        }
    }

    salt_len = strcspn(salt, "$\n");
    if (salt_len > SALT_LEN_MAX) salt_len = SALT_LEN_MAX;
    key_len = strlen(key);

    sha3_init(&ctx);
    sha3_update(&ctx, key, key_len);
    sha3_update(&ctx, salt, salt_len);

    // Burn CPU cycles
    for (cnt = 0; cnt < rounds; ++cnt) {
        sha3_update(&ctx, key, key_len);
        sha3_update(&ctx, salt, salt_len);
        keccak_f1600(ctx.state);
    }
    sha3_final(&ctx, digest, sizeof(digest));

    cp = buffer;
    buflen = sizeof(data->buffer);
    cp = stpncpy(buffer, sha3_512_salt_prefix, buflen);
    buflen -= sizeof(sha3_512_salt_prefix) - 1;
    if (rounds_custom) {
        n = snprintf(cp, buflen, "%s%zu$", sha3_512_rounds_prefix, rounds);
        cp += n;
        buflen -= n;
    }
    cp = stpncpy(cp, salt, buflen < salt_len ? buflen : salt_len);
    buflen -= salt_len;
    if (buflen > 0) {
        *cp++ = '$';
        --buflen;
    }
    // Output base64
    int i = 0;
    while (i + 3 <= SHA3_512_DIGEST_SIZE && buflen > 0) {
        _crypt_b64_from_24bit(digest[i+2], digest[i+1], digest[i], 4, &buflen, &cp);
        i += 3;
    }
    if (i < SHA3_512_DIGEST_SIZE && buflen > 0) {
        _crypt_b64_from_24bit(0, digest[SHA3_512_DIGEST_SIZE-1], digest[SHA3_512_DIGEST_SIZE-2], 3, &buflen, &cp);
    }
    if (buflen <= 0) {
        buffer = NULL;
    } else {
        *cp = '\0';
    }
    return buffer;
}

struct crypt_format crypt_sha3_512_format =
    CRYPT_FORMAT_INITIALIZER(crypt_sha3_512_r, "$SHA3$512$");
