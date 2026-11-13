/* Parallel hashing: N workers each hash their own buffer with
 * zlib's crc32_z (rung 03, -DZ_SOLO), the main thread joins them and hashes the results.
 * The CIR model is Silmaril.X86.Concurrency.Cir.ParHash.par.
 * Not ingested by tools/litmus-x86 (not in
 * ../index.txt); `run.sh` compiles it natively and prints the values for the small instance
 * ParHash.tiny (buffers {7} and {9}). */
#include <pthread.h>
#include <stdio.h>
#include "zlib.h"

#define N 2

struct job {
  int k;
  const unsigned char *buf;
  z_size_t len;
};

static unsigned char buf0[1] = {7};
static unsigned char buf1[1] = {9};
static struct job jobs[N] = {{0, buf0, 1}, {1, buf1, 1}};
static unsigned long res[N]; /* z_crc_t is unsigned long under Z_SOLO: 8 bytes */
static unsigned long out;

static void *worker(void *p) {
  struct job *j = p;
  res[j->k] = crc32_z(0, j->buf, j->len); /* the one local(B) block of thread k + 1 */
  return 0;
}

int main(void) {
  pthread_t t[N];
  for (int k = 0; k < N; k++) pthread_create(&t[k], 0, worker, &jobs[k]);
  for (int k = 0; k < N; k++) pthread_join(t[k], 0);
  out = crc32_z(0, (const unsigned char *)res, sizeof res); /* the combine block */
  for (int k = 0; k < N; k++) printf("res[%d] = %lu\n", k, res[k]);
  printf("out = %lu\n", out);
  return 0;
}
