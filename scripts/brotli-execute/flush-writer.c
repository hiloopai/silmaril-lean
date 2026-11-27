/* Encode two chunks with a real Brotli meta-block boundary between them. */
#include <brotli/encode.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char** argv) {
  uint8_t input[8192], output[16384];
  if (argc != 3) return 2;
  const size_t split = (size_t)strtoul(argv[1], NULL, 10);
  const uint32_t quality = (uint32_t)strtoul(argv[2], NULL, 10);
  const size_t size = fread(input, 1, sizeof(input), stdin);
  if (!feof(stdin) || ferror(stdin) || split == 0 || split >= size) return 2;
  BrotliEncoderState* encoder = BrotliEncoderCreateInstance(NULL, NULL, NULL);
  if (!encoder) return 1;
  const uint8_t* in = input;
  uint8_t* out = output;
  size_t first = split, second = size - split, remaining = sizeof(output);
  int status = 1;
  if (!BrotliEncoderSetParameter(encoder, BROTLI_PARAM_QUALITY, quality) ||
      !BrotliEncoderSetParameter(encoder, BROTLI_PARAM_LGWIN, 18)) goto done;
  if (!BrotliEncoderCompressStream(encoder, BROTLI_OPERATION_FLUSH,
                                   &first, &in, &remaining, &out, NULL) ||
      first != 0 || BrotliEncoderHasMoreOutput(encoder)) goto done;
  if (!BrotliEncoderCompressStream(encoder, BROTLI_OPERATION_FINISH,
                                   &second, &in, &remaining, &out, NULL) ||
      second != 0 || !BrotliEncoderIsFinished(encoder)) goto done;
  const size_t count = (size_t)(out - output);
  if (fwrite(output, 1, count, stdout) == count) status = 0;
done:
  BrotliEncoderDestroyInstance(encoder);
  return status;
}
