/* Emit two real data blocks separated by caller metadata using libbrotli. */
#include <brotli/encode.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char** argv) {
  uint8_t input[8192], output[16384], metadata[1024];
  if (argc != 3) return 2;
  const size_t split = (size_t)strtoul(argv[1], NULL, 10);
  const size_t metadata_length = (size_t)strtoul(argv[2], NULL, 10);
  const size_t size = fread(input, 1, sizeof(input), stdin);
  if (!feof(stdin) || ferror(stdin) || split == 0 || split >= size ||
      metadata_length > sizeof(metadata)) return 2;
  for (size_t i = 0; i < metadata_length; ++i) metadata[i] = (uint8_t)(i ^ 0xa5);
  BrotliEncoderState* encoder = BrotliEncoderCreateInstance(NULL, NULL, NULL);
  if (!encoder) return 1;
  const uint8_t* first = input;
  const uint8_t* note = metadata;
  const uint8_t* second = input + split;
  uint8_t* out = output;
  size_t first_len = split, note_len = metadata_length, second_len = size - split;
  size_t available = sizeof(output);
  int status = 1;
  if (!BrotliEncoderSetParameter(encoder, BROTLI_PARAM_QUALITY, 9) ||
      !BrotliEncoderSetParameter(encoder, BROTLI_PARAM_LGWIN, 18)) goto done;
  if (!BrotliEncoderCompressStream(encoder, BROTLI_OPERATION_FLUSH, &first_len, &first,
                                   &available, &out, NULL) ||
      first_len != 0 || BrotliEncoderHasMoreOutput(encoder)) goto done;
  if (!BrotliEncoderCompressStream(encoder, BROTLI_OPERATION_EMIT_METADATA, &note_len, &note,
                                   &available, &out, NULL) ||
      note_len != 0 || BrotliEncoderHasMoreOutput(encoder)) goto done;
  if (!BrotliEncoderCompressStream(encoder, BROTLI_OPERATION_FINISH, &second_len, &second,
                                   &available, &out, NULL) ||
      second_len != 0 || !BrotliEncoderIsFinished(encoder)) goto done;
  const size_t count = (size_t)(out - output);
  if (fwrite(output, 1, count, stdout) == count) status = 0;
done:
  BrotliEncoderDestroyInstance(encoder);
  return status;
}
