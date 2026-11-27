/* Differential driver for the pinned libbrotli common code. */
#include <stdint.h>
#include <stdio.h>

#include "c/common/dictionary.h"
#include "c/common/transform.h"

static void write_affix(const uint8_t* affix) {
  fwrite(affix + 1, 1, affix[0], stdout);
  putchar(0);
}

static int rfc_operation(int native) {
  if (native == BROTLI_TRANSFORM_IDENTITY) return 0;
  if (native == BROTLI_TRANSFORM_UPPERCASE_FIRST) return 1;
  if (native == BROTLI_TRANSFORM_UPPERCASE_ALL) return 2;
  if (native <= BROTLI_TRANSFORM_OMIT_LAST_9) return 11 + native;
  if (native >= BROTLI_TRANSFORM_OMIT_FIRST_1 &&
      native <= BROTLI_TRANSFORM_OMIT_FIRST_9) {
    return 2 + native - BROTLI_TRANSFORM_OMIT_FIRST_1 + 1;
  }
  return -1;
}

static int write_word(const BrotliTransforms* table, const uint8_t* word,
                      int length) {
  /* The native uppercase helper may touch scratch beyond the logical end. */
  for (uint32_t ordinal = 0; ordinal < table->num_transforms; ++ordinal) {
    uint8_t result[40] = {0};
    int size = BrotliTransformDictionaryWord(result, word, length, table, ordinal);
    if (size < 0 || size > 37) return 0;
    putchar(size);
    fwrite(result, 1, size, stdout);
  }
  return !ferror(stdout);
}

int main(int argc, char** argv) {
  if (argc != 2) return 1;
  const BrotliTransforms* table = BrotliGetTransforms();
  const BrotliDictionary* dictionary = BrotliGetDictionary();
  if (table->num_transforms != 121) return 1;
  for (uint32_t ordinal = 0; ordinal < table->num_transforms; ++ordinal) {
    int operation = rfc_operation(BROTLI_TRANSFORM_TYPE(table, ordinal));
    if (operation < 0) return 1;
    write_affix(BROTLI_TRANSFORM_PREFIX(table, ordinal));
    putchar(operation);
    write_affix(BROTLI_TRANSFORM_SUFFIX(table, ordinal));
  }
  for (int length = 4; length <= 24; ++length) {
    size_t count = (size_t)1 << dictionary->size_bits_by_length[length];
    for (size_t index = 0; index < count; ++index) {
      size_t start = dictionary->offsets_by_length[length] + index * length;
      if (!write_word(table, dictionary->data + start, length)) return 1;
    }
  }
  FILE* edges = fopen(argv[1], "rb");
  if (!edges) return 1;
  int length;
  while ((length = fgetc(edges)) != EOF) {
    /* Pad test inputs so every native omit pointer stays in the object. */
    uint8_t word[32] = {0};
    if (length < 4 || length > 24 || fread(word, 1, length, edges) != (size_t)length ||
        !write_word(table, word, length)) {
      fclose(edges);
      return 1;
    }
  }
  int failed = ferror(edges);
  fclose(edges);
  return failed || fflush(stdout) != 0 || ferror(stdout);
}
