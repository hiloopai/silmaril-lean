#include <cstdint>
#include <iostream>
#include <iterator>
#include <string>

#define ZSTD_STATIC_LINKING_ONLY
#include "zstd.h"
extern "C" size_t ZSTD_noCompressLiterals(void*, size_t, const void*, size_t);
extern "C" size_t ZSTD_compressRleLiteralsBlock(void*, size_t, const void*, size_t);

int main(int argc, char** argv) {
  if (argc < 2 || argc > 3) return 2;
  const std::string mode(argv[1]);
  const std::string input((std::istreambuf_iterator<char>(std::cin)),
                          std::istreambuf_iterator<char>());
  const size_t capacity = argc == 3 ? std::stoul(argv[2]) : 131072;
  const bool compress = mode == "compress" || mode == "compress-checksum";
  const size_t storage = compress ? ZSTD_compressBound(input.size()) : capacity;
  std::string output(storage == 0 ? 1 : storage, '\0');
  size_t size;
  if (mode == "raw") {
    size = ZSTD_noCompressLiterals(&output[0], output.size(), input.data(), input.size());
  } else if (mode == "rle") {
    if (input.empty()) return 2;
    size = ZSTD_compressRleLiteralsBlock(&output[0], output.size(), input.data(), input.size());
  } else if (mode == "decode") {
    size = ZSTD_decompress(&output[0], capacity, input.data(), input.size());
  } else if (mode == "compress") {
    size = ZSTD_compress(&output[0], output.size(), input.data(), input.size(), 3);
  } else if (mode == "compress-checksum") {
    ZSTD_CCtx* context = ZSTD_createCCtx();
    if (context == nullptr) return 2;
    size = ZSTD_CCtx_setParameter(context, ZSTD_c_checksumFlag, 1);
    if (!ZSTD_isError(size)) {
      size = ZSTD_compress2(context, &output[0], output.size(), input.data(), input.size());
    }
    ZSTD_freeCCtx(context);
  } else if (mode == "frame-info") {
    ZSTD_frameHeader header;
    const size_t status = ZSTD_getFrameHeader(&header, input.data(), input.size());
    if (status != 0 || header.frameType != ZSTD_frame) return 3;
    size = ZSTD_findFrameCompressedSize(input.data(), input.size());
    if (ZSTD_isError(size)) return 3;
    std::cout << size << ' ' << header.headerSize << ' ' << header.windowSize << ' '
              << header.frameContentSize << ' ' << header.dictID << ' ' << header.checksumFlag;
    return std::cout ? 0 : 1;
  } else if (mode == "first-block") {
    const size_t at = ZSTD_frameHeaderSize(input.data(), input.size());
    if (ZSTD_isError(at) || at + 3 > input.size()) return 2;
    const auto* bytes = reinterpret_cast<const unsigned char*>(input.data() + at);
    const uint32_t header = bytes[0] + 256u * bytes[1] + 65536u * bytes[2];
    if ((header & 7) != 5 || at + 3 + (header >> 3) != input.size()) return 2;
    std::cout.write(input.data() + at + 3, header >> 3);
    return std::cout ? 0 : 1;
  } else {
    return 2;
  }
  if (ZSTD_isError(size)) return 3;
  std::cout.write(output.data(), size);
  return std::cout ? 0 : 1;
}
