/* zconf-hosted.h: zlib 1.3.1's zconf.h configuration of a hosted build, resolved for
   Silmaril.Data.Layout.Header.read (which reads no #if expressions).

   The values are those zconf.h (SHA-256 f5134250a67d57459234b63858f0d9d3ef8dcc48e9e1028d3f4fdcf6eae677ae,
   from https://github.com/madler/zlib/releases/download/v1.3.1/zlib-1.3.1.tar.gz, SHA-256
   9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23) gives without Z_SOLO,
   on x86_64 Linux with an STDC compiler, a 32-bit unsigned int (UINT_MAX = 0xffffffff), and
   without _WIN64, NO_SIZE_T, SMALL_MEDIUM, __MACTYPES__, HAVE_UNISTD_H, _LARGEFILE64_SOURCE or
   ZLIB_DLL. Each line names the zconf.h line it resolves. `size_t` is the reader's built-in
   name (zconf.h:254 includes <stddef.h>, which the reader does not read). The clang route
   reads zconf.h itself (examples/headers/clang/zlib-hosted.json); the two routes are compared
   in Silmaril.Data.Layout.Header.Import.Thms.

   zlib's licence is in the excerpt zlib.h next to this file. */
#ifndef ZCONF_H
#define ZCONF_H
#define ZEXTERN extern                  /* zconf.h:379 */
#define ZEXPORT                         /* zconf.h:382 */
#define ZEXPORTVA                       /* zconf.h:385 */
#define FAR                             /* zconf.h:389 */
typedef size_t z_size_t;                /* zconf.h:255 (STDC, not NO_SIZE_T) */
typedef unsigned char  Byte;            /* zconf.h:393 */
typedef unsigned int   uInt;            /* zconf.h:395 */
typedef unsigned long  uLong;           /* zconf.h:396 */
typedef Byte  FAR Bytef;                /* zconf.h:402 */
typedef char  FAR charf;                /* zconf.h:404 */
typedef int   FAR intf;                 /* zconf.h:405 */
typedef uInt  FAR uIntf;                /* zconf.h:406 */
typedef uLong FAR uLongf;               /* zconf.h:407 */
typedef void const *voidpc;             /* zconf.h:410 (STDC) */
typedef void FAR   *voidpf;             /* zconf.h:411 (STDC) */
typedef void       *voidp;              /* zconf.h:412 (STDC) */
#define Z_U4 unsigned                   /* zconf.h:422 (UINT_MAX == 0xffffffffUL) */
typedef Z_U4 z_crc_t;                   /* zconf.h:431 */
#define z_off_t long                    /* zconf.h:513 */
#endif
