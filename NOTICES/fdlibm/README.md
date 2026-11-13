# fdlibm-derived code

`pow` in `tools/ccomp/runtime/libc.c` (the C library of programs compiled by `ccomp`) is adapted
from `src/e_pow.c` of [OpenLibm](https://github.com/JuliaMath/openlibm/blob/master/src/e_pow.c),
which is Sun's fdlibm `e_pow.c` (version `1.5 04/04/22 SMI`). The adaptation is described in a
comment next to it (the runtime's binary64 union instead of word-access headers, two shortcuts
replaced by the general path). The OpenLibm revision it was taken from is not recorded in the
source. `Silmaril/Raw/Compiler/C/Sem/runtime/libc.ail`, Cerberus's elaboration of `libc.c`,
contains the same function as typed Ail.

[e_pow.c-NOTICE](e_pow.c-NOTICE) is the copyright and permission notice of the original, as
`libc.c` preserves it: copyright (C) 2004 Sun Microsystems, Inc.; permission to use, copy,
modify and distribute is freely granted, provided that the notice is preserved.
