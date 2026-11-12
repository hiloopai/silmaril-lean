module

public import Silmaril.X86.Str9L.Checks
public import Silmaril.X86.Features.Ext.Avx.Vectors
public import Silmaril.X86.Features.Vectors.Round
public meta import Silmaril.X86.Str9L.Checks
public meta import Silmaril.X86.Features.Ext.Avx.Vectors
public meta import Silmaril.X86.Features.Vectors.Round

/-! The `avx` lane's native vectors (`Features.Avx.Vectors`, 3,627 vectors from
`scripts/x86-features/gen_avx_vectors.py`) and the `roundss`/`roundsd` vectors
(`Features.Vectors.Round`, 7,168 from `scripts/x86-features/gen_vectors.py`), each run through
one `Str9L.step Checks.host lanes` (`Str9L.Checks`). The VEX forms `Str9V` decodes are run by
`Str9V`, the others by the `avx` lane; `roundss`/`roundsd` by `floatExt`. -/

namespace Silmaril.X86.Str9L.Vectors

open Silmaril.X86.Features (hexFields)
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v0).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v1).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v2).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v3).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v4).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v5).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v6).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v7).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v8).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v9).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v10).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v11).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v12).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v13).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v14).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v15).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v16).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v17).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v18).all Checks.checkAvxLine

#guard (hexFields Silmaril.X86.Features.Vectors.Round.vectors).all Checks.checkRoundLine

end Silmaril.X86.Str9L.Vectors
