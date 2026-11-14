module

public import Silmaril.X86.Sep.Xmm.Defs
public import Silmaril.Proofs.X86.Sep.Xmm.Algebra
public import Silmaril.Proofs.X86.Sep.Xmm.Lift
public import Silmaril.Proofs.X86.Sep.Xmm.Moves
/-!
# Separation logic with XMM registers: what is proved

All statements are PROVED with the standard axioms (proofs in
`Silmaril/Proofs/Machine/X86/Sep/Xmm/{Algebra,Lift,Moves}.lean`, names in
`Silmaril.X86.Sep.Xmm`).

**Algebra.** `PMap` (partial maps): `union_assoc`, `union_comm`, `disjoint_union_left/right`,
`le_union_left/right`, `reval_union`, `reval_of_le`, `reval_single`, …; `frag_union`,
`frag_disjoint`, `frag_le`, `frag_reval`, `frag_empty`: `Sep.Frag`'s operations are `PMap`'s.
`XFrag`: the same componentwise. `xsep` is associative and commutative with unit `xemp`
(`xsep_assoc`, `xsep_comm`, `xemp_sep`, `xsep_emp`, registered as `Std.Associative`,
`Std.Commutative`, `Std.LawfulIdentity`), `xsep_mono`, `xsexists_sep`, `xspure_sep_apply`,
`xsep_le`, `xsep_reval`.

**Lifting.** `lift_sep : lift (P ∗ Q) = lift P ∗ₓ lift Q`, `lift_emp`, `lift_spure`,
`lift_sexists`, `lift_mono`.

**Safety and triples.** `xsafeN_post`, `xsafeN_mono`, `xsafeN_le`, `xsafeN_of_post`,
`xsafeN_of_step`, `xsafeN_of_run`, `xsafeN_of_reaches`; `XSTriple.zero`, `mono`, `le`,
`frame`, `conseq`, `xsexists_pre`.

**The bridge from `Open9`.** For every XMM machine `M` with `[ExtendsOpen9X M]`:
`run_of_open9X`, `reaches_of_open9X`, `xsafeN_of_safeN` (the XMM file is unchanged), and
* `xstriple_of_striple : STriple Open9.isa n P Q → XSTriple M n (lift P) (lift Q)`;
* `xstriple_of_triple : Sep.Triple P Q → XSTriple M n (lift P) (lift Q)`.
So every `Open`/`Open9` triple is usable on the XMM machines with no re-proof. For a total
`FnContract` on `Open9.isa` (no separation-logic spec): `xsafeN_of_total`,
`reaches_of_total` (the XMM file is unchanged).

**Move triples on `Sse9.isa`** (`Moves.lean`). `XSTriple.of_step_local` (a triple from one
local step) and the generic rule `xstriple_xwrite` (an SSE form at `pc` that advances RIP and
writes one XMM register, with read-only integer resources `G` and XMM resources `X`; the code
bytes are decoded by `Sse9.decodeL`). Instances, each for every index `n`:
* `xstriple_pxor_self`, `xstriple_xorps_self`: `xmmAny d` to `xmm d ↦ 0`;
* `xstriple_load_reg k` (`movups`/`movaps`/`movdqu`/`movdqa xmm, xmm`): `xmm s ↦ w ∗ₓ xmmAny d`
  to `xmm s ↦ w ∗ₓ xmm d ↦ w`;
* `xstriple_movqLoad_reg` (`movq xmm, xmm`): the low quadword, upper quadword zeroed;
* `xstriple_movToX_reg sz` (`movd`/`movq xmm, r32/r64`): `r ↦ a` to `xmm d ↦ zext(a)`;
* `xstriple_load_mem k` for unaligned `k` (`movups`/`movdqu xmm, [base + disp]`): sixteen
  readable bytes at `base + disp` to `xmm d ↦ ofNat (leValue bs)`.
`xmmPt_le` reads an XMM atom off the machine; `xholds_lift_xmmPt` (non-vacuity helper).

**Instances.** `instExtendsOpen9XSse9 : ExtendsOpen9X Sse9.isa`.

Not here: the **store** forms (`movups`/`movdqu [m], xmm`, `movq [m], xmm`: they change
memory, and need a `writeBytes` frame rule for `bytesPt`), `movFromX` (`movq r64, xmm`), the
aligned memory forms and `punpckl*`, an
`ExtendsOpen9X` instance for `SseF.step u` (`SseF.FState` is a different state type with its
own `SseF.ExtendsOpen9X`; a bridge needs a state-generic `XSafeN`), the `SepAlg` instance for
`XFrag` (CP-10a, after K3).
-/
