module

public import Silmaril.Machine.X86.RelIsa.Safe.Defs
public import Silmaril.Proofs.Machine.X86.RelIsa.Safe

/-!
# Demonic step-indexed safety and triples: what is proved (header)

PROVED (standard axioms; proofs in
`Silmaril/Proofs/Machine/X86/RelIsa/Safe.lean`, names in `Silmaril.Machine.X86.RelIsa`):

* `SafeNR`: `safeNR_zero`, `safeNR_succ`, `safeNR_mono`, `safeNR_le`, `safeNR_post`,
  `safeNR_bind`, `safeNR_of_must` (a `Must` run is safe at every index), and
  **`SafeNR.of_le`**: safety on `A` transfers to every `C` with `Le C A`, from a live state,
  with no progress hypothesis.
* The deterministic case: `ofFun_step_ok`, `ofFun_step_stop`, `progress_ofFun`,
  **`safeNR_ofFun`** (`SafeNR (ofFun step) Q n m ↔ Safe.SafeN step Q n m`), `safeNR_ofIsa`,
  `ofIsa_eq_ofFun`, `ofIsa_open`, `ofIsa_open9`, and `safeN_of_safeNR`: from
  `Le (ofFun step) A`, `SafeNR A` gives back `SafeN step`.
* Loosening: `safeNR_loosen_of_ofIsa`, `safeNR_loosen_of_safeN` (`SafeN I.step` is
  `SafeNR (loosen I ⊤)`), and the mutation witness `not_safeNR_loosen_of_stuck` (where `I` is
  stuck and `Q` fails, `SafeNR (loosen I P) Q 1` is false: the loosening may stop).
* `STripleR`: `zero`, `mono`, `le`, `frame`, `conseq`, `of_le`, `of_tripleR`,
  `of_striple_loosen` (`Safe.STriple I.step` is `STripleR (loosen I ⊤)`), `sexists_pre`,
  `spure_pre`.
* `TripleR`: `frame`, `conseq`, `seq`, `of_le`, `of_triple_ext` (for every `I` with
  `[Safe.ExtendsOpen I.step]`), **`TripleR.of_triple`** (`Sep.Triple P Q` is
  `TripleR (loosen Open.isa ⊤) P Q`, via `must_loosen_of_reaches`), `of_triple9`.

Here `⊤` is written `fun _ => True`. Not here: the K5 bridge `safeNR_iff_safeR` (dropped by
). `SafeNR` and `Must` hold vacuously at a state with no outcome at all; `ofFun`
and `loosen` always have one.
-/
