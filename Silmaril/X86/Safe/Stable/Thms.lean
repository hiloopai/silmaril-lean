module

public import Silmaril.X86.Safe.Stable.Defs
public import Silmaril.X86.BlockCert.Defs
public import Silmaril.Proofs.X86.Safe.Stable
public import Silmaril.Proofs.X86.Safe.Stable.RightRot
public import Silmaril.Proofs.X86.Safe.Stable.NonVacuity

/-!
# Stable triples: theorems (header)

PROVED (standard axioms only; proofs in `Silmaril.Proofs.X86.Safe.Stable`, names in
`Silmaril.X86.Safe`), for every step function `step`:

* Entry from runs: `TripleS.of_local` (a run that leaves every location outside the
  precondition's fragment unchanged **at every state** is a stable triple);
  `stable_of_le`, `stable_of_unchanged`, `Unchanged.refl`.
* Bridges: `TripleS.toTriple : TripleS Open.step P Q → Sep.Triple P Q`, `TripleS.reaches`,
  `STripleS.toSTriple : STripleS step n P Q → STriple step n P Q`, `safeN_of_safeNS`,
  `TripleS.toSTripleS` (a stable total triple gives the stable step-indexed triple at every
  index), `safeNS_of_run`.
* Structural rules: `TripleS.frame`, `TripleS.conseq` (with `pre`, `post`), `TripleS.seq`,
  `TripleS.refl`, `TripleS.sexists`, `TripleS.spure`.
* Machines: `TripleS.of_refines` (along `Refines step step'`, e.g. `Open.step → Open9.step`),
  `run_isSome_of_le`.

Non-vacuity (`Silmaril.X86.Safe.RightRot`, proofs in
`Silmaril.Proofs.X86.Safe.Stable.RightRot` and `…/Stable/RightRotRun`):

* `RightRot.rightRot_tripleS e ret sp bp vdi vsi … : TripleS Open.step (RightRot.pre …)
  (RightRot.post …)`: the `clang -O0` leaf `right_rot` (15 instructions) as a stable triple,
  the frame surviving all fifteen intermediate states. The precondition owns `rbp`, which
  the function overwrites in the middle of the run.
* `Silmaril.Proofs.X86.SafeStable.NonVacuity.rightRot_concrete`: a concrete
  state (one RWX region, the code at `0x400000`, `rsp = 0x7008`, `rbx = 7`) satisfies
  `RightRot.pre ∗ (regPt .rbx 7 ∗ strue)` as a whole state; `rightRot_tripleS` then gives a
  run returning to `0x401000` with `rbx = 7` read back at every intermediate state.

Frozen (`Task.certStable`, not proved): block-certificate functions give stable triples.
-/

@[expose] public section

namespace Silmaril.X86.Safe

open Silmaril.X86 (MState)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (Le reval)
open Silmaril.X86.BlockCert (FunCert Blk runL)

/-- **Frozen: the round-4 certificate route yields stable contracts.** A function certificate
(`BlockCert.FunCert`) whose exit condition is the local reading of `P`/`Q` (unchanged outside
the precondition's fragment, `Q` on the re-valued fragment), whose annotations keep every
location outside that fragment, and each of whose blocks keeps it along every prefix of its
listing, gives a stable triple on the open machine. The per-prefix hypothesis says that each
block is certified against a footprint; `FunCert.total`
(`BlockCert/Thms.lean`) is the non-stable analogue. -/
def Task.certStable : Prop :=
  ∀ (F : FunCert) (entry : Blk) (P Q : SProp), entry ∈ F.blocks → F.checked = true →
    F.VC (fun m0 t => ∀ h₁, P h₁ → Le h₁ (toFrag m0) →
      Unchanged h₁ m0 t ∧ Q (reval h₁ (toFrag t))) →
    (∀ m h₁, P h₁ → Le h₁ (toFrag m) →
      Silmaril.X86.Ext.Loaded m.memory F.base F.code ∧
        m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧ F.ann entry.off m m) →
    (∀ b ∈ F.blocks, ∀ m0 m h₁, F.ann b.off m0 m → P h₁ → Le h₁ (toFrag m0) →
      Unchanged h₁ m0 m) →
    (∀ b ∈ F.blocks, ∀ m0 m h₁, F.ann b.off m0 m → P h₁ → Le h₁ (toFrag m0) →
      ∀ k m', runL (b.instrs.take k) m = some m' → Unchanged h₁ m0 m') →
    TripleS Silmaril.X86.Open.step P Q

end Silmaril.X86.Safe
