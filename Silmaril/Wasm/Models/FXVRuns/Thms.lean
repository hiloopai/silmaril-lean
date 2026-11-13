module

public import Silmaril.Proofs.Wasm.Models.FXVRuns.Lower

/-!
# Runs of `StepFX'`: the abortive fragment in full, and the first lowering re-proved

`StepFX'` (`Silmaril.Wasm.Models.FXV`) lets continuation references move as values. Its inversions
split FX code at the first instruction that is neither a Core value nor a continuation
reference (`Silmaril.Proofs.Wasm.Models.FXVRuns.fnvF`). Without host calls:

**Abortive handlers** (`Silmaril.Wasm.Models.FXAbort`, an earlier step proved `src_runs`):

* **`abort_src_step_inv`**: every step of `abortSrc hs W x ks` is a `suspend` with some split
  `W = U ++ vs` of the payload (the captured context is a value prefix `U`);
* **`abort_split_stuck`**: every split with `U ≠ []` is stuck: the branch carries `|vs| + 1`
  values to a label of arity `|W| + 1`;
* **`abort_src_behaviours_eq`**: without FX functions, the source's `StepFX'` behaviours are
  exactly the Core behaviours of the join `W; ks` at the source's store.

**The first lowering** (`Silmaril.Wasm.Models.FXLower`, an earlier step proved `lower_correct` for
`StepFX`):

* **`lower_complete'`**, **`lower_correct'`**: the source `vs; ref.func a; cont.new; resume` has
  under `StepFX'` exactly the Core behaviours of the target `vs; ref.func a; call_ref`;
* **`behavioursFX'_noK`**: on code without continuations and FX instructions, `StepFX'` and
  `StepFX` have the same behaviours (no FX functions).

Not proved: the comparison of the two sides of the abortive lowering at the join. The source
reaches `W; ks` at `s` and the target at `s.addExn ⟨ta, W⟩`; relating these needs a Core
simulation that renames exception addresses above `s.exns.length` (in values, the store and the
code), which is not built.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXVRuns

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAbort Silmaril.Wasm.Models.FXLower
open Silmaril.Proofs.Wasm.Models.FXVRuns (midCode NoKs)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- **Every step of the abortive source is a `suspend`**, with a split of the payload. -/
theorem abort_src_step_inv {fx : H → Option FuncFX} {s : Store H} {K : List (Option ContFX)}
    {f : Frame} {hs : List HClause} {W : List Val} {x : TagIdx} {ks : List Instr} {ta : Nat}
    {ti : TagInst} {l : LabelIdx} (ht : s.tag? f x = some (ta, ti))
    (hcl : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) {y : ConfigFX H}
    (h : StepFX' P noHost fx ⟨s, K, f, abortSrc hs W x ks⟩ y) :
    ∃ (U vs : List FVal) (E : CtxV), liftV W = U ++ vs ∧
      y = ⟨s, K ++ [some ⟨E.plug⟩], f, midCode W ks vs K.length l⟩ :=
  Silmaril.Proofs.Wasm.Models.FXVRuns.src_step_inv ht hcl h

/-- **The other `suspend` splits are stuck.** -/
theorem abort_split_stuck {fx : H → Option FuncFX} {s : Store H} {K : List (Option ContFX)}
    {f : Frame} {W : List Val} {ks : List Instr} {U vs : List FVal} {j : Nat} {l : LabelIdx}
    (hl : l.toNat = 0) (hU : liftV W = U ++ vs) (hne : U ≠ []) (z : ConfigFX H) :
    ¬ StepFX' P noHost fx ⟨s, K, f, midCode W ks vs j l⟩ z :=
  Silmaril.Proofs.Wasm.Models.FXVRuns.split_stuck hl hU hne z

/-- **The abortive source has exactly the join's behaviours** (no host calls, no FX
functions). -/
theorem abort_src_behaviours_eq {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {hs : List HClause} {W : List Val} {x : TagIdx} {ks : List Instr} {ta : Nat} {ti : TagInst}
    {l : LabelIdx} (ht : s.tag? f x = some (ta, ti))
    (hcl : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0) :
    behavioursFX' P noHost noFX ⟨s, K, f, abortSrc hs W x ks⟩ =
      behavioursOf P noHost ⟨s, f, abortJoin W ks⟩ :=
  Silmaril.Proofs.Wasm.Models.FXVRuns.src_behaviours_eq ht hcl hl

/-- **On code without continuations, `StepFX'` and `StepFX` have the same behaviours.** -/
theorem behavioursFX'_noK {host : HostSemantics H} {x : ConfigFX H} (hx : NoKs x.code) :
    behavioursFX' P host noFX x = behavioursFX P host noFX x :=
  Silmaril.Proofs.Wasm.Models.FXVRuns.behavioursFX'_noK hx

/-- **Completeness of the first lowering under `StepFX'`.** -/
theorem lower_complete' {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct : TypeIdx} {hs : List OnClause} {vs : List Val}
    (hf : s.funcs[a]? = some fi) :
    behavioursFX' P noHost noFX ⟨s, K, f, srcResume a ct hs vs⟩ ⊆
      behavioursOf P noHost ⟨s, f, tgtCall a fi.type vs⟩ :=
  Silmaril.Proofs.Wasm.Models.FXVRuns.lower_complete' hf

/-- **Correctness of the first lowering under `StepFX'`.** -/
theorem lower_correct' {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause} {vs : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs') :
    behavioursFX' P noHost noFX ⟨s, K, f, srcResume a ct hs vs⟩ =
      behavioursOf P noHost ⟨s, f, tgtCall a fi.type vs⟩ :=
  Silmaril.Proofs.Wasm.Models.FXVRuns.lower_correct' hf hr

/--
info: 'Silmaril.Wasm.Models.FXVRuns.abort_src_behaviours_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms abort_src_behaviours_eq

/--
info: 'Silmaril.Wasm.Models.FXVRuns.lower_correct'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lower_correct'

/--
info: 'Silmaril.Wasm.Models.FXVRuns.behavioursFX'_noK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms behavioursFX'_noK

end Silmaril.Wasm.Models.FXVRuns
