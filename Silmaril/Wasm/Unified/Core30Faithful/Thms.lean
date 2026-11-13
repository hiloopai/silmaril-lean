module

public import Silmaril.Wasm.Unified.Core30Dec.Thms

/-!
# Core 3.0 is a faithful model of the 3.0 signature

From the decoder (`Silmaril.Wasm.Unified.Core30Dec`):

* `evalC30_encCode`: **the meaning of an encoded program in the 3.0 opcode algebra is exactly
  that program**, `{is}`.
* `obs_encCode`: `model30` observes exactly the Core 3.0 behaviours (silmaril's
  `behavioursOf`, reduction `Step P host`) of validated code; `obs_encCode_okTrue`: without
  validation, exactly the Core 3.0 behaviours.
* `sat_iff`: a behaviour sentence about Core 3.0 programs holds of silmaril's (validated)
  behaviours iff its encoding holds in `model30`. So the unified institution, restricted to the
  3.0 signature and this model, says the same things as silmaril's Core 3.0 behaviour
  semantics.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Core30

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Unified Silmaril.Wasm.Atlas

/-- Block meanings of encoded bodies pin the bodies down. -/
theorem forall₂_eq (bs : List (List Instr)) :
    ∀ (js : List (List Instr)), (∀ b ∈ bs, ∀ x ∈ evalC30 (encCode b), x = b) →
    List.Forall₂ (fun j (D : Set (List Instr)) => j ∈ D) js (alg30.evalBlocks (bs.map encCode)) →
    js = bs := by
  induction bs with
  | nil =>
    intro js _ h
    cases h
    rfl
  | cons b bs ih =>
    intro js hb h
    cases h with
    | cons hx hr =>
      rw [hb b (List.mem_cons_self ..) _ hx,
        ih _ (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')) hr]

mutual
/-- The only instruction in the meaning of an encoded instruction is that instruction. -/
theorem eq_of_mem_evalI30 (i : Instr) : ∀ j ∈ evalI30 (enc i), j = i := by
  intro j hj
  rw [evalI30, enc_eq, Alg.evalInstr] at hj
  obtain ⟨hh, hi, hd, hF⟩ := hj
  exact eq_of_heads hh hi hd (forall₂_eq _ _ (fun b _ => eq_of_mem_evalC30 b) hF)
termination_by sizeOf i
decreasing_by exact sizeOf_lt_of_mem_bodies ‹_›

/-- The only program in the meaning of an encoded program is that program. -/
theorem eq_of_mem_evalC30 (is : List Instr) : ∀ js ∈ evalC30 (encCode is), js = is := by
  match is with
  | [] =>
    intro js hjs
    exact hjs
  | i :: is =>
    intro js hjs
    unfold evalC30 at hjs
    rw [encCode, Alg.evalCode] at hjs
    obtain ⟨j, t, rfl, hj, ht⟩ := hjs
    rw [eq_of_mem_evalI30 i j hj, eq_of_mem_evalC30 is t ht]
termination_by sizeOf is
end

/-- **The meaning of an encoded program is that program.** -/
theorem evalC30_encCode (is : List Instr) : evalC30 (encCode is) = {is} :=
  Set.ext fun js => ⟨fun h => eq_of_mem_evalC30 is js h, fun h => h ▸ mem_evalCode_encCode is⟩

variable (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
  (okc : List Instr → Prop)

/-- **`model30` observes exactly the Core 3.0 behaviours of validated code.** -/
theorem obs_encCode (is : List Instr) (vs : List Val) :
    (model30 P host s f okc).obs (encCode is, vs) = {b | okc is ∧ b ∈ behCode P host s f is vs} := by
  ext b
  change (∃ js ∈ evalC30 (encCode is), okc js) ∧
      (∃ js ∈ evalC30 (encCode is), okc js ∧ b ∈ behCode P host s f js vs) ↔ _
  rw [evalC30_encCode]
  simp only [Set.mem_singleton_iff, exists_eq_left, Set.mem_ofPred_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- Without validation, `model30` observes exactly the Core 3.0 behaviours. -/
theorem obs_encCode_okTrue (is : List Instr) (vs : List Val) :
    (model30 P host s f okTrue).obs (encCode is, vs) = behCode P host s f is vs := by
  rw [obs_encCode]
  ext b
  exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

/-- The encoding of calls. -/
def encCall (x : List Instr × List Val) : Call (List Val) sig30 := (encCode x.1, x.2)

/-- **A sentence about Core 3.0 programs holds of silmaril's validated behaviours iff its
encoding holds in `model30`.** -/
theorem sat_iff (φ : BSen (List Instr × List Val) (Behaviour Val)) :
    Sat (model30 P host s f okc) (φ.rename encCall) ↔
      φ.Sat fun x => {b | okc x.1 ∧ b ∈ behCode P host s f x.1 x.2} := by
  unfold Sat
  rw [BSen.sat_rename]
  exact BSen.sat_congr (fun x => obs_encCode P host s f okc x.1 x.2) φ

end Silmaril.Wasm.Unified.Core30
