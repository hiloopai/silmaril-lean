module

public import Silmaril.Wasm.Unified.Core30.Defs

/-!
# Core 3.0 in the unified institution: the encoding is observed

* `enc_eq`: the encoding of an instruction is its opcode, immediates, encoded bodies and handler
  table.
* `arity30_head`: the typing table `arity30` agrees with the encoding (number of immediates and
  of blocks).
* `mem_evalCode_encCode`: **the encoded code is among the meanings of its encoding** in the 3.0
  opcode algebra.
* `behCode_subset_obs`: for code passing validation, every Core 3.0 behaviour (silmaril's
  `behavioursOf`, reduction `Step P host`) is an observation of the encoded call in
  `model30`; `sat_may_of_mem_behCode`: hence the `may` sentence of a Core 3.0 behaviour holds
  in the model, and `sat_existential`: existential sentences true of silmaril's behaviours
  hold.

The converse inclusion (the meaning of an encoding contains only the encoded code, so
`model30` observes exactly the Core 3.0 behaviours) needs the encoding to be injective. It is
proved with a decoder in `Silmaril.Wasm.Unified.Core30Dec` and `Silmaril.Wasm.Unified.Core30Faithful`.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Core30

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Unified Silmaril.Wasm.Atlas

/-- The encoding of an instruction, in one shape. -/
theorem enc_eq (i : Instr) :
    enc i = .op (op30 i) (immsOf i) (i.bodies.map encCode) (hdlOf i) := by
  cases i <;> rfl

/-- **The typing table agrees with the encoding**: numbers of immediates and of blocks. -/
theorem arity30_head (i : Instr) :
    (arity30 (head i)).imms = (immsOf i).length ∧ (arity30 (head i)).blocks = i.bodies.length := by
  cases i <;> exact ⟨rfl, rfl⟩

/-- A body of an instruction is smaller than the instruction. -/
theorem sizeOf_lt_of_mem_bodies {i : Instr} {b : List Instr} (h : b ∈ i.bodies) :
    sizeOf b < sizeOf i := by
  unfold Instr.bodies at h
  split at h <;> simp at h <;> rcases h with rfl | rfl <;> simp <;> omega

/-- Blocks: pointwise membership of the encoded bodies. -/
theorem forall₂_evalBlocks (bs : List (List Instr))
    (h : ∀ b ∈ bs, b ∈ evalC30 (encCode b)) :
    List.Forall₂ (fun b (D : Set (List Instr)) => b ∈ D) bs (alg30.evalBlocks (bs.map encCode)) := by
  induction bs with
  | nil => exact .nil
  | cons b bs ih =>
    exact .cons (h b (List.mem_cons_self ..)) (ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))

mutual
/-- **An instruction is among the meanings of its encoding.** -/
theorem mem_evalInstr_enc (i : Instr) : i ∈ evalI30 (enc i) := by
  rw [evalI30, enc_eq, Alg.evalInstr]
  exact ⟨rfl, rfl, rfl, forall₂_evalBlocks _ fun b _ => mem_evalCode_encCode b⟩
termination_by sizeOf i
decreasing_by exact sizeOf_lt_of_mem_bodies ‹_›

/-- **Code is among the meanings of its encoding.** -/
theorem mem_evalCode_encCode (is : List Instr) :
    is ∈ evalC30 (encCode is) := by
  match is with
  | [] => exact rfl
  | i :: is =>
    unfold evalC30
    rw [encCode, Alg.evalCode]
    exact ⟨i, is, rfl, mem_evalInstr_enc i, mem_evalCode_encCode is⟩
termination_by sizeOf is
end

variable (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
  (okc : List Instr → Prop)

/-- Validated code: its Core 3.0 behaviours are observations of its encoding. -/
theorem behCode_subset_obs {is : List Instr} (h : okc is) (vs : List Val) :
    behCode P host s f is vs ⊆ (model30 P host s f okc).obs (encCode is, vs) :=
  fun _ hb => ⟨⟨is, mem_evalCode_encCode is, h⟩, is, mem_evalCode_encCode is, h, hb⟩

/-- The `may` sentence of a Core 3.0 behaviour holds in the model. -/
theorem sat_may_of_mem_behCode {is : List Instr} (h : okc is) {vs : List Val}
    {b : Behaviour Val} (hb : b ∈ behCode P host s f is vs) (φ : Behaviour Val → Prop)
    (hφ : φ b) :
    Sat (model30 P host s f okc) (.may (encCode is, vs) φ) :=
  ⟨b, behCode_subset_obs P host s f okc h vs hb, hφ⟩

/-- Existential sentences over encoded calls that hold of silmaril's behaviours (with validated
code) hold in the model. -/
theorem sat_existential {φ : BSen (List Instr × List Val) (Behaviour Val)} (he : φ.Existential)
    (hok : ∀ x : List Instr × List Val, okc x.1)
    (h : φ.Sat fun x => behCode P host s f x.1 x.2) :
    Sat (model30 P host s f okc) (φ.rename fun x => (encCode x.1, x.2)) := by
  unfold Sat
  rw [BSen.sat_rename]
  exact BSen.sat_of_subset_exist (fun x => behCode_subset_obs P host s f okc (hok x) x.2) he h

end Silmaril.Wasm.Unified.Core30
