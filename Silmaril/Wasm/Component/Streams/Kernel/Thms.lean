module

public import Silmaril.Wasm.Component.Streams.Kernel.Defs
public import Silmaril.Proofs.Wasm.Component.Streams.Kernel

/-!
# Byte kernels: the kernels are the specification transformers

Proofs in `Silmaril.Proofs.Wasm.Component.Streams.Kernel` (a simulation of transformers).

On byte inputs (`< 256`), the meaning of each kernel has the same outputs so far and the same
whole output as its specification transformer, and so the closed forms of the specification:

* `kMap_run`: `xs.map f`; `kInc_run`: add one mod 256;
* `kFilter_run`: `xs.filter p`; `kNoDigit_run`: drop the ASCII digits;
* `kTake_run`: `xs.take n`;
* `kLines_run`: the lines of the input (`lines (· == nl)`, the final partial line included), each
  followed by `nl`; by `unlines_lines` this is the input, plus `nl` if it does not end with one;
* `kRechunk_run`: the uniform chunks (`chunksOf n`), each after its length byte.

The same holds for the outputs so far (`kLines_runP`, `kRechunk_runP`, …): the kernels are
`Tr.Equiv` to their specifications on byte inputs. The **core modules** generated from these
kernels (`KM.coreWat`) are not verified against them; `tools/wasm-streams/tests/jco.sh` runs them.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Kernel

open Silmaril.Wasm.Component.Streams
open Silmaril.Proofs.Wasm.Component.Streams.Kernel
open scoped Silmaril.Wasm.Component.Streams.Tr

/-- Bytes. -/
def Bytes (bs : List Nat) : Prop := ∀ b ∈ bs, b < 256

theorem flatten_singletons' {α : Type} (xs : List α) : (xs.map fun x => [x]).flatten = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem kMap_run (e : KExp) (bs : List Nat) :
    (kMap e).tr.run bs = bs.map (fun b => e.eval ⟨0, []⟩ b % 256) := by
  rw [run_sim (sim_map e) bs (fun _ _ => trivial), Tr.run_map]

theorem kMap_runP (e : KExp) (bs : List Nat) :
    (kMap e).tr.runP bs = bs.map (fun b => e.eval ⟨0, []⟩ b % 256) := by
  rw [runP_sim (sim_map e) bs (fun _ _ => trivial), Tr.runP_map]

theorem kFilter_run (c : KExp) (bs : List Nat) (hb : Bytes bs) :
    (kFilter c).tr.run bs = bs.filter (fun b => c.eval ⟨0, []⟩ b != 0) := by
  rw [run_sim (sim_filter c) bs hb, Tr.run_filter]

theorem kFilter_runP (c : KExp) (bs : List Nat) (hb : Bytes bs) :
    (kFilter c).tr.runP bs = bs.filter (fun b => c.eval ⟨0, []⟩ b != 0) := by
  rw [runP_sim (sim_filter c) bs hb, Tr.runP_filter]

theorem kTake_run (n : Nat) (hn : n < M32) (bs : List Nat) (hb : Bytes bs) :
    (kTake n).tr.run bs = bs.take n := by
  rw [run_sim (sim_take n hn) bs hb, Tr.run_take]

theorem kTake_runP (n : Nat) (hn : n < M32) (bs : List Nat) (hb : Bytes bs) :
    (kTake n).tr.runP bs = bs.take n := by
  rw [runP_sim (sim_take n hn) bs hb, Tr.runP_take]

/-- **Lines**: the lines of the input, each followed by `nl`. -/
theorem kLines_run (nl : Nat) (hnl : nl < 256) (bs : List Nat) (hb : Bytes bs) :
    (kLines nl).tr.run bs = (lines (· == nl) bs).flatMap (· ++ [nl]) := by
  rw [run_sim (sim_lines nl hnl) bs hb, linesU, Tr.run_comp', Tr.run_comp', Tr.run_map,
    Tr.run_linesT, flatten_singletons', Tr.run_flatMap]

theorem kLines_runP (nl : Nat) (hnl : nl < 256) (bs : List Nat) (hb : Bytes bs) :
    (kLines nl).tr.runP bs = (linesU nl).runP bs :=
  runP_sim (sim_lines nl hnl) bs hb

/-- The lines kernel gives its input back, with a final `nl` when it does not end with one. -/
theorem kLines_run_eq (nl : Nat) (hnl : nl < 256) (bs : List Nat) (hb : Bytes bs) :
    (kLines nl).tr.run bs = if (cut (· == nl) bs).2 = [] then bs else bs ++ [nl] := by
  rw [kLines_run nl hnl bs hb, unlines_lines (· == nl) nl (fun x hx => by simpa using hx) bs]

/-- **Uniform chunks**: the chunks of `n` bytes, each after its length byte. -/
theorem kRechunk_run (n : Nat) (h1 : 0 < n) (h2 : n ≤ 255) (bs : List Nat) (hb : Bytes bs) :
    (kRechunk n).tr.run bs = (chunksOf n bs).flatMap (fun c => c.length :: c) := by
  rw [run_sim (sim_rechunk n h1 h2) bs hb, rechunkU, Tr.run_comp', Tr.run_comp', Tr.run_map,
    Tr.run_rechunk, flatten_singletons', Tr.run_flatMap]

theorem kRechunk_runP (n : Nat) (h1 : 0 < n) (h2 : n ≤ 255) (bs : List Nat) (hb : Bytes bs) :
    (kRechunk n).tr.runP bs = (rechunkU n).runP bs :=
  runP_sim (sim_rechunk n h1 h2) bs hb

/-! ## The kernels of the tests -/

theorem kInc_run (bs : List Nat) (hb : Bytes bs) : kInc.tr.run bs = bs.map (fun b => (b + 1) % 256) := by
  rw [kInc, kMap_run]
  refine List.map_congr_left fun b hbm => ?_
  have := hb b hbm
  simp only [KExp.eval, M32]
  omega

theorem noDigit_eval (b : Nat) (hb : b < 256) :
    ((KExp.eqz (.ltu (.sub .x (.lit 48)) (.lit 10))).eval ⟨0, []⟩ b != 0) = !(48 ≤ b && b < 58) := by
  simp only [KExp.eval, M32]
  by_cases h : 48 ≤ b ∧ b < 58
  · have : (b + (2 ^ 32 - 48 % 2 ^ 32 % 2 ^ 32)) % 2 ^ 32 < 10 % 2 ^ 32 := by omega
    simp [this, h.1, h.2]
  · have : ¬ (b + (2 ^ 32 - 48 % 2 ^ 32 % 2 ^ 32)) % 2 ^ 32 < 10 % 2 ^ 32 := by omega
    simp only [this, ↓reduceIte]
    by_cases h1 : 48 ≤ b
    · have h2 : ¬ b < 58 := fun h2 => h ⟨h1, h2⟩
      simp [h1, h2]
    · simp [h1]

theorem kNoDigit_run (bs : List Nat) (hb : Bytes bs) :
    kNoDigit.tr.run bs = bs.filter (fun b => !(48 ≤ b && b < 58)) := by
  rw [kNoDigit, kFilter_run _ _ hb]
  exact List.filter_congr fun b hbm => noDigit_eval b (hb b hbm)

end Silmaril.Wasm.Component.Streams.Kernel
