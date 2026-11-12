module

public import Silmaril.Compiler.Contract.Defs
/-! # A placement obstruction to deleting unreachable symbol references

The frozen `Contract.mirPass` quantifies over every valid output placement, even
when its memory is smaller than `MirSem.need`. Removing an unreachable `addr`
can make a previously required data placement optional. Consequently, wholesale
unreachable-block deletion does not satisfy this contract without an additional
check or a different placement/convention clause. No compiler pass is installed
here: this is a regression counterexample for that proposed theorem.
-/

@[expose] public section

namespace Silmaril.Compile.Mir.UnreachableLimit

open Silmaril.Compile.Contract
open Silmaril.Compile.Contract.MirSem

/-- Entry jumps over the only address reference and returns. -/
def inputFunc : Func :=
  { name := "main", params := [], results := 0,
    blocks := #[⟨#[], .jump 2⟩, ⟨#[.addr 0 "object" 0], .trap⟩, ⟨#[], .ret []⟩] }

/-- Empty the unreachable block, retaining its index and every definition. -/
def outputFunc : Func :=
  { inputFunc with blocks := #[⟨#[], .jump 2⟩, ⟨#[], .trap⟩, ⟨#[], .ret []⟩] }

def object : Data := { name := "object", size := 1, align := 1 }
def input : Array Mir.Unit := #[{ funcs := #[inputFunc], data := #[object] }]
def output : Array Mir.Unit := #[{ funcs := #[outputFunc], data := #[object] }]

def emptyPlacement : Placement :=
  ⟨fun _ => none, fun s => if s = "main" then some 1 else none, 0⟩

/-- Both programs have entry states; the counterexample does not erase entry. -/
theorem entries_exist : (start input emptyPlacement 0).isSome ∧
    (start output emptyPlacement 0).isSome := by decide

/-- Data definitions, hence the contract's memory estimate, are unchanged. -/
theorem need_unchanged (base : Nat) : need output base = need input base := rfl

private theorem output_reach {s : String} (h : Reach output s) : s = "main" := by
  induction h with
  | entry hf =>
    simp [funcDefs, output, outputFunc, inputFunc] at hf
    subst hf
    rfl
  | func hn hf hb hi hs ih =>
    subst ih
    simp [funcOf, funcDefs, output, outputFunc, inputFunc] at hf
    subst hf
    simp at hb
    rcases hb with rfl | rfl | rfl <;> simp at hi
  | data hn hd hr ih =>
    subst ih
    simp [dataOf, dataDefs, output, object] at hd

/-- The output no longer demands the data object. Its entry has pointer 1. -/
theorem output_valid : emptyPlacement.Valid output 0 := by
  refine ⟨?_, ?_, ?_, ?_, by decide, ?_, ?_⟩
  · intro s hs
    have := output_reach hs
    subst this
    simp [dataOf, dataDefs, output, object]
  · intro s hs
    have := output_reach hs
    subst this
    simp [funcOf, funcDefs, output, outputFunc, inputFunc, emptyPlacement]
  · simp [emptyPlacement]
  · simp [emptyPlacement]
  · intro s a hs
    by_cases hn : s = "main"
    · simp [emptyPlacement, hn] at hs
      omega
    · simp [emptyPlacement, hn] at hs
  · intro s s' a hs hs'
    simp only [emptyPlacement] at hs hs'
    split at hs <;> split at hs' <;> simp_all

/-- In the input the syntactically reachable reference requires a positive,
one-byte data placement; no such placement fits in zero bytes. -/
theorem input_not_valid (P : Placement) : ¬ P.Valid input 0 := by
  intro h
  have hentry : Reach input "main" := .entry (f := inputFunc) (by
    simp [funcDefs, input, inputFunc])
  have href : Reach input "object" := .func (f := inputFunc) hentry
    (by simp [funcOf, funcDefs, input, inputFunc])
    (b := ⟨#[.addr 0 "object" 0], .trap⟩) (i := .addr 0 "object" 0)
    (by simp [inputFunc]) (by simp) (by simp [instrRefs])
  have hp := h.1 "object" href (by simp [dataOf, dataDefs, input, object])
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hp
  have hb := h.2.2.1 object (by simp [dataDefs, input, object]) a ha
  have hm := h.2.2.2.2.1
  simp only [object] at hb
  omega

/-- Any pass performing this particular unreachable-block deletion fails the
frozen contract, irrespective of its behaviour on other programs. -/
theorem deletion_not_mirPass (f : Array Mir.Unit → Array Mir.Unit)
    (hf : f input = output) : ¬ Contract.mirPass f := by
  intro h
  have hv : emptyPlacement.Valid (f input) 0 := by simpa only [hf] using output_valid
  obtain ⟨P, hP, _⟩ := (h input).2 0 (by decide) emptyPlacement hv
  exact input_not_valid P hP

end Silmaril.Compile.Mir.UnreachableLimit
