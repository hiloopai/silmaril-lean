module

public import Silmaril.Compiler.Target.X86Layout.Defs

/-! # The tabulated x86-64 layout is the verified one

`fastLayout A p c = layout A p c`, hence `compileX86Fast = X86.Backend.compile`. The
second equation is a `@[csimp]` lemma: code that calls `X86.Backend.compile` (the
driver, through `Backends.codeX86`) runs `compileX86Fast`, and the bytes it emits are
those `X86.Backend.compile_refines` speaks about.
-/

@[expose] public section

namespace Silmaril.Compile.Target

open Silmaril.Machine
open Silmaril.X86.Backend

/-- `o` plus the sum of `w` over each proper prefix of `xs`, shortest first. -/
def prefixSums {α : Type} (w : α → Nat) : Nat → List α → List Nat
  | _, [] => []
  | o, x :: xs => o :: prefixSums w (o + w x) xs

theorem getElem?_prefixSums {α : Type} (w : α → Nat) (o : Nat) (xs : List α) (i : Nat) :
    (prefixSums w o xs)[i]? =
      if i < xs.length then some (o + ((xs.take i).map w).sum) else none := by
  induction xs generalizing o i with
  | nil => simp [prefixSums]
  | cons x xs ih =>
    cases i with
    | zero => simp [prefixSums]
    | succ i => simp [prefixSums, ih, Nat.add_assoc]

/-- A fold that pushes the running offset and adds a width. -/
theorem foldl_offsets {α : Type} (w : α → Nat) (f : Array Nat × Nat → α → Array Nat × Nat)
    (hf : ∀ os o x, f (os, o) x = (os.push o, o + w x)) (xs : List α) (os : Array Nat)
    (o : Nat) :
    xs.foldl f (os, o) = (os ++ (prefixSums w o xs).toArray, o + (xs.map w).sum) := by
  induction xs generalizing os o with
  | nil => simp [prefixSums]
  | cons x xs ih => simp [hf, ih, prefixSums, Nat.add_assoc]

/-- `foldl_offsets`, also pushing one value per element. -/
theorem foldl_offsets₂ {α β : Type} (w : α → Nat) (g : α → β)
    (f : Array Nat × Array β × Nat → α → Array Nat × Array β × Nat)
    (hf : ∀ fo bo o x, f (fo, bo, o) x = (fo.push o, bo.push (g x), o + w x)) (xs : List α)
    (fo : Array Nat) (bo : Array β) (o : Nat) :
    xs.foldl f (fo, bo, o) =
      (fo ++ (prefixSums w o xs).toArray, bo ++ (xs.map g).toArray, o + (xs.map w).sum) := by
  induction xs generalizing fo bo o with
  | nil => simp [prefixSums]
  | cons x xs ih => simp [hf, ih, prefixSums, Nat.add_assoc]

theorem lenOf_flatten (l : List (List AInstr)) : lenOf l.flatten = (l.map lenOf).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

variable {P : Type} (A : Assign P)

theorem funcOff_eq_sum (p : Lir.Prog P) (g : Nat) :
    funcOff A p g = ((p.funcs.zipIdx.take g).map fun x => lenOf (funcCode A x.2 x.1)).sum := by
  simp [funcOff, funcCodes, List.mapIdx_eq_zipIdx_map, lenOf_flatten, List.map_take,
    Function.comp_def]

theorem blockOff_eq_sum (f : Lir.FuncId) (fn : Lir.Func P) (l : Lir.Label) :
    blockOff A f fn l = lenOf (prologue A f fn) +
      ((fn.blocks.take l).map fun b => lenOf (blockCode A f (nslots fn) b)).sum := by
  simp [blockOff, lenOf_flatten, List.map_take, Function.comp_def]

/-- The block offsets `fastLayout` tabulates for function `f` of body `fn`. -/
theorem blockOffs_eq (f : Lir.FuncId) (fn : Lir.Func P) :
    (fn.blocks.foldl (fun s b => (s.1.push s.2, s.2 + lenOf (blockCode A f (nslots fn) b)))
      (#[], lenOf (prologue A f fn))).1 =
      (prefixSums (fun b => lenOf (blockCode A f (nslots fn) b)) (lenOf (prologue A f fn))
        fn.blocks).toArray := by
  rw [foldl_offsets _ _ (fun _ _ _ => rfl)]
  simp

theorem fastLayout_eq (p : Lir.Prog P) (c : Nat) : fastLayout A p c = layout A p c := by
  simp only [fastLayout]
  rw [foldl_offsets₂ (fun x => lenOf (funcCode A x.2 x.1))
    (fun x => (x.1.blocks.foldl
      (fun (os, o) b => (os.push o, o + lenOf (blockCode A x.2 (nslots x.1) b)))
      (#[], lenOf (prologue A x.2 x.1))).1) _ (fun _ _ _ _ => rfl)]
  simp only [layout, Array.empty_append, List.getElem?_toArray,
    getElem?_prefixSums, List.getElem?_map, List.getElem?_zipIdx, List.length_zipIdx,
    blockOffs_eq]
  congr 1
  · funext g
    by_cases h : g < p.funcs.length <;> simp [h, funcOff_eq_sum]
  · funext f l
    by_cases h : f < p.funcs.length
    · by_cases hl : l < p.funcs[f].blocks.length <;>
        simp [h, hl, getElem?_prefixSums, funcOff_eq_sum, blockOff_eq_sum, Lir.Prog.func?,
          Nat.add_assoc]
    · simp [h]

@[csimp] theorem compile_eq_compileX86Fast :
    @X86.Backend.compile = @compileX86Fast := by
  funext P A p c
  simp only [X86.Backend.compile, compileX86Fast, fastLayout_eq]
  cases progErrors A p <;> rfl

end Silmaril.Compile.Target
