module

public import Silmaril.Machine.X86.Lir.Code.Defs

/-!
# Where the code of each program point is

`progCode_at` locates the code of every program point of a Lir function in the
abstract code of the whole program, at the offset `pointAddr` computes, and
`prologue_at` does the same for a function's prologue. `code_drop` turns such a
decomposition into the bytes found at an address of the image.
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.Machine

theorem flatten_split {α : Type} (L : List (List α)) {i : Nat} (h : i < L.length) :
    L.flatten = (L.take i).flatten ++ L[i] ++ (L.drop (i + 1)).flatten := by
  conv => lhs; rw [← List.take_append_drop i L]
  rw [List.flatten_append, List.drop_eq_getElem_cons h, List.flatten_cons, List.append_assoc]

theorem take_succ_flatten {α : Type} (L : List (List α)) {i : Nat} (h : i < L.length) :
    (L.take (i + 1)).flatten = (L.take i).flatten ++ L[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [Option.toList_some, List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil]

variable {P : Type} (A : Assign P)

theorem blockChunks_length (f : Lir.FuncId) (ns : Nat) (b : Lir.Block P) :
    (blockChunks A f ns b).length = b.instrs.length + 1 := by
  simp [blockChunks]

theorem blockChunks_instr (f : Lir.FuncId) (ns : Nat) (b : Lir.Block P) {i : Nat}
    (h : i < b.instrs.length) :
    (blockChunks A f ns b)[i]'(by rw [blockChunks_length]; omega) = instrChunk A ns b.instrs[i] := by
  simp only [blockChunks]
  rw [List.getElem_append_left (by simpa using h)]
  simp

theorem blockChunks_term (f : Lir.FuncId) (ns : Nat) (b : Lir.Block P) :
    (blockChunks A f ns b)[b.instrs.length]'(by rw [blockChunks_length]; omega) =
      termChunk A f ns b.term := by
  simp [blockChunks]

theorem funcCodes_length (p : Lir.Prog P) : (funcCodes A p).length = p.funcs.length := by
  simp [funcCodes]

theorem funcCodes_getElem (p : Lir.Prog P) {f : Nat} (h : f < (funcCodes A p).length) :
    (funcCodes A p)[f] = funcCode A f (p.funcs[f]'(by rwa [funcCodes_length] at h)) := by
  simp [funcCodes]

/-- The code of point `⟨f, l, i⟩` sits at offset `pointAddr - codeBase`. -/
theorem progCode_at (p : Lir.Prog P) (codeBase : Nat) {f : Lir.FuncId} {fn : Lir.Func P}
    {l : Lir.Label} {b : Lir.Block P} {i : Nat} (hf : p.func? f = some fn)
    (hb : fn.blocks[l]? = some b) (hi : i < (blockChunks A f (nslots fn) b).length) :
    ∃ pre post, progCode A p = pre ++ (blockChunks A f (nslots fn) b)[i] ++ post ∧
      codeBase + lenOf pre = pointAddr A p codeBase ⟨f, l, i⟩ := by
  have hf' : f < p.funcs.length ∧ p.funcs[f]? = some fn := by
    simp only [Lir.Prog.func?] at hf
    exact ⟨(List.getElem?_eq_some_iff.mp hf).1, hf⟩
  obtain ⟨hfl, hfe⟩ := List.getElem?_eq_some_iff.mp hf'.2
  obtain ⟨hbl, hbe⟩ := List.getElem?_eq_some_iff.mp hb
  have hF : f < (funcCodes A p).length := by rwa [funcCodes_length]
  have e1 := flatten_split (funcCodes A p) hF
  rw [funcCodes_getElem, hfe] at e1
  have hB : l < (fn.blocks.map (blockCode A f (nslots fn))).length := by simpa using hbl
  have e2 := flatten_split (fn.blocks.map (blockCode A f (nslots fn))) hB
  simp only [List.getElem_map, hbe] at e2
  have e3 := flatten_split (blockChunks A f (nslots fn) b) hi
  refine ⟨(funcCodes A p |>.take f).flatten ++ prologue A f fn ++
      ((fn.blocks.map (blockCode A f (nslots fn))).take l).flatten ++
      ((blockChunks A f (nslots fn) b).take i).flatten,
    ((blockChunks A f (nslots fn) b).drop (i + 1)).flatten ++
      ((fn.blocks.map (blockCode A f (nslots fn))).drop (l + 1)).flatten ++
      ((funcCodes A p).drop (f + 1)).flatten, ?_, ?_⟩
  · rw [progCode, e1, funcCode, e2, blockCode, e3]
    simp only [List.append_assoc]
  · simp only [pointAddr, hf, Option.getD_some, hb, lenOf_append, funcOff, blockOff, chunkOff]
    omega

/-- The prologue of function `f` sits at offset `funcOff f`. -/
theorem prologue_at (p : Lir.Prog P) {f : Lir.FuncId} {fn : Lir.Func P}
    (hf : p.func? f = some fn) :
    ∃ post, progCode A p = ((funcCodes A p).take f).flatten ++ prologue A f fn ++ post := by
  have hf' : p.funcs[f]? = some fn := hf
  obtain ⟨hfl, hfe⟩ := List.getElem?_eq_some_iff.mp hf'
  have hF : f < (funcCodes A p).length := by rwa [funcCodes_length]
  have e1 := flatten_split (funcCodes A p) hF
  rw [funcCodes_getElem, hfe] at e1
  exact ⟨(fn.blocks.map (blockCode A f (nslots fn))).flatten ++ ((funcCodes A p).drop (f + 1)).flatten,
    by rw [progCode, e1, funcCode]; simp only [List.append_assoc]⟩

theorem layout_func (p : Lir.Prog P) (codeBase : Nat) (f : Lir.FuncId) :
    (layout A p codeBase).func f = codeBase + lenOf ((funcCodes A p).take f).flatten := rfl

theorem layout_block (p : Lir.Prog P) (codeBase : Nat) (f : Lir.FuncId) (l : Lir.Label) :
    (layout A p codeBase).block f l = pointAddr A p codeBase ⟨f, l, 0⟩ := by
  simp [layout, pointAddr, chunkOff, lenOf]

/-- The address of the next point of a block. -/
theorem pointAddr_succ (p : Lir.Prog P) (codeBase : Nat) {f : Lir.FuncId} {fn : Lir.Func P}
    {l : Lir.Label} {b : Lir.Block P} {i : Nat} (hf : p.func? f = some fn)
    (hb : fn.blocks[l]? = some b) (hi : i < b.instrs.length) :
    pointAddr A p codeBase ⟨f, l, i + 1⟩ =
      pointAddr A p codeBase ⟨f, l, i⟩ + lenOf (instrChunk A (nslots fn) b.instrs[i]) := by
  simp only [pointAddr, hf, Option.getD_some, hb, chunkOff]
  rw [take_succ_flatten _ (by rw [blockChunks_length]; omega), blockChunks_instr A f _ b hi]
  simp only [lenOf_append]
  omega

/-- Bytes at an address of the image, from a decomposition of the abstract code. -/
theorem code_drop (L : Layout) (codeBase : Nat) {code pre chunk post : List AInstr}
    (h : code = pre ++ chunk ++ post) :
    (encodeAt L codeBase code).drop (lenOf pre) =
      encodeAt L (codeBase + lenOf pre) chunk ++ encodeAt L (codeBase + lenOf pre + lenOf chunk) post := by
  rw [h, encodeAt_append, encodeAt_append, List.drop_append_of_le_length (by simp)]
  simp [Nat.add_assoc]

theorem lenOf_le {code pre chunk post : List AInstr} (h : code = pre ++ chunk ++ post) : lenOf pre + lenOf chunk ≤ lenOf code := by
  rw [h]; simp

end Silmaril.X86.Backend
