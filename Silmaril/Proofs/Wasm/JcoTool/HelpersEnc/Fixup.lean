module

public import Silmaril.Proofs.Wasm.JcoTool.HelpersEnc.Shim

/-!
# The fixup: `CMod.encode (fixupMod tys)` is silmaril's encoding of `fixupAst tys`

Piece by piece (types, imports, the element segment), then the whole module
(`fixup_encode`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.HelpersEnc

open Silmaril.Wasm
open Silmaril.Wasm.Binaryen.Exe
open Silmaril.Parse.ByteParse (Bytes)
open Silmaril.Parse.ByteParse.Enc (u32 sized)
open Silmaril.Wasm.Component (CoreFuncTy)

/-! ## Imports -/

/-- The CMod import list of the fixup. -/
def fixupImportsC (n : Nat) : List (String × String × CImport) :=
  ((List.range n).map fun i => ("actual", toString i, CImport.func i)) ++
    [("shim", "$imports", .table n n)]

/-- The AST import list of the fixup. -/
def fixupImportsA (n : Nat) : List Import :=
  ((List.range n).map fun i => ⟨"actual", toString i, .func (ixn i)⟩) ++
    [⟨"shim", "$imports", .table (tableTy n)⟩]

theorem limits_eq {n : Nat} (h : n < 2 ^ 32) : CMod.limits n n = some (0x01 :: (encU n ++ encU n)) := by
  show (do let a ← u32 n; let b ← u32 n; pure (0x01 :: (a ++ b))) = _
  rw [u32_of_lt h]
  rfl

theorem import_func_eq (mn nm : String) {i : Nat} (h : i < 2 ^ 32) :
    CMod.import_ (mn, nm, .func i) = (encImport ⟨mn, nm, .func (ixn i)⟩).toOption := by
  unfold CMod.import_
  simp only [name_eq, u32_of_lt h]
  show _ = (do pure ((← encName mn) ++ (← encName nm) ++ ([0x00] ++ encIdx (ixn i : Idx .type_))) :
    Except String _).toOption
  rw [encIdx_ixn h]
  cases encName mn <;> cases encName nm <;> rfl

theorem import_table_eq (mn nm : String) {n : Nat} (h : n < 2 ^ 32) :
    CMod.import_ (mn, nm, .table n n) = (encImport ⟨mn, nm, .table (tableTy n)⟩).toOption := by
  unfold CMod.import_
  simp only [name_eq, limits_eq h]
  show _ = (do pure ((← encName mn) ++ (← encName nm) ++ ([0x01] ++ (← encTableType (tableTy n)))) :
    Except String _).toOption
  rw [encTableType_eq h]
  cases encName mn <;> cases encName nm <;> rfl

theorem imports_rel {n : Nat} (hn : n < 2 ^ 32) :
    List.Forall₂ (fun x y => CMod.import_ x = (encImport y).toOption)
      (fixupImportsC n) (fixupImportsA n) := by
  refine List.rel_append (forall₂_maps fun i hi => ?_) (List.Forall₂.cons ?_ List.Forall₂.nil)
  · exact import_func_eq "actual" (toString i) (Nat.lt_trans (List.mem_range.mp hi) hn)
  · exact import_table_eq "shim" "$imports" hn

/-! ## The element segment -/

/-- The AST segment of the fixup. -/
def fixupElem (n : Nat) : Elem :=
  ⟨Helpers.funcref, (List.range n).map fun i => [.refFunc (ixn i)],
    .active (ixn 0) [.intConst .i32 (BitVec.ofNat 32 0)]⟩

theorem encExpr_refFunc (f : Nat) :
    encExpr [.refFunc (ixn f)] = .ok (([0xD2] ++ encIdx (ixn f : Idx .func)) ++ [] ++ [0x0B]) := rfl

theorem refFunc_eq {f : Nat} (h : f < 2 ^ 32) :
    (fun b => 0xd2 :: (b ++ [0x0b])) <$> u32 f = (encExpr [.refFunc (ixn f)]).toOption := by
  rw [u32_of_lt h, encExpr_refFunc, encIdx_ixn h]
  simp [Except.toOption]

theorem elem_eq {n : Nat} (hn : n < 2 ^ 32) :
    CMod.elem (0, List.range n) = (encElem (fixupElem n)).toOption := by
  have hv : Silmaril.Parse.ByteParse.Enc.vec (fun f => (fun b => 0xd2 :: (b ++ [0x0b])) <$> u32 f)
      (List.range n) = (encVec encExpr ((List.range n).map fun i => [.refFunc (ixn i)])).toOption :=
    vec_eq (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun f hf =>
      refFunc_eq (Nat.lt_trans (List.mem_range.mp hf) hn)))
  have hz : encU 4 = [4] := by rw [encU]; rfl
  have ho : encExpr [.intConst .i32 (BitVec.ofNat 32 0)] =
      .ok (([0x41] ++ encS (BitVec.ofNat 32 0).toInt) ++ [] ++ [0x0B]) := rfl
  have he : encElem (fixupElem n) = (do
      let v ← encVec encExpr ((List.range n).map fun i => [.refFunc (ixn i)])
      pure (encU 4 ++ (([0x41] ++ encS (BitVec.ofNat 32 0).toInt) ++ [] ++ [0x0B]) ++ v)) := by
    unfold encElem
    simp only [fixupElem, Helpers.funcref, RefType.mk.injEq, Bool.true_eq_false, false_and,
      ↓reduceIte, ho]
    rfl
  show (do
      let o ← CMod.i32Const 0
      let fs ← Silmaril.Parse.ByteParse.Enc.vec _ (List.range n)
      pure (0x04 :: (o ++ [0x0b] ++ fs))) = _
  rw [i32Const_eq (by decide), hv, he, hz]
  cases encVec encExpr ((List.range n).map fun i => [.refFunc (ixn i)]) <;>
    simp [Except.toOption, bind, Except.bind, pure, Except.pure]

/-! ## The whole fixup -/

/-- What a successful `CMod.encode` of the fixup consists of. -/
theorem fixup_bytes {tys : List CoreFuncTy} {b : ByteArray}
    (h : CMod.encode (New.fixupMod tys) = some b) :
    ∃ ty im el, CMod.vecSec 1 CMod.funcType tys = some ty ∧
      CMod.vecSec 2 CMod.import_ (fixupImportsC tys.length) = some im ∧
      CMod.vecSec 9 CMod.elem [(0, List.range tys.length)] = some el ∧
      b.data.toList = [0, 97, 115, 109, 1, 0, 0, 0] ++ ty ++ im ++ el := by
  obtain ⟨ty, hty, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨im, him, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨fn, hfn, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tb, htb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ex, hex, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨el, hel, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨cd, hcd, h⟩ := Option.bind_eq_some_iff.mp h
  have hb : b.data.toList = [0, 97, 115, 109, 1, 0, 0, 0] ++ ty ++ im ++ fn ++ tb ++ ex ++ st ++
      el ++ cd := by rw [← Option.some.inj h]
  have hz : fn = [] ∧ tb = [] ∧ ex = [] ∧ st = [] ∧ cd = [] :=
    ⟨(Option.some.inj hfn).symm, (Option.some.inj htb).symm, (Option.some.inj hex).symm,
      (Option.some.inj hst).symm, (Option.some.inj hcd).symm⟩
  refine ⟨ty, im, el, hty, him, hel, ?_⟩
  rw [hb, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2]
  simp only [List.append_nil]

/-- **The fixup's bytes are silmaril's encoding of `fixupAst tys`.** -/
theorem fixup_encode {tys : List CoreFuncTy} (hn : tys.length < 2 ^ 32) {b : ByteArray}
    (h : CMod.encode (New.fixupMod tys) = some b) :
    encodeModule? (fixupAst tys) = .ok b.data.toList := by
  obtain ⟨ty, im, el, hty, him, hel, hb⟩ := fixup_bytes h
  obtain ⟨v1, hv1, hs1⟩ := vecSec_ok (types_rel tys) hty
  obtain ⟨v2, hv2, hs2⟩ := vecSec_ok (imports_rel hn) him
  obtain ⟨v9, hv9, hs9⟩ := vecSec_ok (ys := [fixupElem tys.length])
    (List.Forall₂.cons (elem_eq hn) List.Forall₂.nil) hel
  have he : encodeModule? (fixupAst tys) = .ok (header ++ ty ++ im ++ [] ++ [] ++ [] ++ [] ++ [] ++
      [] ++ [] ++ el ++ [] ++ [] ++ []) :=
    encodeModule?_eq rfl hv1 hv2 (encVec_nil _) (encVec_nil encMemory) (encVec_nil _)
      (encVec_nil encGlobal) (encVec_nil encExport) (encVec_nil encCode) (encVec_nil encData)
      (encU32_of_lt (show ([] : List Data).length < 2 ^ 32 by decide)) (encVec_nil _) hv9 hs1 hs2
      (encSection_zero _ _) (encSection_zero _ _) (encSection_zero _ _) (encSection_zero _ _)
      (encSection_zero _ _) (encSection_zero _ _) (encSection_zero _ _) hs9 (encSection_zero _ _)
      (encSection_zero _ _) (encSection_zero _ _)
  rw [he, hb]
  simp only [header, List.append_assoc, List.append_nil, List.nil_append, List.cons_append]

end Silmaril.Wasm.JcoTool.HelpersEnc
