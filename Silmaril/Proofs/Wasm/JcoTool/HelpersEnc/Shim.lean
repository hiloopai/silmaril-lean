module

public import Silmaril.Proofs.Wasm.JcoTool.HelpersEnc.Basic
public import Silmaril.Wasm.JcoTool.New.Defs
public import Mathlib.Data.List.Forall2
import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# The shim: `CMod.encode (shimMod tys)` is silmaril's encoding of `shimAst tys`

Piece by piece (types, functions, table, exports, code), then the whole module
(`shim_encode`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.HelpersEnc

open Silmaril.Wasm
open Silmaril.Wasm.Binaryen.Exe
open Silmaril.Parse.ByteParse (Bytes)
open Silmaril.Parse.ByteParse.Enc (u32 sized)
open Silmaril.Wasm.Component (CoreFuncTy)

/-- `Forall₂` along two maps of one list. -/
theorem forall₂_maps {γ α β : Type} {R : α → β → Prop} {ψ : γ → α} {φ : γ → β} {xs : List γ}
    (h : ∀ x ∈ xs, R (ψ x) (φ x)) : List.Forall₂ R (xs.map ψ) (xs.map φ) :=
  List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr h))

theorem ixn_toNat {k : IndexKind} {n : Nat} (h : n < 2 ^ 32) : (ixn n : Idx k).toNat = n := by
  simp only [ixn, Idx.toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt h

theorem encIdx_ixn {k : IndexKind} {n : Nat} (h : n < 2 ^ 32) :
    encIdx (ixn n : Idx k) = encU n := by
  rw [encIdx, ixn_toNat h]

/-! ## Types -/

theorem numType_eq (x : NumType) : some [CMod.numType x] = (encValType (.num x)).toOption := by
  rcases x with (_ | _) | (_ | _) <;> rfl

theorem funcType_eq (t : CoreFuncTy) : CMod.funcType t = (encRecType (ftAst t)).toOption := by
  have hp : Silmaril.Wasm.Component.Binary.Encode.vec (fun x => some [CMod.numType x]) t.params =
      (encVec encValType (t.params.map .num)).toOption :=
    vec_eq (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun x _ => numType_eq x))
  have hr : Silmaril.Wasm.Component.Binary.Encode.vec (fun x => some [CMod.numType x]) t.results =
      (encVec encValType (t.results.map .num)).toOption :=
    vec_eq (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun x _ => numType_eq x))
  show (do let a ← _; let b ← _; pure (0x60 :: (a ++ b))) =
    (encFuncType ⟨t.params.map .num, t.results.map .num⟩).toOption
  rw [hp, hr]
  unfold encFuncType
  cases encVec encValType (t.params.map .num) <;> cases encVec encValType (t.results.map .num) <;> rfl

theorem types_rel (tys : List CoreFuncTy) :
    List.Forall₂ (fun x y => CMod.funcType x = (encRecType y).toOption) tys (tys.map ftAst) :=
  List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun t _ => funcType_eq t)

/-! ## Functions and code -/

/-- The CMod function list of the shim. -/
def shimFuncsC (tys : List CoreFuncTy) : List (Nat × Bytes) :=
  (List.range tys.length).zip tys |>.map fun (i, t) =>
    (i, (CMod.trampoline t.params.length i i).getD [])

/-- The AST function list of the shim. -/
def shimFuncsA (tys : List CoreFuncTy) : List Func :=
  ((List.range tys.length).zip tys).map fun (i, t) => ⟨ixn i, [], trampAst t.params.length i⟩

theorem mem_zip_lt {tys : List CoreFuncTy} {p : Nat × CoreFuncTy}
    (hp : p ∈ (List.range tys.length).zip tys) : p.1 < tys.length ∧ p.2 ∈ tys := by
  have h := List.of_mem_zip hp
  exact ⟨List.mem_range.mp h.1, h.2⟩

theorem funcs_rel {tys : List CoreFuncTy} (hn : tys.length < 2 ^ 32) :
    List.Forall₂ (fun (x : Nat × Bytes) (y : Func) => u32 x.1 = (pure (encIdx y.type) :
      Except String _).toOption) (shimFuncsC tys) (shimFuncsA tys) :=
  forall₂_maps fun p hp => by
    have hi : p.1 < 2 ^ 32 := Nat.lt_trans (mem_zip_lt hp).1 hn
    show u32 p.1 = some (encIdx (ixn p.1 : Idx .type_))
    rw [u32_of_lt hi, encIdx_ixn hi]

/-- The bytes of the local gets of `0 … p-1`. -/
theorem localGets_ok {p : Nat} (hp : p ≤ 2 ^ 32) :
    Silmaril.Parse.ByteParse.Enc.list CMod.localGet (List.range p) =
      (encInstrs ((List.range p).map fun j => .localGet (ixn j))).toOption := by
  rw [encInstrs_eq]
  refine list_eq (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun j hj => ?_))
  have hj' : j < 2 ^ 32 := Nat.lt_of_lt_of_le (List.mem_range.mp hj) hp
  show (0x20 :: ·) <$> u32 j = some ([0x20] ++ encIdx (ixn j : Idx .local))
  rw [u32_of_lt hj', encIdx_ixn hj']
  rfl

theorem i32Const_eq {i : Nat} (hi : i < 2 ^ 31) :
    CMod.i32Const i = some ([0x41] ++ encS (BitVec.ofNat 32 i).toInt) := by
  have h1 : (BitVec.ofNat 32 i).toNat = i := by
    rw [BitVec.toNat_ofNat]; omega
  have ht : (BitVec.ofNat 32 i).toInt = (i : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by omega), h1]
  have hs : Silmaril.Parse.ByteParse.Enc.sN 32 (i : Int) = some (encS (i : Int)) := by
    unfold Silmaril.Parse.ByteParse.Enc.sN
    simp only [show 0 < 32 ∧ -(2 ^ (32 - 1) : Int) ≤ (i : Int) ∧ (i : Int) < 2 ^ (32 - 1) by omega,
      and_self, ↓reduceIte]
  show (0x41 :: ·) <$> Silmaril.Parse.ByteParse.Enc.sN 32 (i : Int) = _
  rw [hs, ht]
  rfl


theorem encList_ok {α : Type} {g : α → Except String (List UInt8)} {xs : List α}
    (h : ∀ x ∈ xs, ∃ b, g x = .ok b) : ∃ bs, encList g xs = .ok bs := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨b, hb⟩ := h x List.mem_cons_self
    obtain ⟨bs, hbs⟩ := ih fun y hy => h y (List.mem_cons_of_mem x hy)
    exact ⟨b ++ bs, by
      show (do pure ((← g x) ++ (← encList g xs)) : Except String _) = _
      rw [hb, hbs]; rfl⟩

theorem trampAst_ok (p i : Nat) : ∃ tb, encInstrs (trampAst p i) = .ok tb := by
  rw [encInstrs_eq]
  refine encList_ok fun x hx => ?_
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact ⟨_, rfl⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, rfl⟩
    · rcases List.mem_singleton.mp hx with rfl
      exact ⟨_, rfl⟩

theorem localGets_enc (p : Nat) :
    ∃ ls, encInstrs ((List.range p).map fun j => .localGet (ixn j)) = .ok ls := by
  rw [encInstrs_eq]
  exact encList_ok fun x hx => by
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact ⟨_, rfl⟩

/-- The last two instructions of a trampoline. -/
theorem trampTail_enc (i : Nat) :
    encList encInstr [.intConst .i32 (BitVec.ofNat 32 i), .callIndirect (ixn 0) (ixn i)] =
      .ok (([0x41] ++ encS (BitVec.ofNat 32 i).toInt) ++
        (([0x11] ++ encIdx (ixn i : Idx .type_) ++ encIdx (ixn 0 : Idx .table)) ++ [])) := rfl

theorem tramp_eq {p i : Nat} (hp : p ≤ 2 ^ 32) (hi : i < 2 ^ 31) :
    CMod.trampoline p i i = (encInstrs (trampAst p i)).toOption := by
  have hi32 : i < 2 ^ 32 := Nat.lt_trans hi (by decide)
  obtain ⟨ls, hls⟩ := localGets_enc p
  have hl : Silmaril.Parse.ByteParse.Enc.list CMod.localGet (List.range p) = some ls := by
    rw [localGets_ok hp, hls]; rfl
  have he : encInstrs (trampAst p i) = .ok (ls ++ (([0x41] ++ encS (BitVec.ofNat 32 i).toInt) ++
      (([0x11] ++ encU i ++ encU 0) ++ []))) := by
    unfold trampAst
    rw [encInstrs_eq, encList_append, ← encInstrs_eq, hls, trampTail_enc, encIdx_ixn hi32,
      encIdx_ixn (by decide)]
    rfl
  show (do let ls ← Silmaril.Parse.ByteParse.Enc.list CMod.localGet (List.range p)
           let c ← CMod.i32Const i; let t ← u32 i
           pure (ls ++ c ++ (0x11 :: t) ++ [0x00])) = _
  have h0 : encU 0 = [0] := by rw [encU]; rfl
  rw [hl, i32Const_eq hi, u32_of_lt hi32, he, h0]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Except.toOption,
    List.append_assoc, List.cons_append, List.nil_append, List.append_nil]

theorem encU_zero : encU 0 = [0] := by rw [encU]; rfl

theorem encLocals_nil : encLocals [] = .ok [0] := by
  show (do pure ((← encU32 0) ++ (← encList _ [])) : Except String _) = _
  rw [encU32_of_lt (by decide), encU_zero]
  rfl

theorem code_eq {p i : Nat} (hp : p ≤ 2 ^ 32) (hi : i < 2 ^ 31) :
    CMod.code (i, (CMod.trampoline p i i).getD []) =
      (encCode ⟨ixn i, [], trampAst p i⟩).toOption := by
  obtain ⟨tb, htb⟩ := trampAst_ok p i
  have ht : CMod.trampoline p i i = some tb := by rw [tramp_eq hp hi, htb]; rfl
  have he : encExpr (trampAst p i) = .ok (tb ++ [0x0B]) := by
    show (do pure ((← encInstrs (trampAst p i)) ++ [0x0B]) : Except String _) = _
    rw [htb]; rfl
  have hc : encCode ⟨ixn i, [], trampAst p i⟩ =
      (do let n ← encU32 (0x00 :: (tb ++ [0x0b])).length; pure (n ++ (0x00 :: (tb ++ [0x0b])))) := by
    unfold encCode
    simp only [List.length_nil, Nat.ofNat_pos, Nat.pow_pos, ↓reduceIte, Func.locals, Func.body]
    rw [encLocals_nil, he]
    rfl
  rw [ht, hc]
  show sized (0x00 :: (tb ++ [0x0b])) = _
  show (do let n ← u32 (0x00 :: (tb ++ [0x0b])).length; pure (n ++ (0x00 :: (tb ++ [0x0b])))) = _
  rw [u32_eq]
  cases encU32 (0x00 :: (tb ++ [0x0b])).length <;> rfl

theorem codes_rel {tys : List CoreFuncTy} (hn : tys.length < 2 ^ 31)
    (hp : ∀ t ∈ tys, t.params.length ≤ 2 ^ 32) :
    List.Forall₂ (fun x y => CMod.code x = (encCode y).toOption)
      (shimFuncsC tys) (shimFuncsA tys) :=
  forall₂_maps fun q hq => by
    have hq' := mem_zip_lt hq
    exact code_eq (hp q.2 hq'.2) (Nat.lt_trans hq'.1 hn)

/-! ## Empty pieces -/

theorem encVec_nil {α : Type} (g : α → Except String (List UInt8)) : encVec g [] = .ok [0] := by
  show (do pure ((← encU32 0) ++ (← encList g [])) : Except String _) = _
  rw [encU32_of_lt (by decide), encU_zero]
  rfl

theorem encSection_zero (n : UInt8) (body : List UInt8) : encSection n 0 body = .ok [] := rfl

/-! ## The table -/

theorem fin64_val {n : Nat} (h : n < 2 ^ 32) : (Fin.ofNat (2 ^ 64) n).val = n := by
  simp only [Fin.val_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans h (by decide))

theorem encTableType_eq {n : Nat} (h : n < 2 ^ 32) :
    encTableType (tableTy n) = .ok ([0x70] ++ ([0x01] ++ encU n ++ encU n)) := by
  show (do
      let l ← encMemory ⟨.i32, ⟨Fin.ofNat _ n, some (Fin.ofNat _ n)⟩⟩
      pure (encRefType Helpers.funcref ++ l) : Except String _) = _
  have hm : encMemory ⟨.i32, ⟨Fin.ofNat _ n, some (Fin.ofNat _ n)⟩⟩ =
      .ok ([0x01] ++ encU n ++ encU n) := by
    show (do let lo ← encU32 (Fin.ofNat (2 ^ 64) n).val
             pure ([0x01] ++ lo ++ (← encU32 (Fin.ofNat (2 ^ 64) n).val)) : Except String _) = _
    rw [fin64_val h, encU32_of_lt h]
    rfl
  rw [hm]
  rfl

/-- The table section of the shim. -/
theorem table_ok {n : Nat} (h : n < 2 ^ 32) {l s : Bytes} (hl' : CMod.limits n n = some l)
    (hs : CMod.section_ 0x04 (0x01 :: 0x70 :: l) = some s) :
    ∃ v, encVec (encTableWith encExpr) [⟨tableTy n, [.refNull (.abstract .func)]⟩] = .ok v ∧
      encSection 4 1 v = .ok s := by
  have hl : CMod.limits n n = some (0x01 :: (encU n ++ encU n)) := by
    show (do let a ← u32 n; let b ← u32 n; pure (0x01 :: (a ++ b))) = _
    rw [u32_of_lt h]
    rfl
  have ht : encTableWith encExpr ⟨tableTy n, [.refNull (.abstract .func)]⟩ =
      .ok ([0x70] ++ ([0x01] ++ encU n ++ encU n)) := by
    apply encTableWith_of_encTable
    show (if (HeapType.abstract .func) = Helpers.funcref.heap then encTableType (tableTy n)
      else throw "encoder: table initializer is not the default") = _
    simp only [Helpers.funcref, ↓reduceIte]
    exact encTableType_eq h
  refine ⟨encU 1 ++ ([0x70] ++ ([0x01] ++ encU n ++ encU n) ++ []), ?_, ?_⟩
  · show (do pure ((← encU32 1) ++ (← encList _ [_])) : Except String _) = _
    rw [encU32_of_lt (by decide)]
    simp only [encList, ht, bind, Except.bind, pure, Except.pure]
  · have hll : l = 0x01 :: (encU n ++ encU n) := Option.some.inj (hl'.symm.trans hl)
    subst hll
    have he : encU 1 = [1] := by rw [encU]; rfl
    rw [← toOption_eq_some, ← section_eq (by decide : (1 : Nat) ≠ 0), he]
    simpa using hs

/-! ## The exports -/

/-- The CMod export list of the shim. -/
def shimExportsC (n : Nat) : List (String × UInt8 × Nat) :=
  ((List.range n).map fun i => (toString i, (0x00 : UInt8), i)) ++ [("$imports", 0x01, 0)]

/-- The AST export list of the shim. -/
def shimExportsA (n : Nat) : List Export :=
  ((List.range n).map fun i => ⟨toString i, .func (ixn i)⟩) ++ [⟨"$imports", .table (ixn 0)⟩]

theorem export_eq (nm : String) (k : UInt8) (i : Nat) (h : i < 2 ^ 32) (x : ExternIdx)
    (hx : encExport ⟨nm, x⟩ = (do pure ((← encName nm) ++ ([k] ++ encU i)))) :
    CMod.export_ (nm, k, i) = (encExport ⟨nm, x⟩).toOption := by
  show (do
      let a ← Silmaril.Wasm.Component.Binary.Encode.name nm
      let b ← u32 i
      pure (a ++ k :: b)) = _
  rw [hx, name_eq, u32_of_lt h]
  cases encName nm <;> rfl

theorem exports_rel {n : Nat} (hn : n < 2 ^ 32) :
    List.Forall₂ (fun x y => CMod.export_ x = (encExport y).toOption)
      (shimExportsC n) (shimExportsA n) := by
  refine List.rel_append (forall₂_maps fun i hi => ?_) (List.Forall₂.cons ?_ List.Forall₂.nil)
  · have hi' : i < 2 ^ 32 := Nat.lt_trans (List.mem_range.mp hi) hn
    refine export_eq _ _ i hi' _ ?_
    show (do pure ((← encName _) ++ ([0x00] ++ encIdx (ixn i : Idx .func))) : Except String _) = _
    rw [encIdx_ixn hi']
  · refine export_eq _ _ 0 (by decide) _ ?_
    show (do pure ((← encName _) ++ ([0x01] ++ encIdx (ixn 0 : Idx .table))) : Except String _) = _
    rw [encIdx_ixn (by decide)]

/-! ## The whole shim -/

theorem trampAst_dataIdxs (p i : Nat) : Binary.Core.Expr.dataIdxs (trampAst p i) = [] := by
  unfold Binary.Core.Expr.dataIdxs trampAst
  simp only [List.flatMap_append, List.flatMap_map, List.flatMap_cons, List.flatMap_nil]
  simp [Binary.Core.Instr.dataIdxs]

theorem shim_guard (tys : List CoreFuncTy) :
    (Binary.Core.codesDataIdxs ((shimFuncsA tys).map fun f => (f.locals, f.body))).isEmpty =
      true := by
  unfold Binary.Core.codesDataIdxs shimFuncsA
  simp only [List.map_map, List.isEmpty_iff, List.flatMap_eq_nil_iff, List.mem_map]
  rintro _ ⟨q, _, rfl⟩
  exact trampAst_dataIdxs _ _

theorem shimAst_types (tys : List CoreFuncTy) : (shimAst tys).types = tys.map ftAst := rfl
theorem shimAst_imports (tys : List CoreFuncTy) : (shimAst tys).imports = [] := rfl
theorem shimAst_funcs (tys : List CoreFuncTy) : (shimAst tys).funcs = shimFuncsA tys := rfl
theorem shimAst_tables (tys : List CoreFuncTy) : (shimAst tys).tables =
    [⟨tableTy tys.length, [.refNull (.abstract .func)]⟩] := rfl
theorem shimAst_exports (tys : List CoreFuncTy) :
    (shimAst tys).exports = shimExportsA tys.length := rfl
theorem shimAst_memories (tys : List CoreFuncTy) : (shimAst tys).memories = [] := rfl
theorem shimAst_tags (tys : List CoreFuncTy) : (shimAst tys).tags = [] := rfl
theorem shimAst_globals (tys : List CoreFuncTy) : (shimAst tys).globals = [] := rfl
theorem shimAst_data (tys : List CoreFuncTy) : (shimAst tys).data = [] := rfl
theorem shimAst_elems (tys : List CoreFuncTy) : (shimAst tys).elems = [] := rfl
theorem shimAst_start (tys : List CoreFuncTy) : (shimAst tys).start = none := rfl

/-- What a successful `CMod.encode` of the shim consists of. -/
theorem shim_bytes {tys : List CoreFuncTy} {b : ByteArray}
    (h : CMod.encode (New.shimMod tys) = some b) :
    ∃ ty fn l tb ex cd, CMod.vecSec 1 CMod.funcType tys = some ty ∧
      CMod.vecSec 3 (fun f => u32 f.1) (shimFuncsC tys) = some fn ∧
      CMod.limits tys.length tys.length = some l ∧ CMod.section_ 0x04 (0x01 :: 0x70 :: l) = some tb ∧
      CMod.vecSec 7 CMod.export_ (shimExportsC tys.length) = some ex ∧
      CMod.vecSec 10 CMod.code (shimFuncsC tys) = some cd ∧
      b.data.toList = [0, 97, 115, 109, 1, 0, 0, 0] ++ ty ++ fn ++ tb ++ ex ++ cd := by
  obtain ⟨ty, hty, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨im, him, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨fn, hfn, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨l, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tb, htb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ex, hex, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨el, hel, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨cd, hcd, h⟩ := Option.bind_eq_some_iff.mp h
  have hb : b.data.toList = [0, 97, 115, 109, 1, 0, 0, 0] ++ ty ++ im ++ fn ++ tb ++ ex ++ st ++
      el ++ cd := by rw [← Option.some.inj h]
  have hz : im = [] ∧ st = [] ∧ el = [] :=
    ⟨(Option.some.inj him).symm, (Option.some.inj hst).symm, (Option.some.inj hel).symm⟩
  refine ⟨ty, fn, l, tb, ex, cd, hty, hfn, hl, htb, hex, hcd, ?_⟩
  rw [hb, hz.1, hz.2.1, hz.2.2]
  simp only [List.append_nil]

theorem shim_guard' (tys : List CoreFuncTy) :
    ((true && !(shimAst tys).data.isEmpty) || (Binary.Core.codesDataIdxs
      ((shimAst tys).funcs.map fun f => (f.locals, f.body))).isEmpty) = true := by
  rw [Bool.or_eq_true]; exact Or.inr (shim_guard tys)

/-- **The shim's bytes are silmaril's encoding of `shimAst tys`.** -/
theorem shim_encode {tys : List CoreFuncTy} (hn : tys.length < 2 ^ 31)
    (hp : ∀ t ∈ tys, t.params.length ≤ 2 ^ 32) {b : ByteArray}
    (h : CMod.encode (New.shimMod tys) = some b) :
    encodeModule? (shimAst tys) = .ok b.data.toList := by
  have hn32 : tys.length < 2 ^ 32 := Nat.lt_trans hn (by decide)
  obtain ⟨ty, fn, l, tb, ex, cd, hty, hfn, hl, htb, hex, hcd, hb⟩ := shim_bytes h
  obtain ⟨v1, hv1, hs1⟩ := vecSec_ok (types_rel tys) hty
  obtain ⟨v3, hv3, hs3⟩ := vecSec_ok (funcs_rel hn32) hfn
  obtain ⟨v4, hv4, hs4⟩ := table_ok hn32 hl htb
  obtain ⟨v7, hv7, hs7⟩ := vecSec_ok (exports_rel hn32) hex
  obtain ⟨v10, hv10, hs10⟩ := vecSec_ok (codes_rel hn hp) hcd
  have he : encodeModule? (shimAst tys) = .ok (header ++ ty ++ [] ++ fn ++ tb ++ [] ++ [] ++ [] ++
      ex ++ [] ++ [] ++ [] ++ cd ++ []) :=
    encodeModule?_eq (shim_guard' tys) hv1 (encVec_nil encImport) hv3 (encVec_nil encMemory)
      (encVec_nil _) (encVec_nil encGlobal) hv7 hv10 (encVec_nil encData)
      (encU32_of_lt (show ([] : List Data).length < 2 ^ 32 by decide)) hv4 (encVec_nil encElem)
      hs1 (encSection_zero _ _) hs3 hs4 (encSection_zero _ _) (encSection_zero _ _)
      (encSection_zero _ _) hs7 (encSection_zero _ _) (encSection_zero _ _) (encSection_zero _ _)
      hs10 (encSection_zero _ _)
  rw [he, hb]
  simp only [header, List.append_assoc, List.append_nil, List.nil_append, List.cons_append]

end Silmaril.Wasm.JcoTool.HelpersEnc
