module

public import Silmaril.Wasm.Tools.Gen.Typed.Defs
public import Silmaril.Wasm.Models.Syntax.Thms
public import Silmaril.Wasm.Models.Features.Thms
public import Silmaril.Wasm.Models.Lime1Core.Thms

/-!
# The typed generator is valid by construction: proofs

* `te_typed`, `ts_typed`, `ta_typed`: the erasure of a typed term is well typed in Lime1
  (`ExprType C e.erase [] [t]`, `[] []`, `[] ts`), by one structural induction over the mutual
  family; each constructor is one typing rule of `Silmaril.Wasm.Lime1.Validation`;
* `module_valid`: the Lime1 module of a skeleton and its code is `Lime1.Validation.ModuleValid`;
* `te_inFeat`, `ts_inFeat`, `ta_inFeat` and `module_inFeat`: for `v10 ≤ S`, the Core image of
  the erasure is in `S` (each MVP instruction is in `v10`; sign extension, saturating
  conversions and `memory.fill`/`copy` carry their capability; several results only with
  multi-value).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Tools.Gen.Typed

open Silmaril.Wasm Silmaril.Wasm.Lime1.Validation Silmaril.Wasm.Models
open Silmaril.Wasm.Tools.Gen.Typed

variable {S : FeatureSet} {C : Context}

/-! ## Typing -/

theorem one {i : Lime1.Instr} {a b : V1.ResultType} (h : InstrType C i a b) :
    ExprType C [i] a b := ExprType.singleton h

theorem cat {e₁ e₂ : Lime1.Expr} {a b : V1.ResultType} (h₁ : ExprType C e₁ [] a)
    (h₂ : ExprType C e₂ [] b) : ExprType C (e₁ ++ e₂) [] (a ++ b) :=
  h₁.append (by simpa using h₂.frame a)

theorem un {e : Lime1.Expr} {i : Lime1.Instr} {u : VT} {v : V1.ResultType}
    (he : ExprType C e [] [u]) (hi : InstrType C i [u] v) : ExprType C (e ++ [i]) [] v :=
  he.append (one hi)

theorem bin {e₁ e₂ : Lime1.Expr} {i : Lime1.Instr} {u w : VT} {v : V1.ResultType}
    (h₁ : ExprType C e₁ [] [u]) (h₂ : ExprType C e₂ [] [w]) (hi : InstrType C i [u, w] v) :
    ExprType C (e₁ ++ e₂ ++ [i]) [] v :=
  (cat h₁ h₂).append (one hi)

theorem tern {e₁ e₂ e₃ : Lime1.Expr} {i : Lime1.Instr} {u w x : VT} {v : V1.ResultType}
    (h₁ : ExprType C e₁ [] [u]) (h₂ : ExprType C e₂ [] [w]) (h₃ : ExprType C e₃ [] [x])
    (hi : InstrType C i [u, w, x] v) : ExprType C (e₁ ++ e₂ ++ e₃ ++ [i]) [] v :=
  (cat (cat h₁ h₂) h₃).append (one hi)

theorem callT {e : Lime1.Expr} {x : FuncIdx} {ft : V1.FuncType} {rs : V1.ResultType}
    (ha : ExprType C e [] ft.params) (h : C.funcs[x.toNat]? = some ft) (hr : ft.results = rs) :
    ExprType C (e ++ [.call x]) [] rs :=
  hr ▸ ha.append (one (.call x h))

mutual

/-- **Typed expressions erase to well-typed code.** -/
theorem te_typed : {C : Context} → {t : VT} → (e : TE S C t) → ExprType C e.erase [] [t]
  | _, _, .iconst t b => one (.intConst t b)
  | _, _, .fconst t b => one (.floatConst t b)
  | _, _, .get x h => one (.localGet x h)
  | _, _, .gget x _ h => one (.globalGet x h)
  | _, _, .ibin t op a b => bin (te_typed a) (te_typed b) (.intBinOp t op)
  | _, _, .iun t op v _ a => un (te_typed a) (.intUnOp t op v)
  | _, _, .itest t op a => un (te_typed a) (.intTestOp t op)
  | _, _, .irel t op a b => bin (te_typed a) (te_typed b) (.intRelOp t op)
  | _, _, .fbin t op a b => bin (te_typed a) (te_typed b) (.floatBinOp t op)
  | _, _, .fun_ t op a => un (te_typed a) (.floatUnOp t op)
  | _, _, .frel t op a b => bin (te_typed a) (te_typed b) (.floatRelOp t op)
  | _, _, .cvt op _ a => un (te_typed a) (.convert op)
  | _, _, .load t p arg hm acc a => un (te_typed a) (.intLoad t p arg hm acc)
  | _, _, .fload t arg hm al a => un (te_typed a) (.floatLoad t arg hm al)
  | _, _, .msize hm => one (.memorySize hm)
  | _, _, .mgrow hm a => un (te_typed a) (.memoryGrow hm)
  | _, _, .call _ _ h hr args => callT (ta_typed args) h hr
  | _, _, .select a b c => tern (te_typed a) (te_typed b) (te_typed c) (.select _)
  | _, _, .block s v => one (.block (.value _) rfl ((ts_typed s).append (te_typed v)))
  | _, _, .ite c a b => un (te_typed c) (.if_ (.value _) rfl (te_typed a) (te_typed b))
  | _, _, .tee x h a => un (te_typed a) (.localTee x h)

/-- **Typed statements erase to well-typed code with no stack effect.** -/
theorem ts_typed : {C : Context} → (s : TS S C) → ExprType C s.erase [] []
  | _, .nop => one .nop
  | _, .drop a => un (te_typed a) (.drop _)
  | _, .set x h a => un (te_typed a) (.localSet x h)
  | _, .gset x h a => un (te_typed a) (.globalSet x h)
  | _, .store t p arg hm acc a v => bin (te_typed a) (te_typed v) (.intStore t p arg hm acc)
  | _, .fstore t arg hm al a v => bin (te_typed a) (te_typed v) (.floatStore t arg hm al)
  | _, .fill hm _ a b c => tern (te_typed a) (te_typed b) (te_typed c) (.memoryFill hm)
  | _, .copy hm _ a b c => tern (te_typed a) (te_typed b) (te_typed c) (.memoryCopy hm)
  | _, .block s => one (.block .empty rfl (ts_typed s))
  | _, .loop s => one (.loop .empty rfl (ts_typed s))
  | _, .ite c a b => un (te_typed c) (.if_ .empty rfl (ts_typed a) (ts_typed b))
  | _, .brIf l h c => un (te_typed c) (.brIf l h)
  | _, .call _ _ h hr args => callT (ta_typed args) h hr
  | _, .seq a b => (ts_typed a).append (ts_typed b)

/-- **Typed argument lists erase to code pushing their types.** -/
theorem ta_typed : {C : Context} → {ts : List VT} → (a : TA S C ts) → ExprType C a.erase [] ts
  | _, _, .nil => .nil []
  | _, _, .cons a r => cat (te_typed a) (ta_typed r)

end

/-! ## Modules -/

theorem bodies_types {C0 : Context} : ∀ {l : List (TypeIdx × V1.FuncType)} (bs : Bodies S C0 l),
    bs.funcs.map Declaration.Func.type = l.map Prod.fst
  | [], .nil => rfl
  | (_, _) :: _, .cons _ r => by
    simp only [Bodies.funcs, List.map_cons, bodies_types r]

theorem bodies_mem {C0 : Context} : ∀ {l : List (TypeIdx × V1.FuncType)} (bs : Bodies S C0 l)
    {f : Lime1.Func}, f ∈ bs.funcs →
    ∃ x ft, (x, ft) ∈ l ∧ ∃ b : FBody S C0 ft, f = ⟨x, b.locals, b.stmts.erase ++ b.rets.erase⟩
  | [], .nil, _, h => absurd h List.not_mem_nil
  | (x, ft) :: _, .cons b r, f, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact ⟨x, ft, List.mem_cons_self, b, rfl⟩
    · obtain ⟨y, gt, hm, c, hc⟩ := bodies_mem r h'
      exact ⟨y, gt, List.mem_cons_of_mem _ hm, c, hc⟩

/-- The functions of the context are those of the module, by type index. -/
theorem funcs_filterMap (types : List V1.FuncType) (fs : List Lime1.Func) :
    fs.filterMap (fun f => types[f.type.toNat]?) =
      (fs.map Declaration.Func.type).filterMap (fun x => types[x.toNat]?) := by
  rw [List.filterMap_map]
  rfl

/-- **The context of the module is the skeleton's**: only the code differs. -/
theorem ctx_module (k : Skel S) (bs : Bodies S k.ctx k.funcs) (d : Option (Nat × List UInt8)) :
    moduleContext (k.module bs d) = k.ctx := by
  have e₁ : (bs.funcs.map Declaration.Func.type) =
      ((k.funcs.map fun p => (⟨p.1, [], []⟩ : Lime1.Func)).map Declaration.Func.type) := by
    rw [bodies_types, List.map_map]
    rfl
  have e₂ : bs.funcs.filterMap (fun f => k.types[f.type.toNat]?) =
      (k.funcs.map fun p => (⟨p.1, [], []⟩ : Lime1.Func)).filterMap
        (fun f => k.types[f.type.toNat]?) := by
    rw [funcs_filterMap, funcs_filterMap, e₁]
  unfold Skel.ctx moduleContext
  simp only [Skel.module, Skel.module0]
  rw [e₂]
  rfl

/-- Every resolved function appears in the context, in order. -/
theorem ctx_funcs (k : Skel S) : k.ctx.funcs = k.funcs.map Prod.snd := by
  have h : ∀ l : List (TypeIdx × V1.FuncType), (∀ p ∈ l, k.types[p.1.toNat]? = some p.2) →
      (l.map fun p => (⟨p.1, [], []⟩ : Lime1.Func)).filterMap
        (fun f => k.types[f.type.toNat]?) = l.map Prod.snd := by
    intro l hl
    induction l with
    | nil => rfl
    | cons p l ih =>
      have hp : k.types[p.1.toNat]? = some p.2 := hl p List.mem_cons_self
      have ht : (List.map Prod.snd (p :: l)) = p.2 :: l.map Prod.snd := rfl
      rw [ht, ← ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))]
      simp only [List.map_cons, List.filterMap_cons, hp]
  unfold Skel.ctx moduleContext
  simp only [Skel.module0, List.filterMap_nil, List.nil_append]
  exact h k.funcs k.resolved

theorem global_valid (C : Context) (t : VT) (m : Bool) (b : Nat) : GlobalValid C (global t m b) := by
  cases t with
  | int it =>
    refine ⟨one (.intConst _ _), fun i hi => ?_⟩
    rw [List.mem_singleton.mp hi]
    exact .intConst _ _
  | float ft =>
    refine ⟨one (.floatConst _ _), fun i hi => ?_⟩
    rw [List.mem_singleton.mp hi]
    exact .floatConst _ _

theorem memory_valid : MemoryTypeValid (⟨⟨Fin.ofNat _ 1, some (Fin.ofNat _ 4)⟩⟩ : V1.MemoryType) := by
  refine ⟨by decide, fun mx hmx => ?_⟩
  rw [Option.mem_def, Option.some_inj] at hmx
  rw [← hmx]
  exact ⟨by decide, by decide⟩

theorem exportNames_nodup : exportNames.Nodup := by decide

/-- **The Lime1 module of a skeleton and its code is valid.** -/
theorem module_valid (k : Skel S) (bs : Bodies S k.ctx k.funcs) (d : Option (Nat × List UInt8)) :
    ModuleValid (k.module bs d) where
  types _ _ := trivial
  imports _ h := absurd h List.not_mem_nil
  functions f hf := by
    show FuncValid (moduleContext (k.module bs d)) f
    rw [ctx_module]
    obtain ⟨x, ft, hmem, b, rfl⟩ := bodies_mem bs hf
    exact ⟨ft, k.resolved _ hmem, trivial, (ts_typed b.stmts).append (ta_typed b.rets)⟩
  tables _ h := absurd h List.not_mem_nil
  memories mt h := by
    show MemoryTypeValid mt
    have hm : mt ∈ k.memories := h
    unfold Skel.memories at hm
    split at hm
    · rw [List.mem_singleton.mp hm]; exact memory_valid
    · exact absurd hm List.not_mem_nil
  globals g h := by
    show GlobalValid _ g
    obtain ⟨⟨t, m, b⟩, -, rfl⟩ := List.mem_map.mp h
    exact global_valid _ t m b
  elements _ h := absurd h List.not_mem_nil
  data dd h := by
    show DataValid _ dd
    have hdat : dd ∈ (match d with
      | some (off, bytes) => if k.mem then
          [(⟨⟨0⟩, [.intConst .i32 (BitVec.ofNat _ off)], ⟨bytes.toArray⟩⟩ : Lime1.Data)] else []
      | none => []) := h
    split at hdat
    · split at hdat
      · next hmem =>
        rw [List.mem_singleton.mp hdat, ctx_module]
        refine ⟨⟨⟨⟨Fin.ofNat _ 1, some (Fin.ofNat _ 4)⟩⟩, ?_⟩, one (.intConst _ _),
          fun i hi => ?_⟩
        · show k.memories[0]? = some _
          simp only [Skel.memories, hmem, ite_true, List.getElem?_cons_zero]
        · rw [List.mem_singleton.mp hi]; exact .intConst _ _
      · exact absurd hdat List.not_mem_nil
    · exact absurd hdat List.not_mem_nil
  start _ h := absurd h (by simp [Skel.module, Skel.module0])
  exports e h := by
    show ExportValid _ e
    obtain ⟨⟨n, i⟩, hi, rfl⟩ := List.mem_map.mp h
    have hlt : i < (exportNames.take k.funcs.length).length := by
      simpa using List.snd_lt_of_mem_zipIdx hi
    have hlen : (exportNames.take k.funcs.length).length ≤ k.funcs.length ∧
        (exportNames.take k.funcs.length).length ≤ 10 := by
      simp [exportNames]
    have hi' : (idx i : FuncIdx).toNat = i := by
      show i % 2 ^ 32 = i
      exact Nat.mod_eq_of_lt (by omega)
    rw [ctx_module]
    have hk : i < k.funcs.length := by omega
    show ∃ et, exportType? k.ctx (.func (idx i)) = some et
    refine ⟨.func (k.funcs[i]'hk).2, ?_⟩
    show (k.ctx.funcs[(idx i : FuncIdx).toNat]?).map V1.ExternType.func = some _
    rw [hi', ctx_funcs, List.getElem?_map, List.getElem?_eq_getElem hk]
    rfl
  uniqueExports := by
    show (((exportNames.take k.funcs.length).zipIdx.map fun p =>
      (⟨p.1, .func (idx p.2)⟩ : V1.Export)).map V1.Export.name).Nodup
    rw [List.map_map]
    have : ((exportNames.take k.funcs.length).zipIdx.map fun p => p.1) =
        exportNames.take k.funcs.length := List.zipIdx_map_fst 0 _
    rw [show (V1.Export.name ∘ fun p : String × Nat => (⟨p.1, .func (idx p.2)⟩ : V1.Export)) =
      fun p => p.1 from rfl, this]
    exact exportNames_nodup.sublist (List.take_sublist _ _)
  singleTable := by simp [moduleContext, Skel.module, Skel.module0]
  singleMemory := by
    simp only [moduleContext, Skel.module, Skel.module0, Skel.memories]
    split <;> simp

/-! ## Inside the feature set -/

/-- The MVP capabilities a set `S ≥ v10` has. -/
structure Mvp (S : FeatureSet) : Prop where
  i : S.has .intNum = true
  f : S.has .floatNum = true
  c : S.has .control = true
  d : S.has .directCall = true
  m : S.has .memory = true
  g : S.has .globals = true
  mg : S.has .mutGlobal = true

theorem mvp_of (h : v10 ≤ S) : Mvp S :=
  ⟨has_of_le h (by decide), has_of_le h (by decide), has_of_le h (by decide),
    has_of_le h (by decide), has_of_le h (by decide), has_of_le h (by decide),
    has_of_le h (by decide)⟩

/-- Every instruction of a Lime1 sequence has its Core image in `S`. -/
def Ok (S : FeatureSet) (e : Lime1.Expr) : Prop :=
  ∀ i ∈ e, Instr.inFeatB S (Lime1.Instr.toCore i) = true

theorem ok_app {a b : Lime1.Expr} (ha : Ok S a) (hb : Ok S b) : Ok S (a ++ b) := fun i hi =>
  (List.mem_append.mp hi).elim (ha i) (hb i)

theorem ok_one {i : Lime1.Instr} (h : Instr.inFeatB S (Lime1.Instr.toCore i) = true) :
    Ok S [i] := fun _ hj => (List.mem_singleton.mp hj) ▸ h

theorem ok_nil : Ok S [] := fun _ h => absurd h List.not_mem_nil

/-- The Core image of an `Ok` sequence is in `S`. -/
theorem ins_of_ok : (e : Lime1.Expr) → Ok S e → Instr.insInFeatB S (Lime1.Expr.toCore e) = true
  | [], _ => rfl
  | i :: e, h => by
    have h₁ : Instr.inFeatB S (Lime1.Instr.toCore i) = true := h i List.mem_cons_self
    have h₂ : Instr.insInFeatB S (Lime1.Expr.toCore e) = true :=
      ins_of_ok e (fun j hj => h j (List.mem_cons_of_mem _ hj))
    simp only [Lime1.Expr.toCore, Instr.insInFeatB, h₁, h₂, Bool.and_self]

theorem valType_ok (hM : Mvp S) (t : VT) : ValType.inFeatB S (V1.ValType.toCore t) = true := by
  cases t <;> simp [V1.ValType.toCore, ValType.inFeatB, hM.i, hM.f]

theorem blockValue_ok (hM : Mvp S) (t : VT) :
    BlockType.inFeatB S (Lime1.BlockType.value t).toCore = true := by
  cases t <;> simp [Lime1.BlockType.toCore, BlockType.inFeatB, ValType.inFeatB, hM.i, hM.f]

theorem block_ok (hM : Mvp S) (bt : Lime1.BlockType)
    (hbt : BlockType.inFeatB S bt.toCore = true) {b : Lime1.Expr} (hb : Ok S b) :
    Ok S [.block bt b] := ok_one (by
  simp [Lime1.Instr.toCore, Instr.inFeatB, Instr.headB, hM.c, hbt, ins_of_ok b hb])

theorem loop_ok (hM : Mvp S) {b : Lime1.Expr} (hb : Ok S b) : Ok S [.loop .empty b] :=
  ok_one (by
    simp [Lime1.Instr.toCore, Instr.inFeatB, Instr.headB, hM.c, Lime1.BlockType.toCore,
      BlockType.inFeatB, ins_of_ok b hb])

theorem if_ok (hM : Mvp S) (bt : Lime1.BlockType) (hbt : BlockType.inFeatB S bt.toCore = true)
    {a b : Lime1.Expr} (ha : Ok S a) (hb : Ok S b) : Ok S [.if_ bt a b] := ok_one (by
  simp [Lime1.Instr.toCore, Instr.inFeatB, Instr.headB, hM.c, hbt, ins_of_ok a ha, ins_of_ok b hb])

theorem empty_ok : BlockType.inFeatB S (Lime1.BlockType.empty).toCore = true := rfl

/-- The plain instructions: one capability of the MVP each. -/
theorem plain_ok {i : Lime1.Instr} (hi : i.bodies = [])
    (h : Instr.headB S (Lime1.Instr.toCore i) = true) : Ok S [i] :=
  ok_one (by cases i <;> simp_all [Lime1.Instr.toCore, Instr.inFeatB, Lime1.Instr.bodies])

@[simp] theorem memIdx0 : (⟨0⟩ : MemIdx).toNat = 0 := rfl

macro "mvp_simp" hM:term : tactic =>
  `(tactic| simp [Lime1.Instr.toCore, Instr.headB, memIdxB, memIdx0, ($hM).i, ($hM).f, ($hM).c,
    ($hM).d, ($hM).m, ($hM).g, ($hM).mg])

mutual

/-- **The erasure of an expression is in `S`.** -/
theorem te_ok (hM : Mvp S) : {C : Context} → {t : VT} → (e : TE S C t) → Ok S e.erase
  | _, _, .iconst _ _ => plain_ok rfl (by mvp_simp hM)
  | _, _, .fconst _ _ => plain_ok rfl (by mvp_simp hM)
  | _, _, .get _ _ => plain_ok rfl (by mvp_simp hM)
  | _, _, .gget _ _ _ => plain_ok rfl (by mvp_simp hM)
  | _, _, .ibin _ _ a b => ok_app (ok_app (te_ok hM a) (te_ok hM b)) (plain_ok rfl (by mvp_simp hM))
  | _, _, .iun _ _ _ hf a => ok_app (te_ok hM a) (plain_ok rfl (by simpa [Lime1.Instr.toCore, Instr.headB] using hf))
  | _, _, .itest _ _ a => ok_app (te_ok hM a) (plain_ok rfl (by mvp_simp hM))
  | _, _, .irel _ _ a b => ok_app (ok_app (te_ok hM a) (te_ok hM b)) (plain_ok rfl (by mvp_simp hM))
  | _, _, .fbin _ _ a b => ok_app (ok_app (te_ok hM a) (te_ok hM b)) (plain_ok rfl (by mvp_simp hM))
  | _, _, .fun_ _ _ a => ok_app (te_ok hM a) (plain_ok rfl (by mvp_simp hM))
  | _, _, .frel _ _ a b => ok_app (ok_app (te_ok hM a) (te_ok hM b)) (plain_ok rfl (by mvp_simp hM))
  | _, _, .cvt _ hf a => ok_app (te_ok hM a) (plain_ok rfl (by simpa [Lime1.Instr.toCore, Instr.headB] using hf))
  | _, _, .load _ _ _ _ _ a => ok_app (te_ok hM a) (plain_ok rfl (by mvp_simp hM))
  | _, _, .fload _ _ _ _ a => ok_app (te_ok hM a) (plain_ok rfl (by mvp_simp hM))
  | _, _, .msize _ => plain_ok rfl (by mvp_simp hM)
  | _, _, .mgrow _ a => ok_app (te_ok hM a) (plain_ok rfl (by mvp_simp hM))
  | _, _, .call _ _ _ _ args => ok_app (ta_ok hM args) (plain_ok rfl (by mvp_simp hM))
  | _, _, .select a b c =>
    ok_app (ok_app (ok_app (te_ok hM a) (te_ok hM b)) (te_ok hM c)) (plain_ok rfl (by mvp_simp hM))
  | _, t, .block s v => block_ok hM _ (blockValue_ok hM t) (ok_app (ts_ok hM s) (te_ok hM v))
  | _, t, .ite c a b => ok_app (te_ok hM c) (if_ok hM _ (blockValue_ok hM t) (te_ok hM a) (te_ok hM b))
  | _, _, .tee _ _ a => ok_app (te_ok hM a) (plain_ok rfl (by mvp_simp hM))

/-- **The erasure of a statement is in `S`.** -/
theorem ts_ok (hM : Mvp S) : {C : Context} → (s : TS S C) → Ok S s.erase
  | _, .nop => plain_ok rfl (by mvp_simp hM)
  | _, .drop a => ok_app (te_ok hM a) (plain_ok rfl (by mvp_simp hM))
  | _, .set _ _ a => ok_app (te_ok hM a) (plain_ok rfl (by mvp_simp hM))
  | _, .gset _ _ a => ok_app (te_ok hM a) (plain_ok rfl (by mvp_simp hM))
  | _, .store _ _ _ _ _ a v => ok_app (ok_app (te_ok hM a) (te_ok hM v)) (plain_ok rfl (by mvp_simp hM))
  | _, .fstore _ _ _ _ a v => ok_app (ok_app (te_ok hM a) (te_ok hM v)) (plain_ok rfl (by mvp_simp hM))
  | _, .fill _ hf a b c => ok_app (ok_app (ok_app (te_ok hM a) (te_ok hM b)) (te_ok hM c))
      (plain_ok rfl (by simp [Lime1.Instr.toCore, Instr.headB, memIdxB, memIdx0, hf, hM.i, hM.m]))
  | _, .copy _ hf a b c => ok_app (ok_app (ok_app (te_ok hM a) (te_ok hM b)) (te_ok hM c))
      (plain_ok rfl (by simp [Lime1.Instr.toCore, Instr.headB, memIdxB, memIdx0, hf, hM.i, hM.m]))
  | _, .block s => block_ok hM _ empty_ok (ts_ok hM s)
  | _, .loop s => loop_ok hM (ts_ok hM s)
  | _, .ite c a b => ok_app (te_ok hM c) (if_ok hM _ empty_ok (ts_ok hM a) (ts_ok hM b))
  | _, .brIf _ _ c => ok_app (te_ok hM c) (plain_ok rfl (by mvp_simp hM))
  | _, .call _ _ _ _ args => ok_app (ta_ok hM args) (plain_ok rfl (by mvp_simp hM))
  | _, .seq a b => ok_app (ts_ok hM a) (ts_ok hM b)

/-- **The erasure of an argument list is in `S`.** -/
theorem ta_ok (hM : Mvp S) : {C : Context} → {ts : List VT} → (a : TA S C ts) → Ok S a.erase
  | _, _, .nil => ok_nil
  | _, _, .cons a r => ok_app (te_ok hM a) (ta_ok hM r)

end

/-! ## The module -/

theorem recType_ok (hM : Mvp S) {ft : V1.FuncType} (h : FuncTypeOk S ft = true) :
    RecType.inFeatB S ft.toCoreRec = true := by
  simp only [FuncTypeOk] at h
  simp [RecType.inFeatB, SubType.inFeatB, FuncType.inFeatB, V1.FuncType.toCoreRec,
    V1.FuncType.toCore, h]
  exact ⟨fun t _ => valType_ok hM t, fun t _ => valType_ok hM t⟩

theorem constInt_ok (hM : Mvp S) (it : IntType) (x : BitVec it.width) :
    constExprB S [Instr.intConst it x] = true := by
  have h : Instr.insInFeatB S [Instr.intConst it x] = true := by
    show (S.has .intNum && true) = true
    rw [hM.i]; rfl
  show (Instr.insInFeatB S [Instr.intConst it x] &&
    (simpleConst [Instr.intConst it x] || S.has .extConst)) = true
  rw [h]; rfl

theorem constFloat_ok (hM : Mvp S) (ft : FloatType) (x : BitVec ft.width) :
    constExprB S [Instr.floatConst ft x] = true := by
  have h : Instr.insInFeatB S [Instr.floatConst ft x] = true := by
    show (S.has .floatNum && true) = true
    rw [hM.f]; rfl
  show (Instr.insInFeatB S [Instr.floatConst ft x] &&
    (simpleConst [Instr.floatConst ft x] || S.has .extConst)) = true
  rw [h]; rfl

theorem globalType_ok (hM : Mvp S) (mu : Mutability) (t : VT) :
    GlobalType.inFeatB S (V1.GlobalType.toCore ⟨mu, t⟩) = true := by
  have hv : ValType.inFeatB S (V1.ValType.toCore t) = true := valType_ok hM t
  simp only [GlobalType.inFeatB, V1.GlobalType.toCore, hM.g, hM.mg, hv, Bool.or_true,
    Bool.and_self]

theorem global_ok (hM : Mvp S) (t : VT) (m : Bool) (b : Nat) :
    Global.inFeatB S (Lime1.Global.toCore (global t m b)) = true := by
  have hty : GlobalType.inFeatB S (Lime1.Global.toCore (global t m b)).type = true :=
    globalType_ok hM (if m then .var else .const) t
  have hc : constExprB S (Lime1.Global.toCore (global t m b)).init = true := by
    cases t with
    | int it => exact constInt_ok hM it _
    | float ft => exact constFloat_ok hM ft _
  simp only [Global.inFeatB, hty, hc, Bool.and_self]

theorem func_ok (hM : Mvp S) {C0 : Context} {l : List (TypeIdx × V1.FuncType)}
    (bs : Bodies S C0 l) {f : Lime1.Func} (hf : f ∈ bs.funcs) :
    Func.inFeatB S (Lime1.Func.toCore f) = true := by
  obtain ⟨x, ft, -, b, rfl⟩ := bodies_mem bs hf
  have hb : Instr.insInFeatB S (Lime1.Expr.toCore (b.stmts.erase ++ b.rets.erase)) = true :=
    ins_of_ok _ (ok_app (ts_ok hM b.stmts) (ta_ok hM b.rets))
  simp [Func.inFeatB, Lime1.Func.toCore, hb]
  exact fun t _ => valType_ok hM t

theorem memIdx0_ok (hM : Mvp S) : memIdxB S ⟨0⟩ = true := by
  simp only [memIdxB, hM.i, hM.m, memIdx0, beq_self_eq_true, Bool.true_or, Bool.and_self]

/-- **The Core image of the typed generator's module is in `S`.** -/
theorem module_inFeat (hM : Mvp S) (k : Skel S) (bs : Bodies S k.ctx k.funcs)
    (d : Option (Nat × List UInt8)) : Module.InFeat S (Lime1.Module.toCore (k.module bs d)) := by
  have hT : ∀ x ∈ (Lime1.Module.toCore (k.module bs d)).types, RecType.inFeatB S x = true := by
    intro x hx
    obtain ⟨ft, hft, rfl⟩ := List.mem_map.mp hx
    exact recType_ok hM (k.typesOk _ hft)
  have hG : ∀ x ∈ (Lime1.Module.toCore (k.module bs d)).globals, Global.inFeatB S x = true := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    obtain ⟨⟨t, m, b⟩, -, rfl⟩ := List.mem_map.mp hg
    exact global_ok hM t m b
  have hMem : ∀ x ∈ (Lime1.Module.toCore (k.module bs d)).memories,
      MemoryType.inFeatB S x = true := by
    intro x hx
    obtain ⟨mt, -, rfl⟩ := List.mem_map.mp hx
    simp only [MemoryType.inFeatB, V1.MemoryType.toCore, hM.m, beq_self_eq_true, Bool.true_or,
      Bool.and_self]
  have hF : ∀ x ∈ (Lime1.Module.toCore (k.module bs d)).funcs, Func.inFeatB S x = true := by
    intro x hx
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
    exact func_ok hM bs hf
  have hD : ∀ x ∈ (Lime1.Module.toCore (k.module bs d)).data, Data.inFeatB S x = true := by
    intro x hx
    obtain ⟨dd, h, rfl⟩ := List.mem_map.mp hx
    have hdat : dd ∈ (match d with
      | some (off, bytes) => if k.mem then
          [(⟨⟨0⟩, [.intConst .i32 (BitVec.ofNat _ off)], ⟨bytes.toArray⟩⟩ : Lime1.Data)] else []
      | none => []) := h
    split at hdat
    · split at hdat
      · rw [List.mem_singleton.mp hdat]
        show (memIdxB S ⟨0⟩ && constExprB S [Instr.intConst .i32 _]) = true
        rw [memIdx0_ok hM, constInt_ok hM]; rfl
      · exact absurd hdat List.not_mem_nil
    · exact absurd hdat List.not_mem_nil
  have hC : (decide ((Lime1.Module.toCore (k.module bs d)).memories.length +
      ((Lime1.Module.toCore (k.module bs d)).imports.filter Import.isMemory).length ≤ 1) ||
      S.has .multiMemory) = true := by
    have hl : k.memories.length ≤ 1 := by unfold Skel.memories; split <;> simp
    simp only [Lime1.Module.toCore, Skel.module, Skel.module0, List.length_map, List.map_nil,
      List.filter_nil, List.length_nil, Nat.add_zero, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl hl
  have hE : ∀ x ∈ (Lime1.Module.toCore (k.module bs d)).elems, Elem.inFeatB S x = true :=
    fun _ hx => absurd hx List.not_mem_nil
  have hTb : ∀ x ∈ (Lime1.Module.toCore (k.module bs d)).tables, Table.inFeatB S x = true :=
    fun _ hx => absurd hx List.not_mem_nil
  have hI : ∀ x ∈ (Lime1.Module.toCore (k.module bs d)).imports,
      ExternType.inFeatB S x.type = true := fun _ hx => absurd hx List.not_mem_nil
  have hTg : ((Lime1.Module.toCore (k.module bs d)).tags.isEmpty || S.has .exn) = true := rfl
  have hTc : (decide ((Lime1.Module.toCore (k.module bs d)).tables.length +
      ((Lime1.Module.toCore (k.module bs d)).imports.filter Import.isTable).length ≤ 1) ||
      S.has .refTypes) = true := rfl
  unfold Module.InFeat Module.inFeatB
  simp only [Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hT, hI⟩, hTg⟩, hG⟩, hMem⟩, hTb⟩, hF⟩, hE⟩, hD⟩, hC⟩, hTc⟩

/-- **The typed generator's modules are valid in every `S ≥ v10`.** -/
theorem module_validIn (h : v10 ≤ S) (k : Skel S) (bs : Bodies S k.ctx k.funcs)
    (d : Option (Nat × List UInt8)) : ValidIn S (Lime1.Module.toCore (k.module bs d)) :=
  ⟨(Silmaril.Wasm.Models.Lime1Core.validIn_v30 (module_valid k bs d)).1,
    module_inFeat (mvp_of h) k bs d⟩

end Silmaril.Proofs.Wasm.Tools.Gen.Typed
