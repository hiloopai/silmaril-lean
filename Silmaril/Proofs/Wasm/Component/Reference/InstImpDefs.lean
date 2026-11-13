module

public import Silmaril.Proofs.Wasm.Component.Reference.InstImpCore
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Instantiating the import definitions of `SimpleI.toRef`

The definitions that `SimpleI.toRef` emits for its imports (`SimpleI.importsDefs`) run without a
machine operation other than store reads, both in the instantiation (`importsDefs_run`) and in
the import pre-check of the root (`importsDefs_pre`): the type definitions extend the type index
space, and `(import "name" (func (type t)))` with the argument `func k` of the root
(`importArgs`) passes the import type check (`importTypeCheck_func`: the function type at index
`t` is the type of the host function `k`, and the subtype checker is reflexive on function
types, which it compares by equality) and pushes component function `k`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition Syntax.VT Syntax.DefValType)

variable {E : CoreEngine} {σ : Type}

/-! ## The import type check of a function import -/

section Check

theorem openInstanceType_func_self (chk : EntityT E → EntityT E → Except String Unit)
    (nm : String) (t : Types.FuncType RtId) (hchk : chk (.func t) (.func t) = .ok ()) :
    ∃ m, Types.openInstanceType? chk [(nm, .func t)] [] [(nm, .func t)] "import" = .ok m := by
  have hid : ∀ m : Types.Remapping RtId, (Types.Entity.func t : EntityT E).map
      (m.apply []) = .func t := by
    intro m
    have hf : m.apply [] = id := funext fun r => Types.Remapping.apply_of_not_mem m (List.not_mem_nil)
    rw [hf, Types.Entity.map_id]
  refine ⟨Types.inferRemapping (X := E.ExternType) [] [(nm, .func t)] [(nm, .func t)], ?_⟩
  simp only [Types.openInstanceType?, Types.presentEach, Types.checkEach, Types.lookupKey,
    ite_true, hid, hchk, Types.withCtx]

variable [∀ a b, Decidable (E.ExternSub a b)]

theorem entitySub_func_self (t : Types.FuncType RtId) :
    Types.Entity.sub? (xsubCheck (E := E)) (.func t : EntityT E) (.func t) = .ok () := by
  simp only [Types.Entity.sub?, Types.subFuel, Types.entitySubStep, Types.funcSub?, ite_true]

/-- **The import type check of a function import passes** when the function type at the
descriptor's type index is the type of the supplied component function. -/
theorem importTypeCheck_func (s : CStore E) (f : Frame E) (nm : String) {n : Nat} {k : FuncId}
    {t : Types.FuncType RtId} {fi : CFuncInst E} (hf : f.types[n]? = some (.func t))
    (hs : ArenaField.funcs.get? s k = some fi) (ht : fi.ft = t) :
    importTypeCheck s f nm (.func n) (.func k) = .ok () := by
  have hd : descEntity? f 0 (.func n) = some (.func t, [], 0) := by
    simp only [descEntity?, funcTypeAt?, Frame.type?, hf, Option.map_some]
  have hi : itemEntity? s (.func k) = some (.func t) := by
    simp only [itemEntity?, hs, Option.map_some, ht]
  have hp : pruneEntity (.func t : EntityT E) = some (.func t) := rfl
  obtain ⟨m, hm⟩ := openInstanceType_func_self (Types.Entity.sub? (xsubCheck (E := E))) nm t
    (entitySub_func_self t)
  simp only [importTypeCheck, hd, hi, hp, hm]

end Check

/-! ## The import pre-check of type definitions -/

section Pre

variable [∀ a b, Decidable (E.ExternSub a b)] (s : CStore E) (args : Exports E)

/-- The definitions `ds` are pre-checked from `f` to `f'` (whatever follows them), only
appending to the type index space (giving `n'` types). -/
def PreTys (f : Frame E) (ds : List (Syntax.Definition E.Module)) (f' : Frame E) (n' : Nat) :
    Prop :=
  (∀ rest, precheckImports s args f (ds ++ rest) = precheckImports s args f' rest) ∧
    (∃ new, f' = { f with types := f.types ++ new }) ∧ f'.types.length = n'

variable {s args}

theorem PreTys.nil (f : Frame E) : PreTys s args f [] f f.types.length :=
  ⟨fun _ => rfl, ⟨[], by rw [List.append_nil]; cases f; rfl⟩, rfl⟩

theorem PreTys.trans {f f₁ f₂ : Frame E} {ds ds' : List (Syntax.Definition E.Module)}
    {n₁ n₂ : Nat} (h : PreTys s args f ds f₁ n₁) (h' : PreTys s args f₁ ds' f₂ n₂) :
    PreTys s args f (ds ++ ds') f₂ n₂ := by
  obtain ⟨e₁, ⟨new₁, f₁e⟩, -⟩ := h
  obtain ⟨e₂, ⟨new₂, f₂e⟩, l₂⟩ := h'
  refine ⟨fun rest => ?_, ⟨new₁ ++ new₂, ?_⟩, l₂⟩
  · rw [List.append_assoc, e₁, e₂]
  · rw [f₂e, f₁e, List.append_assoc]

theorem PreTys.prefix {f f' : Frame E} {ds : List (Syntax.Definition E.Module)} {n : Nat}
    (h : PreTys s args f ds f' n) : f.types <+: f'.types := by
  obtain ⟨-, ⟨new, hf⟩, -⟩ := h
  rw [hf]
  exact List.prefix_append _ _

theorem PreTys.cast {f f' : Frame E} {ds ds' : List (Syntax.Definition E.Module)} {n n' : Nat}
    (h : PreTys s args f ds f' n) (hd : ds = ds') (hn : n = n') : PreTys s args f ds' f' n' :=
  hd ▸ hn ▸ h

theorem PreTys.single {f f' : Frame E} {d : Syntax.Definition E.Module} {ty}
    (h : precheckDef s args f d = .ok (some f')) (hf : f' = { f with types := f.types ++ [ty] }) :
    PreTys s args f [d] f' (f.types.length + 1) := by
  refine ⟨fun rest => ?_, ⟨[ty], hf⟩, by rw [hf, List.length_append, List.length_singleton]⟩
  simp only [List.singleton_append, precheckImports, h]

theorem PreTys.val (f : Frame E) {d : Syntax.DefValType} {t : WIT.ClosedType RtId}
    (h : resolveDefValType? f d = some t) :
    PreTys s args f [.type (.val d)] { f with types := f.types ++ [.val t] }
      (f.types.length + 1) :=
  PreTys.single (by simp only [precheckDef, staticType?, h, Option.map_some, Option.bind_some,
    Frame.push]) rfl

theorem PreTys.func (f : Frame E) {ft : Syntax.FuncType} {t : Types.FuncType RtId}
    (h : resolveFuncType? f ft = some t) :
    PreTys s args f [.type (.func ft)] { f with types := f.types ++ [.func t] }
      (f.types.length + 1) :=
  PreTys.single (by simp only [precheckDef, staticType?, h, Option.map_some, Option.bind_some,
    Frame.push]) rfl

theorem PreTys.tyExport (f : Frame E) {n : Nat} {ty : Types.TypeDef RtId E.ExternType}
    (h : f.types[n]? = some ty) :
    PreTys s args f [typeExport n] { f with types := f.types ++ [ty] } (f.types.length + 1) :=
  PreTys.single (by simp only [precheckDef, typeExport, typeRelevant, ite_true, Frame.get?,
    Frame.type?, h, Option.map_some, Option.bind_some, Function.comp_apply, Frame.push]) rfl

/-- A value type definition followed by its type export. -/
theorem PreTys.valExport (f : Frame E) {d : Syntax.DefValType} {t : WIT.ClosedType RtId}
    (h : resolveDefValType? f d = some t) :
    ∃ f', PreTys s args f [.type (.val d), typeExport f.types.length] f'
        (f.types.length + 2) ∧ Res f'.types (.idx (f.types.length + 1)) t := by
  have h₁ := PreTys.val (s := s) (args := args) f h
  have hl : (f.types ++ [.val t])[f.types.length]? = some (.val t) := by simp
  have h₂ := PreTys.tyExport (s := s) (args := args) { f with types := f.types ++ [.val t] } hl
  refine ⟨_, (h₁.trans h₂).cast rfl (by simp), Res.idx ?_⟩
  simp

mutual
/-- **The type definitions emitted for an IR type pass the pre-check**, extending the type
index space as in the instantiation, and the emitted value type resolves to `toClosed t`. -/
theorem emitTy_pre : ∀ (t : ValTy) (f : Frame E),
    ∃ f', PreTys s args f (emitTy (M := E.Module) t f.types.length).2.1 f'
        (emitTy (M := E.Module) t f.types.length).2.2 ∧
      Res f'.types (emitTy (M := E.Module) t f.types.length).1 (toClosed t)
  | .bool, f => ⟨f, PreTys.nil f, Res.prim _ .bool⟩
  | .s8, f => ⟨f, PreTys.nil f, Res.prim _ .s8⟩
  | .u8, f => ⟨f, PreTys.nil f, Res.prim _ .u8⟩
  | .s16, f => ⟨f, PreTys.nil f, Res.prim _ .s16⟩
  | .u16, f => ⟨f, PreTys.nil f, Res.prim _ .u16⟩
  | .s32, f => ⟨f, PreTys.nil f, Res.prim _ .s32⟩
  | .u32, f => ⟨f, PreTys.nil f, Res.prim _ .u32⟩
  | .s64, f => ⟨f, PreTys.nil f, Res.prim _ .s64⟩
  | .u64, f => ⟨f, PreTys.nil f, Res.prim _ .u64⟩
  | .f32, f => ⟨f, PreTys.nil f, Res.prim _ .f32⟩
  | .f64, f => ⟨f, PreTys.nil f, Res.prim _ .f64⟩
  | .char, f => ⟨f, PreTys.nil f, Res.prim _ .char⟩
  | .record ts, f => by
    obtain ⟨f₁, hP₁, hR₁⟩ := emitTys_pre ts f
    have hl₁ : f₁.types.length = (emitTys (M := E.Module) ts f.types.length).2.2 := hP₁.2.2
    have hrec : resolveDefValType? f₁
        (.record (labels "f" (emitTys (M := E.Module) ts f.types.length).1)) =
          some (toClosed (.record ts)) :=
      resolve_record hR₁ _ (List.prefix_refl _)
    obtain ⟨f₂, hP₂, hR₂⟩ := PreTys.valExport (s := s) (args := args) f₁ hrec
    rw [emitTy_record, ← hl₁]
    exact ⟨f₂, hP₁.trans hP₂, hR₂⟩
  | .variant cs, f => by
    obtain ⟨f₁, hP₁, hR₁⟩ := emitCases_pre cs f
    have hl₁ : f₁.types.length = (emitCases (M := E.Module) cs f.types.length).2.2 := hP₁.2.2
    have hvar : resolveDefValType? f₁
        (.variant (labels "c" (emitCases (M := E.Module) cs f.types.length).1)) =
          some (toClosed (.variant cs)) :=
      resolve_variant hR₁ _ (List.prefix_refl _)
    obtain ⟨f₂, hP₂, hR₂⟩ := PreTys.valExport (s := s) (args := args) f₁ hvar
    rw [emitTy_variant, ← hl₁]
    exact ⟨f₂, hP₁.trans hP₂, hR₂⟩

/-- `emitTy_pre` on lists. -/
theorem emitTys_pre : ∀ (ts : List ValTy) (f : Frame E),
    ∃ f', PreTys s args f (emitTys (M := E.Module) ts f.types.length).2.1 f'
        (emitTys (M := E.Module) ts f.types.length).2.2 ∧
      List.Forall₂ (Res f'.types) (emitTys (M := E.Module) ts f.types.length).1
        (toClosedList ts)
  | [], f => ⟨f, PreTys.nil f, .nil⟩
  | t :: ts, f => by
    obtain ⟨f₁, hP₁, hR₁⟩ := emitTy_pre t f
    obtain ⟨f₂, hP₂, hR₂⟩ := emitTys_pre ts f₁
    have hl₁ : f₁.types.length = (emitTy (M := E.Module) t f.types.length).2.2 := hP₁.2.2
    rw [emitTys_cons, ← hl₁]
    exact ⟨f₂, hP₁.trans hP₂, .cons (hR₁.mono hP₂.prefix) hR₂⟩

/-- `emitTy_pre` on variant cases. -/
theorem emitCases_pre : ∀ (cs : List (Option ValTy)) (f : Frame E),
    ∃ f', PreTys s args f (emitCases (M := E.Module) cs f.types.length).2.1 f'
        (emitCases (M := E.Module) cs f.types.length).2.2 ∧
      List.Forall₂ (ResO f'.types) (emitCases (M := E.Module) cs f.types.length).1
        (toClosedCases cs)
  | [], f => ⟨f, PreTys.nil f, .nil⟩
  | none :: cs, f => by
    obtain ⟨f₁, hP₁, hR₁⟩ := emitCases_pre cs f
    rw [emitCases_none]
    exact ⟨f₁, hP₁, .cons (ResO.none _) hR₁⟩
  | some t :: cs, f => by
    obtain ⟨f₁, hP₁, hR₁⟩ := emitTy_pre t f
    obtain ⟨f₂, hP₂, hR₂⟩ := emitCases_pre cs f₁
    have hl₁ : f₁.types.length = (emitTy (M := E.Module) t f.types.length).2.2 := hP₁.2.2
    rw [emitCases_some, ← hl₁]
    exact ⟨f₂, hP₁.trans hP₂, .cons ((ResO.some hR₁).mono hP₂.prefix) hR₂⟩
end

end Pre

/-! ## The definitions of one import -/

section Imports

variable {Pf : Silmaril.Wasm.Numerics.Profile} {R : Recurse (core3P Pf) σ} {inst : InstId}
  {outer : List (Frame (core3P Pf))} {args : Exports (core3P Pf)} {s : CStore (core3P Pf)}

theorem importDefs_eq (p : String × FuncTy) (n : Nat) :
    (SimpleI.importDefs p n : List (Syntax.Definition (core3P Pf).Module) × Nat) =
      ((emitTys (M := (core3P Pf).Module) p.2.params n).2.1 ++
        (emitTys (M := (core3P Pf).Module) p.2.results
          (emitTys (M := (core3P Pf).Module) p.2.params n).2.2).2.1 ++
        [.type (.func { params := labels "a" (emitTys (M := (core3P Pf).Module) p.2.params n).1,
                        result := (emitTys (M := (core3P Pf).Module) p.2.results
                          (emitTys (M := (core3P Pf).Module) p.2.params n).2.2).1.head? }),
         .import_ { name := p.1 } (.func (emitTys (M := (core3P Pf).Module) p.2.results
           (emitTys (M := (core3P Pf).Module) p.2.params n).2.2).2.2)],
        (emitTys (M := (core3P Pf).Module) p.2.results
          (emitTys (M := (core3P Pf).Module) p.2.params n).2.2).2.2 + 1) := by
  simp only [SimpleI.importDefs]
  rfl

theorem importsDefs_cons (p : String × FuncTy) (ps : Iface) (n : Nat) :
    SimpleI.importsDefs (p :: ps) n =
      ((SimpleI.importDefs p n).1 ++ (SimpleI.importsDefs ps (SimpleI.importDefs p n).2).1,
        (SimpleI.importsDefs ps (SimpleI.importDefs p n).2).2) := by
  simp only [SimpleI.importsDefs]

/-- The emitted function type of an import resolves to `witFt`. -/
theorem resolveFuncType_witFt {f : Frame (core3P Pf)} {ft : FuncTy} {ps rs : List Syntax.VT}
    (hp : List.Forall₂ (Res f.types) ps (toClosedList ft.params))
    (hr : List.Forall₂ (Res f.types) rs (toClosedList ft.results)) :
    resolveFuncType? f { params := labels "a" ps, result := rs.head? } = some (witFt ft) :=
  resolveFuncType_lifted (x := ⟨"", ft, 0⟩) hp hr

/-- **A function import with the root argument `func k`**, whose host function has the
descriptor's type, pushes component function `k`. -/
theorem import_run (sc : Scope (core3P Pf)) (cfg : Machine.Config (core3P Pf) σ) {nm : String}
    {n : Nat} {k : FuncId} {t : Types.FuncType RtId} {fi : CFuncInst (core3P Pf)}
    (hl : args.lookup nm = some (.func k)) (hf : sc.frame.types[n]? = some (.func t))
    (hs : ArenaField.funcs.get? cfg.store k = some fi) (ht : fi.ft = t) :
    TRuns (instantiateDef R inst outer args sc (.import_ { name := nm } (.func n))) cfg
      { sc with frame := { sc.frame with funcs := sc.frame.funcs ++ [k] } } cfg := by
  have hc : importTypeCheck cfg.store sc.frame nm (.func n) (.func k) = .ok () :=
    importTypeCheck_func cfg.store sc.frame nm hf hs ht
  have hpush : (pushEntry sc.frame (Syntax.ExternDesc.func n).sort (.item (.func k)) :
      P (core3P Pf) σ (Frame (core3P Pf))) =
      Pure.pure { sc.frame with funcs := sc.frame.funcs ++ [k] } := by
    simp only [pushEntry, Syntax.ExternDesc.sort, Frame.push, need, orTrap]
  simp only [instantiateDef, hl, orTrap, pure_bind]
  refine (TRuns.getStore cfg).bind ((checkImport_run hc cfg).bind ?_)
  rw [hpush, pure_bind]
  exact TRuns.pure _ cfg

/-- The pre-check of a function import with the root argument `func k`. -/
theorem precheck_import (f : Frame (core3P Pf)) {nm : String} {n : Nat} {k : FuncId}
    {t : Types.FuncType RtId} {fi : CFuncInst (core3P Pf)}
    (hl : args.lookup nm = some (.func k)) (hf : f.types[n]? = some (.func t))
    (hs : ArenaField.funcs.get? s k = some fi) (ht : fi.ft = t) :
    precheckDef s args f (.import_ { name := nm } (.func n)) = .ok (some f) := by
  have hc : importTypeCheck s f nm (.func n) (.func k) = .ok () :=
    importTypeCheck_func s f nm hf hs ht
  simp only [precheckDef, hl, hc, Syntax.ExternDesc.sort, typeRelevant]
  rfl

/-- **The definitions of one import run silently**, pushing component function `k`. -/
theorem importDef_run (p : String × FuncTy) (k : FuncId) (sc : Scope (core3P Pf))
    (cfg : Machine.Config (core3P Pf) σ) {fi : CFuncInst (core3P Pf)}
    (hl : args.lookup p.1 = some (.func k)) (hs : ArenaField.funcs.get? cfg.store k = some fi)
    (ht : fi.ft = witFt p.2) :
    ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) sc
        (SimpleI.importDefs p sc.frame.types.length).1) cfg sc' cfg ∧
      (∃ new, sc'.frame =
        { sc.frame with types := sc.frame.types ++ new, funcs := sc.frame.funcs ++ [k] }) ∧
      sc'.frame.types.length = (SimpleI.importDefs p sc.frame.types.length).2 ∧
      funcExports sc'.exports = funcExports sc.exports := by
  obtain ⟨sc₁, hP₁, hR₁⟩ := emitTys_run (R := R) (inst := inst) (outer := outer) (args := args)
    p.2.params sc
  obtain ⟨sc₂, hP₂, hR₂⟩ := emitTys_run (R := R) (inst := inst) (outer := outer) (args := args)
    p.2.results sc₁
  have hl₁ : sc₁.frame.types.length =
      (emitTys (M := (core3P Pf).Module) p.2.params sc.frame.types.length).2.2 := hP₁.2.2.1
  have hl₂ : sc₂.frame.types.length =
      (emitTys (M := (core3P Pf).Module) p.2.results sc₁.frame.types.length).2.2 := hP₂.2.2.1
  rw [importDefs_eq, ← hl₁, ← hl₂]
  have hft : resolveFuncType? sc₂.frame
      { params := labels "a" (emitTys (M := (core3P Pf).Module) p.2.params
          sc.frame.types.length).1,
        result := (emitTys (M := (core3P Pf).Module) p.2.results
          sc₁.frame.types.length).1.head? } = some (witFt p.2) :=
    resolveFuncType_witFt (hR₁.imp fun _ _ h => h.mono hP₂.prefix) hR₂
  have h₃ := instDef_func (R := R) (inst := inst) (outer := outer) (args := args) sc₂ hft
  have hty : (sc₂.frame.types ++ [.func (witFt p.2)])[sc₂.frame.types.length]? =
      some (.func (witFt p.2)) := by simp
  have h₄ := import_run (R := R) (inst := inst) (outer := outer)
    { sc₂ with frame := { sc₂.frame with types := sc₂.frame.types ++ [.func (witFt p.2)] } }
    cfg hl hty hs ht
  obtain ⟨new₁, hf₁⟩ := hP₁.2.1
  obtain ⟨new₂, hf₂⟩ := hP₂.2.1
  refine ⟨_, TRuns.foldlM_append (TRuns.foldlM_append (TRuns.ofPure hP₁ cfg)
    (TRuns.ofPure hP₂ cfg)) (TRuns.foldlM_cons (TRuns.of_eq cfg h₃)
    (TRuns.foldlM_cons h₄ (TRuns.foldlM_nil _ _))), ⟨new₁ ++ new₂ ++ [.func (witFt p.2)], ?_⟩,
    by simp, hP₂.2.2.2.1.trans hP₁.2.2.2.1⟩
  show { sc₂.frame with types := sc₂.frame.types ++ [Types.TypeDef.func (witFt p.2)],
                        funcs := sc₂.frame.funcs ++ [k] } = _
  rw [hf₂, hf₁]
  simp only [List.append_assoc]

/-- **The pre-check of the definitions of one import** extends the type index space as their
instantiation does. -/
theorem importDef_pre (p : String × FuncTy) (k : FuncId) (f : Frame (core3P Pf))
    {fi : CFuncInst (core3P Pf)} (hl : args.lookup p.1 = some (.func k))
    (hs : ArenaField.funcs.get? s k = some fi) (ht : fi.ft = witFt p.2) :
    ∃ f', PreTys s args f (SimpleI.importDefs p f.types.length).1 f'
      (SimpleI.importDefs p f.types.length).2 := by
  obtain ⟨f₁, hP₁, hR₁⟩ := emitTys_pre (s := s) (args := args) p.2.params f
  obtain ⟨f₂, hP₂, hR₂⟩ := emitTys_pre (s := s) (args := args) p.2.results f₁
  have hl₁ : f₁.types.length =
      (emitTys (M := (core3P Pf).Module) p.2.params f.types.length).2.2 := hP₁.2.2
  have hl₂ : f₂.types.length =
      (emitTys (M := (core3P Pf).Module) p.2.results f₁.types.length).2.2 := hP₂.2.2
  rw [importDefs_eq, ← hl₁, ← hl₂]
  have hft : resolveFuncType? f₂
      { params := labels "a" (emitTys (M := (core3P Pf).Module) p.2.params f.types.length).1,
        result := (emitTys (M := (core3P Pf).Module) p.2.results f₁.types.length).1.head? } =
      some (witFt p.2) :=
    resolveFuncType_witFt (hR₁.imp fun _ _ h => h.mono hP₂.prefix) hR₂
  have h₃ := PreTys.func (s := s) (args := args) f₂ hft
  have hty : (f₂.types ++ [.func (witFt p.2)])[f₂.types.length]? = some (.func (witFt p.2)) := by
    simp
  have h₄ : PreTys s args { f₂ with types := f₂.types ++ [.func (witFt p.2)] }
      [.import_ { name := p.1 } (.func f₂.types.length)]
      { f₂ with types := f₂.types ++ [.func (witFt p.2)] } (f₂.types.length + 1) := by
    refine ⟨fun rest => ?_, ⟨[], by simp⟩, by simp⟩
    simp only [List.singleton_append, precheckImports,
      precheck_import (s := s) { f₂ with types := f₂.types ++ [.func (witFt p.2)] } hl hty hs ht]
  exact ⟨_, (hP₁.trans hP₂).trans (h₃.trans h₄)⟩

/-- **The definitions of the imports `ps` run silently**, pushing component functions
`k, k + 1, …` when import `j` of `ps` is bound to the host function `k + j` of its type. -/
theorem importsDefs_run : ∀ (ps : Iface) (k : Nat) (sc : Scope (core3P Pf))
    (cfg : Machine.Config (core3P Pf) σ),
    (∀ j (hj : j < ps.length), args.lookup ps[j].1 = some (.func ⟨k + j⟩) ∧
      ArenaField.funcs.get? cfg.store ⟨k + j⟩ = some (.host (witFt ps[j].2) ⟨k + j⟩)) →
    ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) sc
        (SimpleI.importsDefs ps sc.frame.types.length).1) cfg sc' cfg ∧
      (∃ new, sc'.frame = { sc.frame with types := sc.frame.types ++ new,
                                          funcs := sc.frame.funcs ++ (List.range' k ps.length).map FuncId.mk }) ∧
      sc'.frame.types.length = (SimpleI.importsDefs ps sc.frame.types.length).2 ∧
      funcExports sc'.exports = funcExports sc.exports
  | [], _, sc, cfg, _ => ⟨sc, TRuns.foldlM_nil sc cfg, ⟨[], by cases sc.frame; simp⟩, rfl, rfl⟩
  | p :: ps, k, sc, cfg, h => by
    obtain ⟨hl, hs⟩ := h 0 (Nat.zero_lt_succ _)
    obtain ⟨sc₁, hr₁, ⟨new₁, hf₁⟩, hn₁, hx₁⟩ := importDef_run (R := R) (inst := inst)
      (outer := outer) p ⟨k + 0⟩ sc cfg hl hs rfl
    obtain ⟨sc₂, hr₂, ⟨new₂, hf₂⟩, hn₂, hx₂⟩ := importsDefs_run ps (k + 1) sc₁ cfg
      (fun j hj => by
        obtain ⟨a, b⟩ := h (j + 1) (Nat.succ_lt_succ hj)
        rw [← Nat.add_assoc, Nat.add_right_comm] at a b
        exact ⟨a, b⟩)
    rw [importsDefs_cons]
    refine ⟨sc₂, TRuns.foldlM_append hr₁ (hn₁ ▸ hr₂), ⟨new₁ ++ new₂, ?_⟩, hn₁ ▸ hn₂,
      hx₂.trans hx₁⟩
    rw [hf₂, hf₁]
    simp only [List.length_cons, List.range'_succ, List.map_cons, List.append_assoc,
      List.singleton_append, Nat.add_zero]

/-- **The pre-check of the import definitions** passes them, extending the type index space. -/
theorem importsDefs_pre : ∀ (ps : Iface) (k : Nat) (f : Frame (core3P Pf)),
    (∀ j (hj : j < ps.length), args.lookup ps[j].1 = some (.func ⟨k + j⟩) ∧
      ArenaField.funcs.get? s ⟨k + j⟩ = some (.host (witFt ps[j].2) ⟨k + j⟩)) →
    ∃ f', PreTys s args f (SimpleI.importsDefs ps f.types.length).1 f'
      (SimpleI.importsDefs ps f.types.length).2
  | [], _, f, _ => ⟨f, PreTys.nil f⟩
  | p :: ps, k, f, h => by
    obtain ⟨hl, hs⟩ := h 0 (Nat.zero_lt_succ _)
    obtain ⟨f₁, hP₁⟩ := importDef_pre p ⟨k + 0⟩ f hl hs rfl
    obtain ⟨f₂, hP₂⟩ := importsDefs_pre ps (k + 1) f₁
      (fun j hj => by
        obtain ⟨a, b⟩ := h (j + 1) (Nat.succ_lt_succ hj)
        rw [← Nat.add_assoc, Nat.add_right_comm] at a b
        exact ⟨a, b⟩)
    rw [importsDefs_cons]
    exact ⟨f₂, hP₁.trans (hP₁.2.2 ▸ hP₂)⟩

end Imports

end Silmaril.Proofs.Wasm.Component.Reference
