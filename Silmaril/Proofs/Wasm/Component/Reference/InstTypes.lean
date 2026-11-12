module

public import Silmaril.Proofs.Wasm.Component.Reference.InstCore

/-!
# Instantiating the type definitions of `Simple.toRef`

The type definitions that `Simple.toRef` emits for an IR type (`emitTy`, `emitTys`,
`emitCases`) are run by `instantiateDef` without any machine operation: they only extend the
type index space of the frame (and record type exports, which are no function exports). The
emitted value type then resolves to `toClosed t` in every frame extending the type index space
(`emitTy_run`). Consequently the emitted function type of an export resolves to `liftedFt x`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component (Syntax.Definition Syntax.VT Syntax.DefValType)

variable {E : CoreEngine} {σ : Type}

/-! ## Resolution in extended frames -/

/-- `v` resolves to `t` in every frame whose type index space extends `tys`. -/
def Res (tys : List (Types.TypeDef RtId E.ExternType)) (v : Syntax.VT)
    (t : WIT.ClosedType RtId) : Prop :=
  ∀ f : Frame E, tys <+: f.types → resolveValType? f v = some t

theorem Res.mono {tys tys' : List (Types.TypeDef RtId E.ExternType)} {v : Syntax.VT}
    {t : WIT.ClosedType RtId} (h : Res tys v t) (hp : tys <+: tys') : Res tys' v t :=
  fun f hf => h f (hp.trans hf)

theorem Res.prim (tys : List (Types.TypeDef RtId E.ExternType)) (p : Syntax.Prim) :
    Res tys (.prim p) (primType p) :=
  fun _ _ => rfl

/-- An index whose entry is a value type resolves to it. -/
theorem Res.idx {tys : List (Types.TypeDef RtId E.ExternType)} {i : Nat}
    {t : WIT.ClosedType RtId} (h : tys[i]? = some (.val t)) : Res tys (.idx i) t := by
  intro f hf
  have hi : f.types[i]? = some (.val t) := by
    obtain ⟨l, hl⟩ := hf
    rw [← hl, List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1, h]
  simp only [resolveValType?, Frame.type?, hi]

/-! ## Running definitions without machine operations -/

/-- No definition is an import. -/
def NoImport {M : Type} (ds : List (Syntax.Definition M)) : Prop :=
  ∀ d ∈ ds, ∀ n x, d ≠ .import_ n x

theorem NoImport.append {M : Type} {ds ds' : List (Syntax.Definition M)} (h : NoImport ds)
    (h' : NoImport ds') : NoImport (ds ++ ds') := by
  intro d hd
  rcases List.mem_append.1 hd with hd | hd
  · exact h d hd
  · exact h' d hd

variable [∀ a b, Decidable (E.ExternSub a b)] (R : Recurse E σ) (inst : InstId) (outer : List (Frame E)) (args : Exports E)

/-- The definitions `ds` run from `sc` to `sc'` without a machine operation, only appending to
the type index space (giving `n'` types) and recording no function export. -/
def PureTys (sc : Scope E) (ds : List (Syntax.Definition E.Module)) (sc' : Scope E) (n' : Nat) :
    Prop :=
  ds.foldlM (instantiateDef R inst outer args) sc = (pure sc' : P E σ (Scope E)) ∧
    (∃ new, sc'.frame = { sc.frame with types := sc.frame.types ++ new }) ∧
    sc'.frame.types.length = n' ∧ funcExports sc'.exports = funcExports sc.exports ∧
    NoImport ds

variable {R inst outer args}

theorem PureTys.nil (sc : Scope E) :
    PureTys R inst outer args sc [] sc sc.frame.types.length :=
  ⟨rfl, ⟨[], by rw [List.append_nil]; cases sc.frame; rfl⟩, rfl, rfl, fun _ h => by cases h⟩

theorem PureTys.trans {sc sc₁ sc₂ : Scope E} {ds ds' : List (Syntax.Definition E.Module)}
    {n₁ n₂ : Nat} (h : PureTys R inst outer args sc ds sc₁ n₁)
    (h' : PureTys R inst outer args sc₁ ds' sc₂ n₂) :
    PureTys R inst outer args sc (ds ++ ds') sc₂ n₂ := by
  obtain ⟨e₁, ⟨new₁, f₁⟩, -, x₁, i₁⟩ := h
  obtain ⟨e₂, ⟨new₂, f₂⟩, l₂, x₂, i₂⟩ := h'
  refine ⟨?_, ⟨new₁ ++ new₂, ?_⟩, l₂, x₂.trans x₁, i₁.append i₂⟩
  · rw [List.foldlM_append, e₁]
    exact e₂
  · rw [f₂, f₁, List.append_assoc]

/-! ## Single type definitions -/

/-- A value type definition that resolves pushes its type. -/
theorem instDef_val (sc : Scope E) {d : Syntax.DefValType} {t : WIT.ClosedType RtId}
    (h : resolveDefValType? sc.frame d = some t) :
    instantiateDef R inst outer args sc (.type (.val d)) =
      (pure { sc with frame := { sc.frame with types := sc.frame.types ++ [.val t] } } :
        P E σ (Scope E)) := by
  simp only [instantiateDef, staticType?, h, Option.map_some, need, orTrap, pushEntry, Frame.push]
  rfl

/-- A function type definition that resolves pushes its type. -/
theorem instDef_func (sc : Scope E) {ft : Syntax.FuncType} {t : Types.FuncType RtId}
    (h : resolveFuncType? sc.frame ft = some t) :
    instantiateDef R inst outer args sc (.type (.func ft)) =
      (pure { sc with frame := { sc.frame with types := sc.frame.types ++ [.func t] } } :
        P E σ (Scope E)) := by
  simp only [instantiateDef, staticType?, h, Option.map_some, need, orTrap, pushEntry, Frame.push]
  rfl

/-- A type export re-pushes the exported type and records a type export. -/
theorem instDef_typeExport (sc : Scope E) {n : Nat} {ty : Types.TypeDef RtId E.ExternType}
    (h : sc.frame.types[n]? = some ty) :
    instantiateDef R inst outer args sc (typeExport n) =
      (pure { frame := { sc.frame with types := sc.frame.types ++ [ty] },
              exports := sc.exports ++ [(tag "t" n, .type ty)] } : P E σ (Scope E)) := by
  simp only [instantiateDef, typeExport, Frame.get?, Frame.type?, h, Option.map_some, need,
    orTrap, Function.comp_apply, Entry.toItem?, pushEntry, Frame.push]
  rfl

theorem foldlM_single {sc sc' : Scope E} {d : Syntax.Definition E.Module}
    (h : instantiateDef R inst outer args sc d = (pure sc' : P E σ (Scope E))) :
    [d].foldlM (instantiateDef R inst outer args) sc = (pure sc' : P E σ (Scope E)) := by
  rw [List.foldlM_cons, h]
  rfl

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem funcExports_append_type (l : Exports E) (n : String)
    (ty : Types.TypeDef RtId E.ExternType) :
    Silmaril.Wasm.Component.funcExports (l ++ [(n, .type ty)]) =
      Silmaril.Wasm.Component.funcExports l := by
  simp only [Silmaril.Wasm.Component.funcExports, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, List.append_nil]

theorem PureTys.val (sc : Scope E) {d : Syntax.DefValType} {t : WIT.ClosedType RtId}
    (h : resolveDefValType? sc.frame d = some t) :
    PureTys R inst outer args sc [.type (.val d)]
      { sc with frame := { sc.frame with types := sc.frame.types ++ [.val t] } }
      (sc.frame.types.length + 1) :=
  ⟨foldlM_single (instDef_val sc h), ⟨_, rfl⟩, List.length_append, rfl,
    fun _ hd => by rw [List.mem_singleton.1 hd]; intro _ _ e; cases e⟩

theorem PureTys.tyExport (sc : Scope E) {n : Nat} {ty : Types.TypeDef RtId E.ExternType}
    (h : sc.frame.types[n]? = some ty) :
    PureTys R inst outer args sc [typeExport n]
      { frame := { sc.frame with types := sc.frame.types ++ [ty] },
        exports := sc.exports ++ [(tag "t" n, .type ty)] }
      (sc.frame.types.length + 1) :=
  ⟨foldlM_single (instDef_typeExport sc h), ⟨_, rfl⟩, List.length_append,
    funcExports_append_type _ _ _,
    fun _ hd => by rw [List.mem_singleton.1 hd]; intro _ _ e; cases e⟩

/-! ## Labelled lists -/

theorem mapM_mapIdx_pair {α β : Type} {F : String × α → Option (String × β)}
    {R : α → β → Prop} (hF : ∀ n x y, R x y → F (n, x) = some (n, y)) :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → ∀ f : Nat → String,
      (xs.mapIdx fun i x => (f i, x)).mapM F = some (ys.mapIdx fun i y => (f i, y))
  | [], [], .nil, _ => rfl
  | x :: xs, y :: ys, .cons hxy hs, f => by
    rw [List.mapIdx_cons, List.mapIdx_cons, List.mapM_cons, hF _ _ _ hxy,
      mapM_mapIdx_pair hF hs (fun i => f (i + 1))]
    rfl

theorem mapM_labels {α β : Type} {F : String × α → Option (String × β)} {R : α → β → Prop}
    (hF : ∀ n x y, R x y → F (n, x) = some (n, y)) (p : String) {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) : (labels p xs).mapM F = some (labels p ys) :=
  mapM_mapIdx_pair hF h (tag p)

/-! ## Equations of the emitters -/

section Emit

variable {M : Type}

theorem emitTy_record (ts : List ValTy) (n : Nat) :
    emitTy (M := M) (.record ts) n =
      (.idx ((emitTys (M := M) ts n).2.2 + 1),
        (emitTys ts n).2.1 ++ [.type (.val (.record (labels "f" (emitTys (M := M) ts n).1))),
          typeExport (emitTys (M := M) ts n).2.2], (emitTys (M := M) ts n).2.2 + 2) := by
  simp only [emitTy]

theorem emitTy_variant (cs : List (Option ValTy)) (n : Nat) :
    emitTy (M := M) (.variant cs) n =
      (.idx ((emitCases (M := M) cs n).2.2 + 1),
        (emitCases cs n).2.1 ++
          [.type (.val (.variant (labels "c" (emitCases (M := M) cs n).1))),
            typeExport (emitCases (M := M) cs n).2.2], (emitCases (M := M) cs n).2.2 + 2) := by
  simp only [emitTy]

theorem emitTys_cons (t : ValTy) (ts : List ValTy) (n : Nat) :
    emitTys (M := M) (t :: ts) n =
      ((emitTy (M := M) t n).1 :: (emitTys (M := M) ts (emitTy (M := M) t n).2.2).1,
        (emitTy (M := M) t n).2.1 ++ (emitTys (M := M) ts (emitTy (M := M) t n).2.2).2.1,
        (emitTys (M := M) ts (emitTy (M := M) t n).2.2).2.2) := by
  simp only [emitTys]

theorem emitCases_none (cs : List (Option ValTy)) (n : Nat) :
    emitCases (M := M) (none :: cs) n =
      (none :: (emitCases (M := M) cs n).1, (emitCases (M := M) cs n).2.1,
        (emitCases (M := M) cs n).2.2) := by
  simp only [emitCases]

theorem emitCases_some (t : ValTy) (cs : List (Option ValTy)) (n : Nat) :
    emitCases (M := M) (some t :: cs) n =
      (some (emitTy (M := M) t n).1 :: (emitCases (M := M) cs (emitTy (M := M) t n).2.2).1,
        (emitTy (M := M) t n).2.1 ++ (emitCases (M := M) cs (emitTy (M := M) t n).2.2).2.1,
        (emitCases (M := M) cs (emitTy (M := M) t n).2.2).2.2) := by
  simp only [emitCases]

end Emit

/-! ## Resolution of emitted definitions -/

/-- `o` resolves to `c` in every frame whose type index space extends `tys`. -/
def ResO (tys : List (Types.TypeDef RtId E.ExternType)) (o : Option Syntax.VT)
    (c : Option (WIT.ClosedType RtId)) : Prop :=
  ∀ f : Frame E, tys <+: f.types → resolveOptValType? f o = some c

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem ResO.mono {tys tys' : List (Types.TypeDef RtId E.ExternType)} {o : Option Syntax.VT}
    {c : Option (WIT.ClosedType RtId)} (h : ResO tys o c) (hp : tys <+: tys') : ResO tys' o c :=
  fun f hf => h f (hp.trans hf)

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem ResO.none (tys : List (Types.TypeDef RtId E.ExternType)) : ResO tys none none :=
  fun _ _ => rfl

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem ResO.some {tys : List (Types.TypeDef RtId E.ExternType)} {v : Syntax.VT}
    {t : WIT.ClosedType RtId} (h : Res tys v t) : ResO tys (some v) (some t) := by
  intro f hf
  simp only [resolveOptValType?, h f hf, Option.map_some]

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem resolve_record {tys : List (Types.TypeDef RtId E.ExternType)} {vs : List Syntax.VT}
    {ts : List (WIT.ClosedType RtId)} (h : List.Forall₂ (Res tys) vs ts) (f : Frame E)
    (hf : tys <+: f.types) :
    resolveDefValType? f (.record (labels "f" vs)) = some (.record (labels "f" ts)) := by
  have hm := mapM_labels (F := fun p => (fun x => (p.1, x)) <$> resolveValType? f p.2)
    (R := fun v t => resolveValType? f v = some t) (fun n x y hxy => by simp only [hxy]; rfl)
    "f" (h.imp fun _ _ hr => hr f hf)
  simp only [resolveDefValType?]
  rw [hm]
  rfl

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem resolve_variant {tys : List (Types.TypeDef RtId E.ExternType)}
    {os : List (Option Syntax.VT)} {cs : List (Option (WIT.ClosedType RtId))}
    (h : List.Forall₂ (ResO tys) os cs) (f : Frame E) (hf : tys <+: f.types) :
    resolveDefValType? f (.variant (labels "c" os)) = some (.variant (labels "c" cs)) := by
  have hm := mapM_labels (F := fun p => (fun x => (p.1, x)) <$> resolveOptValType? f p.2)
    (R := fun o c => resolveOptValType? f o = some c) (fun n x y hxy => by simp only [hxy]; rfl)
    "c" (h.imp fun _ _ hr => hr f hf)
  simp only [resolveDefValType?]
  rw [hm]
  rfl

/-! ## Runs of emitted definitions -/

theorem PureTys.prefix {sc sc' : Scope E} {ds : List (Syntax.Definition E.Module)} {n : Nat}
    (h : PureTys R inst outer args sc ds sc' n) : sc.frame.types <+: sc'.frame.types := by
  obtain ⟨-, ⟨new, hf⟩, -⟩ := h
  rw [hf]
  exact List.prefix_append _ _

theorem PureTys.cast {sc sc' : Scope E} {ds ds' : List (Syntax.Definition E.Module)}
    {n n' : Nat} (h : PureTys R inst outer args sc ds sc' n) (hd : ds = ds') (hn : n = n') :
    PureTys R inst outer args sc ds' sc' n' :=
  hd ▸ hn ▸ h

/-- A value type definition followed by its type export. -/
theorem PureTys.valExport (sc : Scope E) {d : Syntax.DefValType} {t : WIT.ClosedType RtId}
    (h : resolveDefValType? sc.frame d = some t) :
    ∃ sc', PureTys R inst outer args sc [.type (.val d), typeExport sc.frame.types.length] sc'
        (sc.frame.types.length + 2) ∧
      Res sc'.frame.types (.idx (sc.frame.types.length + 1)) t := by
  have h₁ := PureTys.val (R := R) (inst := inst) (outer := outer) (args := args) sc h
  have hl : (sc.frame.types ++ [.val t])[sc.frame.types.length]? = some (.val t) := by simp
  have h₂ := PureTys.tyExport (R := R) (inst := inst) (outer := outer) (args := args)
    { sc with frame := { sc.frame with types := sc.frame.types ++ [.val t] } } hl
  refine ⟨_, (h₁.trans h₂).cast rfl (by simp), Res.idx ?_⟩
  simp

mutual
/-- **The definitions emitted for an IR type run without a machine operation** and the
emitted value type resolves to `toClosed t`. -/
theorem emitTy_run : ∀ (t : ValTy) (sc : Scope E),
    ∃ sc', PureTys R inst outer args sc (emitTy (M := E.Module) t sc.frame.types.length).2.1 sc'
        (emitTy (M := E.Module) t sc.frame.types.length).2.2 ∧
      Res sc'.frame.types (emitTy (M := E.Module) t sc.frame.types.length).1 (toClosed t)
  | .bool, sc => ⟨sc, PureTys.nil sc, Res.prim _ .bool⟩
  | .s8, sc => ⟨sc, PureTys.nil sc, Res.prim _ .s8⟩
  | .u8, sc => ⟨sc, PureTys.nil sc, Res.prim _ .u8⟩
  | .s16, sc => ⟨sc, PureTys.nil sc, Res.prim _ .s16⟩
  | .u16, sc => ⟨sc, PureTys.nil sc, Res.prim _ .u16⟩
  | .s32, sc => ⟨sc, PureTys.nil sc, Res.prim _ .s32⟩
  | .u32, sc => ⟨sc, PureTys.nil sc, Res.prim _ .u32⟩
  | .s64, sc => ⟨sc, PureTys.nil sc, Res.prim _ .s64⟩
  | .u64, sc => ⟨sc, PureTys.nil sc, Res.prim _ .u64⟩
  | .f32, sc => ⟨sc, PureTys.nil sc, Res.prim _ .f32⟩
  | .f64, sc => ⟨sc, PureTys.nil sc, Res.prim _ .f64⟩
  | .char, sc => ⟨sc, PureTys.nil sc, Res.prim _ .char⟩
  | .record ts, sc => by
    obtain ⟨sc₁, hP₁, hR₁⟩ := emitTys_run ts sc
    have hl₁ : sc₁.frame.types.length = (emitTys (M := E.Module) ts sc.frame.types.length).2.2 :=
      hP₁.2.2.1
    have hrec : resolveDefValType? sc₁.frame
        (.record (labels "f" (emitTys (M := E.Module) ts sc.frame.types.length).1)) =
          some (toClosed (.record ts)) :=
      resolve_record hR₁ _ (List.prefix_refl _)
    obtain ⟨sc₂, hP₂, hR₂⟩ := PureTys.valExport (R := R) (inst := inst) (outer := outer)
      (args := args) sc₁ hrec
    rw [emitTy_record, ← hl₁]
    exact ⟨sc₂, hP₁.trans hP₂, hR₂⟩
  | .variant cs, sc => by
    obtain ⟨sc₁, hP₁, hR₁⟩ := emitCases_run cs sc
    have hl₁ : sc₁.frame.types.length =
        (emitCases (M := E.Module) cs sc.frame.types.length).2.2 := hP₁.2.2.1
    have hvar : resolveDefValType? sc₁.frame
        (.variant (labels "c" (emitCases (M := E.Module) cs sc.frame.types.length).1)) =
          some (toClosed (.variant cs)) :=
      resolve_variant hR₁ _ (List.prefix_refl _)
    obtain ⟨sc₂, hP₂, hR₂⟩ := PureTys.valExport (R := R) (inst := inst) (outer := outer)
      (args := args) sc₁ hvar
    rw [emitTy_variant, ← hl₁]
    exact ⟨sc₂, hP₁.trans hP₂, hR₂⟩

/-- `emitTy_run` on lists. -/
theorem emitTys_run : ∀ (ts : List ValTy) (sc : Scope E),
    ∃ sc', PureTys R inst outer args sc (emitTys (M := E.Module) ts sc.frame.types.length).2.1
        sc' (emitTys (M := E.Module) ts sc.frame.types.length).2.2 ∧
      List.Forall₂ (Res sc'.frame.types) (emitTys (M := E.Module) ts sc.frame.types.length).1
        (toClosedList ts)
  | [], sc => ⟨sc, PureTys.nil sc, .nil⟩
  | t :: ts, sc => by
    obtain ⟨sc₁, hP₁, hR₁⟩ := emitTy_run t sc
    obtain ⟨sc₂, hP₂, hR₂⟩ := emitTys_run ts sc₁
    have hl₁ : sc₁.frame.types.length = (emitTy (M := E.Module) t sc.frame.types.length).2.2 :=
      hP₁.2.2.1
    rw [emitTys_cons, ← hl₁]
    exact ⟨sc₂, hP₁.trans hP₂, .cons (hR₁.mono hP₂.prefix) hR₂⟩

/-- `emitTy_run` on variant cases. -/
theorem emitCases_run : ∀ (cs : List (Option ValTy)) (sc : Scope E),
    ∃ sc', PureTys R inst outer args sc (emitCases (M := E.Module) cs sc.frame.types.length).2.1
        sc' (emitCases (M := E.Module) cs sc.frame.types.length).2.2 ∧
      List.Forall₂ (ResO sc'.frame.types) (emitCases (M := E.Module) cs sc.frame.types.length).1
        (toClosedCases cs)
  | [], sc => ⟨sc, PureTys.nil sc, .nil⟩
  | none :: cs, sc => by
    obtain ⟨sc₁, hP₁, hR₁⟩ := emitCases_run cs sc
    rw [emitCases_none]
    exact ⟨sc₁, hP₁, .cons (ResO.none _) hR₁⟩
  | some t :: cs, sc => by
    obtain ⟨sc₁, hP₁, hR₁⟩ := emitTy_run t sc
    obtain ⟨sc₂, hP₂, hR₂⟩ := emitCases_run cs sc₁
    have hl₁ : sc₁.frame.types.length = (emitTy (M := E.Module) t sc.frame.types.length).2.2 :=
      hP₁.2.2.1
    rw [emitCases_some, ← hl₁]
    exact ⟨sc₂, hP₁.trans hP₂, .cons ((ResO.some hR₁).mono hP₂.prefix) hR₂⟩
end

end Silmaril.Proofs.Wasm.Component.Reference
