module

public import Silmaril.Proofs.Wasm.Component.Reference.InstLinkDefs

/-!
# The export maps of the nested instances

The parent of `Linked2.toRef` aliases function exports of its child instances by name
(`alias export i "name" func`), which reads the first export of that name (`lookupExport?`).
The export map of a child holds its function exports and the type exports that the emitted
type definitions name (`typeExport n`, name `tag "t" n`). This file proves that every entry of
such an export map is a function or carries a generated type name (`TagOrFunc`), so that a
function export whose name is not a generated type name is found by name
(`lookup_of_tagOrFunc`).

* `Rets Q p`: every return value of the program `p` satisfies `Q`; `SRuns.rets`: the result of
  a silent run satisfies it.
* `ExpName d`: an export definition of `d` is of a function or has a generated type name;
  `foldlM_rets`: instantiating definitions satisfying `ExpName` keeps `TagOrFunc` of the export
  map, whatever their runs do (late-bound calls included).
* `expName_toRef`, `expName_toRefI`: every definition of `Simple.toRef` and `SimpleI.toRef`
  satisfies `ExpName`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition)

/-! ## Return values of programs -/

/-- Every return value of the program satisfies `Q`. -/
inductive Rets {S : Sig} {α : Type} (Q : α → Prop) : Prog S α → Prop where
  | pure {a : α} : Q a → Rets Q (.pure a)
  | op {o : S.Op} {k : S.Resp o → Prog S α} : (∀ r, Rets Q (k r)) → Rets Q (.op o k)

namespace Rets

variable {S : Sig} {α β : Type}

theorem bind_of {P : α → Prop} {Q : β → Prop} {p : Prog S α} {f : α → Prog S β}
    (h : Rets P p) (hf : ∀ a, P a → Rets Q (f a)) : Rets Q (p >>= f) := by
  induction h with
  | pure ha => exact hf _ ha
  | op _ ih => exact .op fun r => ih r

theorem bind {Q : β → Prop} {p : Prog S α} {f : α → Prog S β} (hf : ∀ a, Rets Q (f a)) :
    Rets Q (p >>= f) := by
  induction p with
  | pure a => exact hf a
  | op o k ih => exact .op fun r => ih r

theorem pure' {Q : α → Prop} {a : α} (h : Q a) : Rets Q (Pure.pure a : Prog S α) := .pure h

end Rets

variable {E : CoreEngine} {σ : Type}

/-- **The result of a silent run returns from the program.** -/
theorem SRuns.rets {α : Type} {Q : α → Prop} {p : P E σ α} {m m' : Machine.Config E σ}
    {os : List HostObs} {a : α} (h : SRuns p m os a m') (hq : Rets Q p) : Q a := by
  induction h with
  | pure => cases hq; assumption
  | get _ ih => cases hq with | op hk => exact ih (hk _)
  | modify _ _ ih => cases hq with | op hk => exact ih (hk _)
  | emit _ ih => cases hq with | op hk => exact ih (hk _)

/-! ## Export maps of functions and generated type names -/

/-- Every entry of the export map is a function or has a generated type name. -/
def TagOrFunc (es : Exports E) : Prop :=
  ∀ p ∈ es, (∃ k, p.1 = tag "t" k) ∨ ∃ f, p.2 = .func f

theorem TagOrFunc.nil : TagOrFunc ([] : Exports E) := fun _ h => by cases h

theorem TagOrFunc.append {es es' : Exports E} (h : TagOrFunc es) (h' : TagOrFunc es') :
    TagOrFunc (es ++ es') := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h p hp
  · exact h' p hp

/-- **A function export with a name that is not generated is found by name**: in an export map
of functions and generated type names, looking up a name that is no generated type name finds
the function export map's entry. -/
theorem lookup_of_tagOrFunc {es : Exports E} (h : TagOrFunc es) {name : String}
    (hn : ∀ k, name ≠ tag "t" k) :
    lookupExport? es name = ((funcExports es).lookup name).map .func := by
  induction es with
  | nil => rfl
  | cons p es ih =>
    obtain ⟨n, v⟩ := p
    have ih' := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    rcases h (n, v) List.mem_cons_self with ⟨k, hk⟩ | ⟨f, hf⟩
    · have hne : (name == n) = false := beq_false_of_ne fun e => hn k (e.trans hk)
      cases v <;>
        simp only [lookupExport?, funcExports, List.lookup_cons, hne, List.filterMap_cons] at ih' ⊢ <;>
        exact ih'
    · subst hf
      simp only [lookupExport?, funcExports, List.lookup_cons, List.filterMap_cons] at ih' ⊢
      cases hb : name == n
      · exact ih'
      · rfl

/-- An export definition is of a function or has a generated type name. -/
def ExpName {M : Type} (d : Syntax.Definition M) : Prop :=
  ∀ n si o, d = .export_ n si o → (∃ k, n.name = tag "t" k) ∨ si.sort = .func

theorem expName_of_ne {M : Type} {d : Syntax.Definition M} (h : ∀ n si o, d ≠ .export_ n si o) :
    ExpName d := fun n si o e => absurd e (h n si o)


/-- The program traps. -/
theorem rets_trap {α : Type} {Q : α → Prop} (r : TrapReason) : Rets Q (trap r : P E σ α) :=
  .op fun e => nomatch e

theorem rets_need {α : Type} {Q : α → Prop} {what : String} {o : Option α}
    (h : ∀ a, o = some a → Q a) : Rets Q (need what o : P E σ α) := by
  cases o with
  | none => exact rets_trap _
  | some a => exact .pure (h a rfl)

variable [∀ a b, Decidable (E.ExternSub a b)] {R : Recurse E σ} {inst : InstId}
  {outer : List (Frame E)} {args : Exports E}

/-- An export with a generated type name keeps `TagOrFunc`. -/
theorem instDef_tagExport_rets (sc : Scope E) (nm : Syntax.ExternName)
    (si : Syntax.SortIdx Syntax.Sort_) (o : Option Syntax.ExternDesc) {k : Nat}
    (hk : nm.name = tag "t" k) (hs : TagOrFunc sc.exports) :
    Rets (fun sc' : Scope E => TagOrFunc sc'.exports)
      (instantiateDef R inst outer args sc (.export_ nm si o)) := by
  simp only [instantiateDef]
  refine Rets.bind fun _ => Rets.bind fun v => Rets.bind fun _ => Rets.pure' ?_
  show TagOrFunc (sc.exports ++ [(nm.name, v)])
  exact hs.append fun p hp => by rw [List.mem_singleton.1 hp, hk]; exact .inl ⟨k, rfl⟩

/-- A function export keeps `TagOrFunc`: the exported item is a function. -/
theorem instDef_funcExport_rets (sc : Scope E) (nm : Syntax.ExternName) (i : Nat)
    (o : Option Syntax.ExternDesc) (hs : TagOrFunc sc.exports) :
    Rets (fun sc' : Scope E => TagOrFunc sc'.exports)
      (instantiateDef R inst outer args sc (.export_ nm ⟨.func, i⟩ o)) := by
  simp only [instantiateDef]
  have he : ∀ e, sc.frame.get? .func i = some e → ∃ f, Entry.toItem? e = some (.func f) := by
    intro e h
    have h' : ∃ f, sc.frame.func? i = some f ∧ Entry.item (.func f) = e := by
      simpa only [Frame.get?, Option.map_eq_some_iff, Function.comp_apply] using h
    obtain ⟨f, -, hf⟩ := h'
    exact ⟨f, by rw [← hf]; rfl⟩
  refine Rets.bind_of (P := fun e => ∃ f, Entry.toItem? e = some (.func f)) (rets_need he)
    fun e ⟨f, hf⟩ => ?_
  have hv : ∀ v, Entry.toItem? e = some v → ∃ f, v = .func f :=
    fun v h => ⟨f, Option.some.inj (h.symm.trans hf)⟩
  refine Rets.bind_of (P := fun v => ∃ f, v = .func f) (rets_need hv)
    fun v hv' => Rets.bind fun _ => Rets.pure' ?_
  show TagOrFunc (sc.exports ++ [(nm.name, v)])
  exact hs.append fun p hp => by rw [List.mem_singleton.1 hp]; exact .inr hv'

/-- **One definition keeps `TagOrFunc`** of the export map, along every return. -/
theorem instDef_rets (sc : Scope E) {d : Syntax.Definition E.Module} (hd : ExpName d)
    (hs : TagOrFunc sc.exports) :
    Rets (fun sc' : Scope E => TagOrFunc sc'.exports)
      (instantiateDef R inst outer args sc d) := by
  cases d with
  | export_ n si o =>
    rcases hd n si o rfl with ⟨k, hk⟩ | hsort
    · exact instDef_tagExport_rets sc n si o hk hs
    · obtain ⟨s, i⟩ := si
      cases hsort
      exact instDef_funcExport_rets sc n i o hs
  | coreInstance e => cases e <;> simp only [instantiateDef] <;>
      repeat' first
        | exact Rets.pure' hs
        | refine Rets.bind fun _ => ?_
  | instance_ e => cases e <;> simp only [instantiateDef] <;>
      repeat' first
        | exact Rets.pure' hs
        | refine Rets.bind fun _ => ?_
  | «alias» a => cases a <;> simp only [instantiateDef] <;>
      repeat' first
        | exact Rets.pure' hs
        | refine Rets.bind fun _ => ?_
  | type t => cases t <;> simp only [instantiateDef] <;>
      repeat' first
        | exact Rets.pure' hs
        | refine Rets.bind fun _ => ?_
  | canon c => cases c <;> simp only [instantiateDef] <;>
      repeat' first
        | exact Rets.pure' hs
        | refine Rets.bind fun _ => ?_
  | _ =>
    simp only [instantiateDef]
    repeat' first
      | exact Rets.pure' hs
      | exact rets_trap _
      | refine Rets.bind fun _ => ?_

/-- **Instantiating definitions that satisfy `ExpName` keeps `TagOrFunc`** of the export map,
along every return. -/
theorem foldlM_rets : ∀ (ds : List (Syntax.Definition E.Module)) (sc : Scope E),
    (∀ d ∈ ds, ExpName d) → TagOrFunc sc.exports →
    Rets (fun sc' : Scope E => TagOrFunc sc'.exports)
      (ds.foldlM (instantiateDef R inst outer args) sc)
  | [], _, _, hs => Rets.pure' hs
  | d :: ds, sc, h, hs => by
    rw [List.foldlM_cons]
    exact Rets.bind_of (instDef_rets sc (h d List.mem_cons_self) hs) fun sc₁ h₁ =>
      foldlM_rets ds sc₁ (fun d hd => h d (List.mem_cons_of_mem _ hd)) h₁

/-! ## The definitions of the translations -/

section Syntax

variable {M : Type}

theorem expName_typeExport (n : Nat) : ExpName (typeExport n : Syntax.Definition M) := by
  intro nm si o e
  simp only [typeExport, Syntax.Definition.export_.injEq] at e
  exact .inl ⟨n, by rw [← e.1]⟩

theorem expName_funcExport (nm : Syntax.ExternName) (k : Nat) :
    ExpName (.export_ nm ⟨.func, k⟩ none : Syntax.Definition M) := by
  intro nm' si o e
  simp only [Syntax.Definition.export_.injEq] at e
  exact .inr (by rw [← e.2.1])

/-- Definitions that are no export. -/
theorem expName_noExport {d : Syntax.Definition M} (h : ∀ n si o, d ≠ .export_ n si o) :
    ExpName d := expName_of_ne h

mutual
/-- The emitted type definitions satisfy `ExpName`. -/
theorem emitTy_expName : ∀ (t : ValTy) (n : Nat), ∀ d ∈ (emitTy (M := M) t n).2.1, ExpName d
  | .bool, _ => fun _ h => by simp [emitTy] at h
  | .s8, _ => fun _ h => by simp [emitTy] at h
  | .u8, _ => fun _ h => by simp [emitTy] at h
  | .s16, _ => fun _ h => by simp [emitTy] at h
  | .u16, _ => fun _ h => by simp [emitTy] at h
  | .s32, _ => fun _ h => by simp [emitTy] at h
  | .u32, _ => fun _ h => by simp [emitTy] at h
  | .s64, _ => fun _ h => by simp [emitTy] at h
  | .u64, _ => fun _ h => by simp [emitTy] at h
  | .f32, _ => fun _ h => by simp [emitTy] at h
  | .f64, _ => fun _ h => by simp [emitTy] at h
  | .char, _ => fun _ h => by simp [emitTy] at h
  | .record ts, n => by
    rw [emitTy_record]
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact emitTys_expName ts n d hd
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact expName_noExport fun _ _ _ e => by cases e
      · exact expName_typeExport _
  | .variant cs, n => by
    rw [emitTy_variant]
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact emitCases_expName cs n d hd
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact expName_noExport fun _ _ _ e => by cases e
      · exact expName_typeExport _

/-- `emitTy_expName` on lists. -/
theorem emitTys_expName : ∀ (ts : List ValTy) (n : Nat), ∀ d ∈ (emitTys (M := M) ts n).2.1,
    ExpName d
  | [], _ => fun _ h => by simp [emitTys] at h
  | t :: ts, n => by
    rw [emitTys_cons]
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact emitTy_expName t n d hd
    · exact emitTys_expName ts _ d hd

/-- `emitTy_expName` on variant cases. -/
theorem emitCases_expName : ∀ (cs : List (Option ValTy)) (n : Nat),
    ∀ d ∈ (emitCases (M := M) cs n).2.1, ExpName d
  | [], _ => fun _ h => by simp [emitCases] at h
  | none :: cs, n => by
    rw [emitCases_none]
    exact emitCases_expName cs n
  | some t :: cs, n => by
    rw [emitCases_some]
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact emitTy_expName t n d hd
    · exact emitCases_expName cs _ d hd
end

/-- The definitions of an export: emitted types, the function type, the alias, the lift and
the function export. -/
theorem expName_exportTail {dps drs : List (Syntax.Definition M)} (hp : ∀ d ∈ dps, ExpName d)
    (hr : ∀ d ∈ drs, ExpName d) (d₁ d₂ d₃ : Syntax.Definition M)
    (h₁ : ∀ n si o, d₁ ≠ .export_ n si o) (h₂ : ∀ n si o, d₂ ≠ .export_ n si o)
    (h₃ : ∀ n si o, d₃ ≠ .export_ n si o) (nm : Syntax.ExternName) (k : Nat) :
    ∀ d ∈ dps ++ drs ++ [d₁, d₂, d₃, .export_ nm ⟨.func, k⟩ none], ExpName d := by
  intro d hd
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with (hd | hd) | rfl | rfl | rfl | rfl
  · exact hp d hd
  · exact hr d hd
  · exact expName_noExport h₁
  · exact expName_noExport h₂
  · exact expName_noExport h₃
  · exact expName_funcExport _ _

end Syntax

/-- Every definition of `Simple.exportsDefs` satisfies `ExpName`. -/
theorem exportsDefs_expName (m : NumModule) :
    ∀ (i : Nat) (xs : List SimpleExport) (n : Nat), ∀ d ∈ Simple.exportsDefs m i xs n, ExpName d
  | _, [], _ => fun _ h => by cases h
  | i, x :: xs, n => by
    intro d hd
    simp only [Simple.exportsDefs] at hd
    rcases List.mem_append.1 hd with hd | hd
    · simp only [Simple.exportDefs] at hd
      exact expName_exportTail (emitTys_expName _ _) (emitTys_expName _ _) _ _ _
        (fun _ _ _ e => by cases e) (fun _ _ _ e => by cases e) (fun _ _ _ e => by cases e)
        _ _ d hd
    · exact exportsDefs_expName m (i + 1) xs _ d hd

/-- **Every definition of `Simple.toRef` satisfies `ExpName`.** -/
theorem expName_toRef (c : Simple) : ∀ d ∈ c.toRef, ExpName d := by
  intro d hd
  simp only [Simple.toRef, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with (rfl | rfl) | hd
  · exact expName_noExport fun _ _ _ e => by cases e
  · exact expName_noExport fun _ _ _ e => by cases e
  · exact exportsDefs_expName c.mod 0 c.exports 0 d hd

/-- Every definition of `SimpleI.exportsDefsAt` satisfies `ExpName`. -/
theorem exportsDefsAt_expName (names : CoreIface) (ix base : Nat) :
    ∀ (i : Nat) (xs : List SimpleExport) (n : Nat),
      ∀ d ∈ SimpleI.exportsDefsAt names ix base i xs n, ExpName d
  | _, [], _ => fun _ h => by cases h
  | i, x :: xs, n => by
    intro d hd
    simp only [SimpleI.exportsDefsAt] at hd
    rcases List.mem_append.1 hd with hd | hd
    · simp only [SimpleI.exportDefsAt] at hd
      exact expName_exportTail (emitTys_expName _ _) (emitTys_expName _ _) _ _ _
        (fun _ _ _ e => by cases e) (fun _ _ _ e => by cases e) (fun _ _ _ e => by cases e)
        _ _ d hd
    · exact exportsDefsAt_expName names ix base (i + 1) xs _ d hd

/-- Every definition of `SimpleI.importsDefs` satisfies `ExpName`. -/
theorem importsDefs_expName : ∀ (ps : Iface) (n : Nat),
    ∀ d ∈ (SimpleI.importsDefs ps n).1, ExpName d
  | [], _ => fun _ h => by cases h
  | p :: ps, n => by
    intro d hd
    simp only [SimpleI.importsDefs] at hd
    rcases List.mem_append.1 hd with hd | hd
    · simp only [SimpleI.importDefs, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hd
      rcases hd with (hd | hd) | rfl | rfl
      · exact emitTys_expName _ _ d hd
      · exact emitTys_expName _ _ d hd
      · exact expName_noExport fun _ _ _ e => by cases e
      · exact expName_noExport fun _ _ _ e => by cases e
    · exact importsDefs_expName ps _ d hd

/-- **Every definition of `SimpleI.toRef` satisfies `ExpName`.** -/
theorem expName_toRefI (c : SimpleI) : ∀ d ∈ c.toRef, ExpName d := by
  intro d hd
  simp only [SimpleI.toRef, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_mapIdx] at hd
  rcases hd with ((((hd | rfl) | ⟨k, -, rfl⟩) | rfl | rfl) | hd)
  · exact importsDefs_expName _ _ d hd
  · exact expName_noExport fun _ _ _ e => by cases e
  · exact expName_noExport fun _ _ _ e => by cases e
  · exact expName_noExport fun _ _ _ e => by cases e
  · exact expName_noExport fun _ _ _ e => by cases e
  · exact exportsDefsAt_expName _ _ _ _ _ _ d hd

/-! ## The nested instantiations, with their export maps -/

section Nested

variable {Pf : Silmaril.Wasm.Numerics.Profile} {σ : Type}

/-- **The function export `j` of an export map of functions and generated type names is found
by name**, when the function exports are `fb + i` for the export `i` of `xs`, the names of `xs`
are distinct and not generated. -/
theorem lookup_funcExportL {es : Exports (core3P Pf)} (h : TagOrFunc es) {xs : List SimpleExport}
    {fb : Nat} (hx : funcExports es = xs.mapIdx fun i x => (x.name, ⟨fb + i⟩))
    (hnd : (xs.map (·.name)).Nodup) (j : Nat) (hj : j < xs.length)
    (hn : ∀ k, xs[j].name ≠ tag "t" k) :
    lookupExport? es xs[j].name = some (.func ⟨fb + j⟩) := by
  rw [lookup_of_tagOrFunc h hn, hx]
  have e := lookup_mapIdx_val (·.name) (fun i => (⟨i⟩ : FuncId)) fb xs j hj hnd
  rw [e]
  rfl

/-- **The nested instantiation of an import-free simple component** (`instantiateCall_simple`),
with an export map of functions and generated type names. -/
theorem instantiateCall_simple' {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst}
    (hF : CoreFacts c I cs ci) (outer : List (Frame (core3P Pf)))
    (cfg : Machine.Config (core3P Pf) σ)
    (hcore : cfg.store.core = (core3P Pf).empty _) (hfuncs : cfg.store.funcs = []) :
    ∃ es, funcExports es = exportMap c ∧ TagOrFunc es ∧
      TRuns (instantiateCallProg ⟨c.toRef, outer⟩ [] : P (core3P Pf) σ (Ret (core3P Pf))) cfg
        (.items es)
        (nestCfg cs cfg (fun k => I.addrs.getD k 0) c) := by
  obtain ⟨sc', hr, hx, -⟩ := toRefDefs_run (R := callRecurse)
    (inst := nextInst cfg.store) (outer := outer)
    (args := []) hF { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store }
    hcore hfuncs
  have hmap : funcExports sc'.exports = exportMap c := by
    rw [hx, exportMap]
    simp only [Nat.zero_add]
  have ht : TagOrFunc sc'.exports :=
    SRuns.rets (Q := fun sc : Scope (core3P Pf) => TagOrFunc sc.exports) hr (foldlM_rets (E := core3P Pf) (R := callRecurse) (inst := nextInst cfg.store) (outer := outer)
      (args := []) c.toRef {} (expName_toRef c) TagOrFunc.nil)
  refine ⟨sc'.exports, hmap, ht, ?_⟩
  unfold instantiateCallProg instantiateClosure instantiateComponent
  refine TRuns.bind (f := fun es => Pure.pure (Ret.items es)) ?_ (TRuns.pure _ _)
  have hr' : TRuns (List.foldlM (instantiateDef callRecurse (nextInst cfg.store) outer []) {}
      c.toRef) { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store } sc'
      (nestCfg cs cfg (fun k => I.addrs.getD k 0) c) := hr
  exact (TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} cfg).bind
    (TRuns.bind (a := sc') (b := sc'.exports) hr' (TRuns.pure _ _))

/-- **The nested instantiation of a simple component with imports over a shared store**
(`instantiateCall_simpleI`), with an export map of functions and generated type names. -/
theorem instantiateCall_simpleI' {c : SimpleI} (hc : c.Good) (har : c.Arity)
    {cs₀ : (core3P Pf).Store (CanonHost (core3P Pf))} {fid : Nat → FuncId} {addr : Nat → Nat}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst}
    (outer : List (Frame (core3P Pf))) (vs : Exports (core3P Pf))
    (cfg : Machine.Config (core3P Pf) σ) {fb : Nat}
    (hF : CoreFactsL c cs₀ (nextInst cfg.store) fid addr cs ci)
    (hcore : cfg.store.core = cs₀) (hfb : cfg.store.funcs.length = fb)
    (hb : ImportsBound c vs fid cfg.store) :
    ∃ es, funcExports es = c.exports.mapIdx (fun i x => (x.name, ⟨fb + i⟩)) ∧ TagOrFunc es ∧
      TRuns (instantiateCallProg ⟨c.toRef, outer⟩ vs : P (core3P Pf) σ (Ret (core3P Pf))) cfg
        (.items es)
        { cfg with store := nestStoreI cs cfg.store addr (nextInst cfg.store) c } := by
  obtain ⟨sc', hr, hx⟩ := toRefDefsL_run (R := callRecurse) (inst := nextInst cfg.store)
    (outer := outer) (args := vs) hc har hF
    { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store } hcore hfb hb
  have ht : TagOrFunc sc'.exports :=
    SRuns.rets (Q := fun sc : Scope (core3P Pf) => TagOrFunc sc.exports) hr (foldlM_rets (E := core3P Pf) (R := callRecurse) (inst := nextInst cfg.store) (outer := outer)
      (args := vs) c.toRef {} (expName_toRefI c) TagOrFunc.nil)
  refine ⟨sc'.exports, hx, ht, ?_⟩
  unfold instantiateCallProg instantiateClosure instantiateComponent
  refine TRuns.bind (f := fun es => Pure.pure (Ret.items es)) ?_ (TRuns.pure _ _)
  exact (TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} cfg).bind
    (TRuns.bind (a := sc') (b := sc'.exports) hr (TRuns.pure _ _))

end Nested

end Silmaril.Proofs.Wasm.Component.Reference
