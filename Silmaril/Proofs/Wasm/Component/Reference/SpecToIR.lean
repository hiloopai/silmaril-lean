module

public import Silmaril.Wasm.Component.Reference.Sound.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.Games
public import Silmaril.Wasm.Game.Instantiate.Thms
public import Silmaril.Wasm.Game.Adequacy.Thms
public import Silmaril.Wasm.Component.ABI.Thms

/-!
# The IR side of soundness: specification outcomes are IR plays

`specToIR : Simple.SpecToIR`: for a simple component `c`, every terminating outcome of the
canonical-ABI specification `exportSpec P c x vs` of an export call is a two-move play of
`c.toComp.den (modSem P)`. The play is assembled layer by layer through the IR's denotation
(`atSizes`, the export handler, `ext`, the core node, `core3Sem`).
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

/-! ## The outer layers -/

theorem den_of_denU {M : Type} [CoreModule M] (C : CoreSem M) (c : Comp M)
    {j : Nat} (hj : j < c.exports.length) (p : Payload) (A : Option Payload)
    (h : two (E := sigU) (F := sigU) (j, p) A ∈ c.denU C) :
    two (E := c.imports.sig) (F := sigN c.exports.length) (⟨j, hj⟩, p) A ∈ c.den C := by
  unfold Comp.den atSizes
  refine two_comp (q' := (j, p)) (a' := A) (two_comp_upper h) ?_
  exact four_ofHandler_call (h := narrowH c.exports.length) (k := fun r => .pure r) rfl rfl

/-! ## The export layer of a simple component -/

/-- The environment of a simple component's exports: the core instance on top of the empty
environment. -/
abbrev envS (C : CoreSem NumModule) (c : Simple) : Strategy sigU sigU :=
  ext 0 (Strategy.ofHandler (maskH 0)) (coreNode C 0 c.mod [])

theorem denU_toComp (C : CoreSem NumModule) (c : Simple) :
    c.toComp.denU C = (envS C c).comp
      (Strategy.ofHandler (exportsH c.mod.exports.length (c.toComp.exports))) := by
  simp only [Simple.toComp, Comp.denU, denNodes, Node.den, envAfter, Node.width,
    List.length_nil, Nat.zero_add, Comp.exports_mk]
  rfl

/-- The export handler on export `j` of a simple component. -/
theorem exportsH_toComp (c : Simple) {j : Nat} (hj : j < c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hcore : c.exports[j].core < c.mod.exports.length) :
    exportsH c.mod.exports.length c.toComp.exports (j, .vals vs) =
      match checkLower c.exports[j].ty.params vs with
      | none => .pure none
      | some xs => .call (c.exports[j].core, .flat xs)
          fun n => .pure (n.bind (Adapter.up (.lift c.exports[j].ty))) := by
  have hget : (c.toComp.exports.map Export.impl)[j]? =
      some ⟨[.lift c.exports[j].ty], .call c.exports[j].core⟩ := by
    simp [Simple.toComp, hj]
  simp only [exportsH, implsH, hget, Impl.prog, runChain, Adapter.down]
  cases checkLower c.exports[j].ty.params vs with
  | none => rfl
  | some xs => simp [Target.prog, hcore, Prog.bind]

/-- A trap of the argument check. -/
theorem denU_trap (C : CoreSem NumModule) (c : Simple) {j : Nat} (hj : j < c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (hcore : c.exports[j].core < c.mod.exports.length)
    (hl : checkLower c.exports[j].ty.params vs = none) :
    two (E := sigU) (F := sigU) (j, .vals vs) none ∈ c.toComp.denU C := by
  rw [denU_toComp]
  refine two_comp_upper (two_ofHandler_pure ?_)
  rw [exportsH_toComp c hj vs hcore, hl]

/-- A call of the core export through the environment. -/
theorem denU_call (C : CoreSem NumModule) (c : Simple) {j : Nat} (hj : j < c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (hcore : c.exports[j].core < c.mod.exports.length) {xs : List Flat}
    (hl : checkLower c.exports[j].ty.params vs = some xs) {R : Option Payload}
    (hR : two (E := sigU) (F := sigU) (c.exports[j].core, .flat xs) R ∈ envS C c) :
    two (E := sigU) (F := sigU) (j, .vals vs) (R.bind (Adapter.up (.lift c.exports[j].ty))) ∈
      c.toComp.denU C := by
  rw [denU_toComp]
  refine two_comp hR (four_ofHandler_call
    (k := fun (n : Option Payload) => .pure (n.bind (Adapter.up (.lift c.exports[j].ty)))) ?_ rfl)
  rw [exportsH_toComp c hj vs hcore, hl]

/-! ## The environment layer -/

/-- A call of function `k` of the environment is a call of export `k` of the core instance. -/
theorem envS_of_sem (C : CoreSem NumModule) (c : Simple) {i : Nat}
    (hi : i < c.mod.exports.length) (p : Payload) {R : Option Payload}
    (h : two (E := CoreIface.sig (CoreModule.imports c.mod)) (F := CoreIface.sig (CoreModule.exports c.mod))
      (⟨i, hi⟩, p) R ∈ C.sem c.mod) :
    two (E := sigU) (F := sigU) (i, p) R ∈ envS C c := by
  unfold envS ext
  refine two_comp_upper (two_comp (F := sigU ⊕ₛ sigU) (q' := Sum.inr (i - 0, p)) (a' := R)
    (two_pair_inr ?_) ?_)
  · unfold coreNode
    refine two_comp_upper (two_comp (q' := (⟨i, hi⟩, p)) (a' := R) h ?_)
    refine four_ofHandler_call (h := widenH (CoreModule.exports c.mod).length)
      (q := (i - 0, p)) (q' := (⟨i, hi⟩, p)) (k := fun (r : Option Payload) => .pure r) ?_ rfl
    exact dite_eq_left (show i < (CoreModule.exports c.mod).length from hi)
  · refine four_ofHandler_call (h := splitH 0) (q := (i, p)) (q' := Sum.inr (i - 0, p))
      (k := fun (r : Option Payload) => .pure r) ?_ rfl
    simp only [splitH, Nat.not_lt_zero, ite_false]
    rfl

/-! ## The core layer -/

/-- The upper moves of a play, as moves over another lower interface. -/
def upMoves {E F G : Sig.{0}} : List (Move E G) → List (Move F G)
  | [] => []
  | .inl _ :: p => upMoves p
  | .inr c :: p => .inr c :: upMoves p

/-- An interaction with no events at either inner interface is its upper play. -/
theorem zip_eq_of_isEmpty {E F G : Sig.{0}} [IsEmpty E.Op] [IsEmpty F.Op]
    {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)} (h : Zip s t p) :
    t = upMoves p := by
  induction h with
  | nil => rfl
  | left a _ _ => exact isEmptyElim (match a with | .ask m => m | .ans m _ => m : E.Op)
  | right c _ ih => rw [ih]; rfl
  | sync b _ _ => exact isEmptyElim (match b with | .ask m => m | .ans m _ => m : F.Op)

instance : IsEmpty (Sig.empty.{0}).Op := ⟨fun m => PEmpty.elim m⟩

/-- An instance without imports answers as its closed program does. -/
theorem two_strategy_of_responds {I : Silmaril.Wasm.Game.ScalarInstance} (hI : I.imports = [])
    {P : Profile} {s : Silmaril.Wasm.Execution.Core.Store Nat} {K : Silmaril.Wasm.Game.Env I.E}
    {f : I.F.Op} {w : I.F.Ar f} (h : Silmaril.Wasm.Game.Responds (I.closedWith P s K) f w) :
    two f w ∈ I.strategy P s := by
  obtain ⟨u, _, t, ht, hz⟩ := h
  have : IsEmpty I.E.Op := ⟨fun e => absurd e.1.isLt (by simp [hI])⟩
  have he : t = two f w := zip_eq_of_isEmpty hz
  exact he ▸ ht

/-- With no imports, the host induced by any environment is the empty host. -/
theorem hostOf_nil {I : Silmaril.Wasm.Game.ScalarInstance} (hI : I.imports = [])
    (K : Silmaril.Wasm.Game.Env I.E) :
    Silmaril.Wasm.Game.hostOf I.imports K = Silmaril.Wasm.SingleThreaded.Det.noHost := by
  funext h s args out
  apply propext
  constructor
  · rintro ⟨e, _, _⟩
    exact absurd e.1.isLt (by simp [hI])
  · intro hf
    exact hf.elim

/-- Instances of a module are unique. -/
theorem NumModule.IsInst.unique {m : NumModule} {I J : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) (hJ : m.IsInst J) : I = J := by
  obtain ⟨⟨mt, hmt⟩, _, _⟩ := hI
  obtain ⟨⟨mt', hmt'⟩, _, _⟩ := hJ
  have hv : some mt = some mt' := hmt.valid.symm.trans hmt'.valid
  cases Option.some.inj hv
  exact Silmaril.Wasm.Game.IsInstance.unique hmt hmt'

theorem modSem_sem {P : Profile} {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) :
    (modSem P).sem m = (core3Sem P).sem
      { inst := I, imports := [], exports := m.exports, imports_eq := hI.2.1,
        exports_eq := hI.2.2 } := by
  have hex : ∃ J, m.IsInst J := ⟨I, hI⟩
  have key : ∀ J (hJ : m.IsInst J), (core3Sem P).sem
      { inst := J, imports := [], exports := m.exports, imports_eq := hJ.2.1,
        exports_eq := hJ.2.2 } = (core3Sem P).sem
      { inst := I, imports := [], exports := m.exports, imports_eq := hI.2.1,
        exports_eq := hI.2.2 } := by
    intro J hJ
    obtain rfl := NumModule.IsInst.unique hJ hI
    rfl
  simp only [modSem, dite_eq_left hex]
  exact key _ hex.choose_spec

/-- Lowered values have the flattened types. -/
theorem lowerList_types : ∀ (ts : List ValTy) (vs : List Silmaril.Wasm.Component.Val),
    ValTy.checkList ts vs = true → (ValTy.lowerList ts vs).map (·.type) = ValTy.flatList ts
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [ValTy.checkList] at h
  | _ :: _, [], h => by simp [ValTy.checkList] at h
  | t :: ts, v :: vs, h => by
    have h' : t.check v = true ∧ ValTy.checkList ts vs = true := by
      simpa only [ValTy.checkList, Bool.and_eq_true] using h
    simp only [ValTy.lowerList, ValTy.flatList, List.map_append, ValTy.lower_types t v h'.1,
      lowerList_types ts vs h'.2]

/-- Flat values have their own scalar types. -/
theorem forall₂_hasVal_ofFlat (xs : List Flat) :
    List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (xs.map fun x => .num x.type)
      (xs.map Silmaril.Wasm.SingleThreaded.ofFlat) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons ⟨x.bits, rfl⟩ ih

/-- The payload of the answer to a result. -/
theorem answerPayload_of_ofResult? {ft : Silmaril.Wasm.Game.FnType}
    {res : Silmaril.Wasm.Execution.Core.Result} {w : Silmaril.Wasm.Game.Answer ft}
    (h : Silmaril.Wasm.Game.Answer.ofResult? ft res = some w) :
    answerPayload w = (match res with
      | .values vs => vs.mapM Silmaril.Wasm.SingleThreaded.toFlat?
      | _ => none).map .flat := by
  cases res with
  | values vs =>
    unfold Silmaril.Wasm.Game.Answer.ofResult? at h
    dsimp only at h
    split_ifs at h with hf
    cases h
    rfl
  | trap =>
    have hw : w = .trap := by simpa [Silmaril.Wasm.Game.Answer.ofResult?] using h.symm
    rw [hw]
    rfl
  | throw a =>
    have hw : w = .throw a := by simpa [Silmaril.Wasm.Game.Answer.ofResult?] using h.symm
    rw [hw]
    rfl

/-- **The core layer.** A Core run of core export `i` of the instance of `m`, on flat values of
its parameter types, is a play of `modSem P` on `m` with the payload of the result. -/
theorem sem_of_run {P : Profile} {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) {i : Nat} (hi : i < m.exports.length) {xs : List Flat}
    (hxs : xs.map (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) =
      (m.exports[i].2.params.map Silmaril.Wasm.Game.ScalarType.num))
    {c' : Silmaril.Wasm.Execution.Core.Config Nat} {res : Silmaril.Wasm.Execution.Core.Result}
    (run : Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (Silmaril.Wasm.Execution.Core.invoke I.store (I.addrs.getD i 0)
        (xs.map Silmaril.Wasm.SingleThreaded.ofFlat)) c')
    (final : c'.code = res.toAdmin) :
    two (E := CoreIface.sig (CoreModule.imports m)) (F := CoreIface.sig (CoreModule.exports m))
      (⟨i, hi⟩, .flat xs)
      ((match res with
        | .values vs => vs.mapM Silmaril.Wasm.SingleThreaded.toFlat?
        | _ => none).map .flat) ∈ (modSem P).sem m := by
  let n : NumInstance :=
    { inst := I, imports := [], exports := m.exports, imports_eq := hI.2.1,
      exports_eq := hI.2.2 }
  let j : Fin I.exports.length := Fin.cast n.exports_length ⟨i, hi⟩
  have hparams : (I.exports.get j).params = xs.map fun x => .num x.type := by
    have hj : I.exports.get j = fnOf m.exports[i].2 := by
      simp only [List.get_eq_getElem, j, Fin.val_cast]
      simp only [hI.2.2, List.getElem_map]
    rw [hj, hxs]
    rfl
  have htyped : typed? (I.exports.get j).params (xs.map Silmaril.Wasm.SingleThreaded.ofFlat) =
      some ⟨xs.map Silmaril.Wasm.SingleThreaded.ofFlat, hparams ▸ forall₂_hasVal_ofFlat xs⟩ := by
    unfold typed?
    rw [dite_eq_left (hparams ▸ forall₂_hasVal_ofFlat xs)]
  let f : I.F.Op := ⟨j, ⟨xs.map Silmaril.Wasm.SingleThreaded.ofFlat,
    hparams ▸ forall₂_hasVal_ofFlat xs⟩⟩
  have hok : I.Ok := hI.1.choose_spec.ok
  have run' : Silmaril.Wasm.Execution.Core.Steps P
      (Silmaril.Wasm.Game.hostOf I.imports (Silmaril.Wasm.Game.Env.silent _))
      (Silmaril.Wasm.Execution.Core.invoke I.store (I.addr f.1) f.2.1) c' := by
    rw [hostOf_nil hI.2.1]
    exact run
  obtain ⟨w, hw, hresp⟩ := Silmaril.Wasm.Game.ScalarInstance.answer_of_run hok
    (fun _ _ h => by cases h) run' final
  rw [modSem_sem hI, ← answerPayload_of_ofResult? hw]
  refine two_comp_upper (two_comp (q' := f) (a' := w) (two_strategy_of_responds hI.2.1 hresp) ?_)
  refine four_ofHandler_call (h := exportH n) (q := (⟨i, hi⟩, .flat xs)) (q' := f)
    (k := fun a => .pure (answerPayload a)) ?_ rfl
  unfold exportH
  dsimp only
  erw [htyped]

/-! ## The theorem -/

/-- The answer through the lift adapter of a lifted core outcome. -/
theorem irObs_of_answer {k : Nat} {σ : Strategy (sigN 0) (sigN k)} {j : Fin k}
    {vs : List Silmaril.Wasm.Component.Val} (ft : FuncTy) (r : Option (List Flat))
    (h : two (j, .vals vs) ((r.map Payload.flat).bind (Adapter.up (.lift ft))) ∈ σ) :
    IRObs σ j vs (liftOutcome ft r) := by
  cases r with
  | none => exact h
  | some ys =>
    cases hl : liftArgs ft.results ys with
    | none =>
      have h' : two (j, .vals vs) none ∈ σ := by
        simpa [Adapter.up, hl] using h
      simpa [liftOutcome, hl, IRObs] using h'
    | some ws =>
      have h' : two (j, .vals vs) (some (.vals ws)) ∈ σ := by
        simpa [Adapter.up, hl] using h
      simp only [liftOutcome, hl, IRObs]
      exact ⟨ws, rfl, h'⟩

/-- The checked lowering of well-typed values. -/
theorem checkLower_eq {ts : List ValTy} {vs : List Silmaril.Wasm.Component.Val} {xs : List Flat}
    (hl : checkLower ts vs = some xs) :
    ValTy.checkList ts vs = true ∧ xs = ValTy.lowerList ts vs := by
  unfold checkLower at hl
  split_ifs at hl with h
  exact ⟨h, (Option.some.inj hl).symm⟩

/-- The lowered arguments have the parameter types of the lifted core export. -/
theorem lowered_types {ft : FuncTy} {vs : List Silmaril.Wasm.Component.Val} {xs : List Flat}
    (hl : checkLower ft.params vs = some xs) :
    xs.map (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) =
      ft.flat.params.map Silmaril.Wasm.Game.ScalarType.num := by
  obtain ⟨hck, rfl⟩ := checkLower_eq hl
  show (ValTy.lowerList ft.params vs).map (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) =
    (ValTy.flatList ft.params).map Silmaril.Wasm.Game.ScalarType.num
  rw [← lowerList_types _ _ hck, List.map_map]
  rfl

/-- A core outcome of export `j` is an IR play. -/
theorem irObs_of_coreOut {P : Profile} {c : Simple} {j : Fin c.exports.length} {nm : String}
    (hcore : c.mod.exports[c.exports[j].core]? = some (nm, c.exports[j].ty.flat))
    {vs : List Silmaril.Wasm.Component.Val} {xs : List Flat}
    (hl : checkLower c.exports[j].ty.params vs = some xs) {r : Option (List Flat)}
    (hr : r ∈ coreOut P c.mod c.exports[j].core xs) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ vs (liftOutcome c.exports[j].ty r) := by
  obtain ⟨I, hI, c', res, run, final, rfl⟩ := hr
  have hlt : c.exports[j].core < c.mod.exports.length := (List.getElem?_eq_some_iff.mp hcore).1
  have hget : c.mod.exports[c.exports[j].core] = (nm, c.exports[j].ty.flat) :=
    (List.getElem?_eq_some_iff.mp hcore).2
  have hxs : xs.map (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) =
      (c.mod.exports[c.exports[j].core].2.params.map Silmaril.Wasm.Game.ScalarType.num) := by
    rw [hget]
    exact lowered_types hl
  have h₁ := sem_of_run hI hlt hxs run final
  have h₂ := envS_of_sem (modSem P) c hlt _ h₁
  exact irObs_of_answer _ _ (den_of_denU (modSem P) c.toComp _ _ _
    (denU_call (modSem P) c j.isLt vs hlt hl h₂))

/-- **The IR side of soundness.** Every terminating outcome of the canonical-ABI specification
of an export call of a simple component is a play of its IR denotation over `modSem P`. -/
theorem specToIR : Simple.SpecToIR := by
  intro P c hc j vs b hb
  obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem j.isLt)
  have hlt : c.exports[j].core < c.mod.exports.length := (List.getElem?_eq_some_iff.mp hcore).1
  unfold exportSpec at hb
  split at hb
  next hl =>
    have hb' : b = .traps := hb
    rw [hb']
    exact den_of_denU (modSem P) c.toComp _ _ _ (denU_trap (modSem P) c j.isLt vs hlt hl)
  next xs hl =>
    rcases hb with ⟨r, hr, rfl⟩ | ⟨rfl, _⟩
    · exact irObs_of_coreOut hcore hl hr
    · trivial

end Silmaril.Proofs.Wasm.Component.Reference
