module

public import Silmaril.Wasm.Wac.TypeOfW.Defs

/-!
# The inference of `TypeOf` simulates the world decoder on world-shaped components

Step by step: each declaration's inference step (`runDecl`) changes the decoder scope `sc` as
the world decoder's step (`stepD`, one step of `decCDecls`) does, and appends the same import
or export. Then `ofSecs` of a world-shaped component is the inference of its declarations.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.TypeOf

open Silmaril.Wasm Silmaril.Wasm.Component.Binary

namespace W

/-- One step of the world decoder. -/
def stepD : ComponentDecl → Externs → Externs → Bridge.DM (Externs × Externs)
  | .import n d, is, es => do
    let k ← Bridge.decExtern n.name d
    pure (is ++ [(n.name, k)], es)
  | .inst d, is, es => do
    let es ← Bridge.decIDecl d es
    pure (is, es)

theorem decCDecls_cons (d : ComponentDecl) (ds : List ComponentDecl) (is es : Externs) :
    Bridge.decCDecls (d :: ds) is es = stepD d is es >>= fun p => Bridge.decCDecls ds p.1 p.2 := by
  cases d <;> simp [Bridge.decCDecls, stepD]

theorem ok_bindE {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem err_bindE {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

theorem liftD_ok {α : Type} {m : Bridge.DM α} {s : TS} {a : α} {sc : Bridge.DScope}
    (h : m.run s.sc = .ok (a, sc)) : (liftD m).run s = .ok (a, { s with sc := sc }) := by
  simp only [StateT.run] at h
  simp [liftD, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, h,
    set, StateT.set, pure, StateT.pure, Except.bind, Except.pure]

/-- The relation of the two states after a step. -/
structure Rel (s : TS) (sc : Bridge.DScope) (is es : Externs) : Prop where
  sc : s.sc = sc
  imports : s.imports = is
  exports : s.exports = es

theorem pushKind_ok (k : Kind) (s : TS) :
    ∃ s', (pushKind k).run s = .ok ((), s') ∧ Rel s' s.sc s.imports s.exports := by
  cases k <;> exact ⟨_, rfl, ⟨rfl, rfl, rfl⟩⟩

theorem import_sim {n : ExternName} {d : ExternDesc} {s : TS} {r : Externs × Externs}
    {sc' : Bridge.DScope} (h : (stepD (.import n d) s.imports s.exports).run s.sc = .ok (r, sc')) :
    ∃ s', (runDecl (.import n d)).run s = .ok ((), s') ∧ Rel s' sc' r.1 r.2 := by
  cases hk : (Bridge.decExtern n.name d).run s.sc with
  | error e => simp [stepD, hk] at h
  | ok p =>
    obtain ⟨k, sc1⟩ := p
    simp [stepD, hk] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨s2, h2, hr⟩ := pushKind_ok k { s with sc := sc1 }
    refine ⟨{ s2 with imports := s2.imports ++ [(n.name, k)] }, ?_, ⟨hr.sc, ?_, hr.exports⟩⟩
    · simp only [runDecl, import_, StateT.run_bind, liftD_ok hk, ok_bindE, h2, StateT.run_modify]
      rfl
    · simp [hr.imports]

theorem type_sim {t : DefType} {s : TS} {r : Externs × Externs} {sc' : Bridge.DScope}
    (h : (stepD (.inst (.type t)) s.imports s.exports).run s.sc = .ok (r, sc')) :
    ∃ s', (runDecl (.inst (.type t))).run s = .ok ((), s') ∧ Rel s' sc' r.1 r.2 := by
  cases hk : (Bridge.decDefType t).run s.sc with
  | error e => simp [stepD, Bridge.decIDecl, hk, err_bindE] at h
  | ok p =>
    obtain ⟨ti, sc1⟩ := p
    simp [stepD, Bridge.decIDecl, hk, Bridge.pushTy] at h
    obtain ⟨rfl, rfl⟩ := h
    have hp : (Bridge.pushTy ti).run sc1 = .ok ((), { sc1 with types := sc1.types.push ti }) := rfl
    cases t with
    | resource => exact nomatch hk
    | _ =>
      refine ⟨{ s with sc := { sc1 with types := sc1.types.push ti } }, ?_, ⟨rfl, rfl, rfl⟩⟩
      simp only [runDecl, type_, StateT.run_bind, liftD_ok (decDefTypeT_ok hk), ok_bindE,
        liftD_ok (s := { s with sc := sc1 }) hp]

theorem coreType_sim {t : CoreType} {s : TS} {r : Externs × Externs} {sc' : Bridge.DScope}
    (h : (stepD (.inst (.coreType t)) s.imports s.exports).run s.sc = .ok (r, sc')) :
    ∃ s', (runDecl (.inst (.coreType t))).run s = .ok ((), s') ∧ Rel s' sc' r.1 r.2 := by
  simp [stepD, Bridge.decIDecl] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨s, rfl, ⟨rfl, rfl, rfl⟩⟩

/-- On the aliases both sides read alike, the inference's step is the decoder's step, or both
do nothing. -/
theorem alias_eq {a : Alias} (ha : AliasOk a) (sc : Bridge.DScope) :
    alias_ a = liftD (Bridge.decAlias a) ∨
      (alias_ a = pure () ∧ (Bridge.decAlias a).run sc = .ok ((), sc)) := by
  obtain ⟨sort, target⟩ := a
  rcases ha with hs | ⟨hs, i, n, ht⟩ | ⟨k, hs⟩
  · simp only at hs; subst hs; exact .inl rfl
  · simp only at hs ht; subst hs ht; exact .inl rfl
  · simp only at hs; subst hs
    exact .inr ⟨rfl, by cases target <;> rfl⟩

theorem alias_sim {a : Alias} (ha : AliasOk a) {s : TS} {r : Externs × Externs}
    {sc' : Bridge.DScope}
    (h : (stepD (.inst (.alias a)) s.imports s.exports).run s.sc = .ok (r, sc')) :
    ∃ s', (runDecl (.inst (.alias a))).run s = .ok ((), s') ∧ Rel s' sc' r.1 r.2 := by
  cases hk : (Bridge.decAlias a).run s.sc with
  | error e => simp [stepD, Bridge.decIDecl, hk] at h
  | ok p =>
    obtain ⟨u, sc1⟩ := p
    simp [stepD, Bridge.decIDecl, hk] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases alias_eq ha s.sc with hl | ⟨hl, hd⟩
    · exact ⟨{ s with sc := sc1 }, by simp only [runDecl, hl, liftD_ok hk], ⟨rfl, rfl, rfl⟩⟩
    · rw [hd] at hk
      cases hk
      exact ⟨s, by simp only [runDecl, hl]; rfl, ⟨rfl, rfl, rfl⟩⟩

theorem export_sim {n : ExternName} {d : ExternDesc} {s : TS} {r : Externs × Externs}
    {sc' : Bridge.DScope}
    (h : (stepD (.inst (.export n d)) s.imports s.exports).run s.sc = .ok (r, sc')) :
    ∃ s', (runDecl (.inst (.export n d))).run s = .ok ((), s') ∧ Rel s' sc' r.1 r.2 := by
  cases hk : (Bridge.decExtern n.name d).run s.sc with
  | error e => simp [stepD, Bridge.decIDecl, hk] at h
  | ok p =>
    obtain ⟨k, sc1⟩ := p
    simp [stepD, Bridge.decIDecl, hk] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨s2, h2, hr⟩ := pushKind_ok k { s with sc := sc1 }
    refine ⟨{ s2 with exports := s2.exports ++ [(n.name, k)] }, ?_, ⟨hr.sc, hr.imports, ?_⟩⟩
    · simp only [runDecl, export_, StateT.run_bind, liftD_ok hk, ok_bindE, h2, StateT.run_modify]
      rfl
    · simp [hr.exports]

theorem step_sim {d : ComponentDecl} (hd : DeclOk d) {s : TS} {r : Externs × Externs}
    {sc' : Bridge.DScope} (h : (stepD d s.imports s.exports).run s.sc = .ok (r, sc')) :
    ∃ s', (runDecl d).run s = .ok ((), s') ∧ Rel s' sc' r.1 r.2 := by
  match d, hd with
  | .import n e, _ => exact import_sim h
  | .inst (.type t), _ => exact type_sim h
  | .inst (.coreType t), _ => exact coreType_sim h
  | .inst (.alias a), ha => exact alias_sim ha h
  | .inst (.export n e), _ => exact export_sim h

/-- **The simulation**: on declarations both read the same way, the inference reaches a state
with the decoder's scope, imports and exports. -/
theorem decls_sim : ∀ (ds : List ComponentDecl), (∀ d ∈ ds, DeclOk d) → ∀ (s : TS)
    {r : Externs × Externs} {sc' : Bridge.DScope},
    (Bridge.decCDecls ds s.imports s.exports).run s.sc = .ok (r, sc') →
    ∃ s', (ds.forM runDecl).run s = .ok ((), s') ∧ Rel s' sc' r.1 r.2
  | [], _, s, r, sc', h => by
    simp [Bridge.decCDecls] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨s, rfl, ⟨rfl, rfl, rfl⟩⟩
  | d :: ds, hok, s, r, sc', h => by
    rw [decCDecls_cons, StateT.run_bind] at h
    cases hs : (stepD d s.imports s.exports).run s.sc with
    | error e => rw [hs] at h; cases h
    | ok p =>
      rw [hs, ok_bindE] at h
      obtain ⟨s1, h1, hr1⟩ := step_sim (hok d (.head _)) hs
      rw [← hr1.imports, ← hr1.exports, ← hr1.sc] at h
      obtain ⟨s2, h2, hr2⟩ := decls_sim ds (fun x hx => hok x (.tail _ hx)) s1 h
      refine ⟨s2, ?_, hr2⟩
      show (runDecl d >>= fun _ => List.forM ds runDecl).run s = _
      rw [StateT.run_bind, h1, ok_bindE, h2]

/-! ## Sections as declarations -/

theorem forM_map {β : Type} (f : β → ComponentDecl) (g : β → TM Unit)
    (hg : ∀ x, runDecl (f x) = g x) : ∀ xs : List β, (xs.map f).forM runDecl = xs.forM g
  | [] => rfl
  | x :: xs => by
    show (runDecl (f x) >>= fun _ => (xs.map f).forM runDecl) = (g x >>= fun _ => xs.forM g)
    rw [hg, forM_map f g hg xs]

theorem forM_pure {β : Type} : ∀ xs : List β, xs.forM (fun _ => (pure () : TM Unit)) = pure ()
  | [] => rfl
  | x :: xs => by
    show ((pure () : TM Unit) >>= fun _ => xs.forM fun _ => (pure () : TM Unit)) = pure ()
    rw [pure_bind, forM_pure xs]

theorem export_desc {e : Silmaril.Wasm.Component.Binary.Export} {d : ExternDesc} (h : e.desc = some d) :
    export_ e = runDecl (.inst (.export e.name d)) := by
  obtain ⟨n, x, desc⟩ := e
  simp only at h
  subst h
  rfl

theorem exports_eq : ∀ (xs : List Silmaril.Wasm.Component.Binary.Export) (l : List ComponentDecl),
    xs.mapM (fun e => e.desc.map fun d => ComponentDecl.inst (.export e.name d)) = some l →
    xs.forM export_ = l.forM runDecl
  | [], l, h => by simp at h; subst h; rfl
  | e :: xs, l, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, ⟨d, hd, rfl⟩, l', hl', he⟩ := h
    cases he
    show (export_ e >>= fun _ => xs.forM export_) = (runDecl _ >>= fun _ => l'.forM runDecl)
    rw [export_desc hd, exports_eq xs l' hl']

theorem ofSec_eq (s : Section) {l : List ComponentDecl} (h : secDecls s = some l) :
    ofSec s = l.forM runDecl := by
  cases s with
  | imports xs => simp only [secDecls, Option.some.injEq] at h; subst h
                  exact (forM_map _ import_ (fun _ => rfl) xs).symm
  | types xs => simp only [secDecls, Option.some.injEq] at h; subst h
                exact (forM_map _ type_ (fun _ => rfl) xs).symm
  | aliases xs => simp only [secDecls, Option.some.injEq] at h; subst h
                  exact (forM_map _ alias_ (fun _ => rfl) xs).symm
  | coreTypes xs => simp only [secDecls, Option.some.injEq] at h; subst h
                    rw [forM_map _ (fun _ => pure ()) (fun _ => rfl) xs, forM_pure]; rfl
  | exports xs => exact exports_eq xs l h
  | custom => simp only [secDecls, Option.some.injEq] at h; subst h; rfl
  | coreModule => simp only [secDecls, Option.some.injEq] at h; subst h; rfl
  | coreInstances => simp only [secDecls, Option.some.injEq] at h; subst h; rfl
  | _ => simp [secDecls] at h

theorem forM_app : ∀ (l l' : List ComponentDecl),
    (l ++ l').forM runDecl = (l.forM runDecl >>= fun _ => l'.forM runDecl)
  | [], l' => by show _ = ((pure () : TM Unit) >>= _); rw [pure_bind]; rfl
  | d :: l, l' => by
    show (runDecl d >>= fun _ => (l ++ l').forM runDecl) =
      ((runDecl d >>= fun _ => l.forM runDecl) >>= fun _ => l'.forM runDecl)
    rw [forM_app l l', bind_assoc]

theorem ofSecs_eq : ∀ (ss : List Section) {ds : List ComponentDecl},
    worldDecls ss = some ds → ofSecs ss = ds.forM runDecl
  | [], ds, h => by simp [worldDecls] at h; subst h; rfl
  | s :: ss, ds, h => by
    simp only [worldDecls, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨_, ⟨l, hl, ls, hls, hw⟩, rfl⟩ := h
    cases hw
    show (ofSec s >>= fun _ => ofSecs ss) = _
    rw [ofSec_eq s hl, ofSecs_eq ss (ds := ls.flatten) (by simp [worldDecls, hls]),
      List.flatten_cons, forM_app]

end W

end Silmaril.Wasm.Wac.TypeOf
