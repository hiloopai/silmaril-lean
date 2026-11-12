module

public import Silmaril.Wasm.Wac.TypeOfX.Defs

/-!
# `TypeOf.typeOf` reports the component's own import and export names

`Track m di de`: running `m` appends exactly the names `di` to the inferred imports and `de`
to the inferred exports. Every step of the inference is tracked: import and export sections
append their names, every other step leaves both lists alone (a nested component is inferred
in its own state, of which only the nominal table is kept).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.TypeOf

open Silmaril.Wasm Silmaril.Wasm.Component.Binary

namespace Names

/-- Running `m` appends the names `di` to the imports and `de` to the exports. -/
def Track {α : Type} (m : TM α) (di de : List String) : Prop :=
  ∀ s r, m.run s = .ok r →
    r.2.imports.map (·.1) = s.imports.map (·.1) ++ di ∧ r.2.exports.map (·.1) = s.exports.map (·.1) ++ de

theorem track_pure {α : Type} (a : α) : Track (pure a : TM α) [] [] := by
  intro s r h
  have hr : (a, s) = r := Except.ok.inj h
  rw [← hr]
  exact ⟨(List.append_nil _).symm, (List.append_nil _).symm⟩

theorem track_throw {α : Type} (e : String) : Track (throw e : TM α) [] [] := by
  intro s r h
  exact nomatch h

theorem track_bind {α β : Type} {m : TM α} {f : α → TM β} {a b c d : List String}
    (hm : Track m a b) (hf : ∀ x, Track (f x) c d) : Track (m >>= f) (a ++ c) (b ++ d) := by
  intro s r h
  have hrun : (m >>= f).run s = (m.run s >>= fun p => (f p.1).run p.2) := rfl
  rw [hrun] at h
  cases hm' : m.run s with
  | error e => rw [hm'] at h; exact nomatch h
  | ok p =>
    have hf' : (f p.1).run p.2 = .ok r := by rw [hm'] at h; exact h
    obtain ⟨h1, h2⟩ := hm s p hm'
    obtain ⟨h3, h4⟩ := hf p.1 p.2 r hf'
    exact ⟨by rw [h3, h1, List.append_assoc], by rw [h4, h2, List.append_assoc]⟩

theorem track_bind0 {α β : Type} {m : TM α} {f : α → TM β}
    (hm : Track m [] []) (hf : ∀ x, Track (f x) [] []) : Track (m >>= f) [] [] :=
  track_bind hm hf

theorem track_get : Track (get : TM TS) [] [] := by
  intro s r h
  have hr : (s, s) = r := Except.ok.inj h
  rw [← hr]
  exact ⟨(List.append_nil _).symm, (List.append_nil _).symm⟩

theorem track_modify {f : TS → TS} (hi : ∀ s, (f s).imports = s.imports)
    (he : ∀ s, (f s).exports = s.exports) : Track (modify f : TM Unit) [] [] := by
  intro s r h
  have hr : ((), f s) = r := Except.ok.inj h
  rw [← hr]
  exact ⟨by rw [hi, List.append_nil], by rw [he, List.append_nil]⟩

/-- A step that only reads the state and then writes back that state with another type
scope. -/
theorem track_scope {α : Type} {m : TM α}
    (h : ∀ s r, m.run s = .ok r → ∃ sc, r.2 = { s with sc := sc }) : Track m [] [] := by
  intro s r hr
  obtain ⟨sc, hsc⟩ := h s r hr
  rw [hsc]
  exact ⟨(List.append_nil _).symm, (List.append_nil _).symm⟩

theorem track_liftD {α : Type} (m : Bridge.DM α) : Track (liftD m) [] [] := by
  refine track_scope fun s r h => ?_
  cases hm : m s.sc with
  | error e =>
    have h' : (Except.error e : Except String (α × TS)) = .ok r := by
      simp [liftD, hm, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        pure, Except.bind, Except.pure] at h
      exact h
    exact nomatch h'
  | ok p =>
    have h' : (Except.ok (p.1, { s with sc := p.2 }) : Except String (α × TS)) = .ok r := by
      simpa [liftD, hm, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, pure, StateT.pure, Except.bind, Except.pure] using h
    exact ⟨p.2, by rw [← Except.ok.inj h']⟩

theorem track_nested {α : Type} (m : TM α) : Track (nested m) [] [] := by
  refine track_scope fun s r h => ?_
  cases hm : m { sc := { outer := s.sc.types :: s.sc.outer, nom := s.sc.nom } } with
  | error e =>
    have h' : (Except.error e : Except String (α × TS)) = .ok r := by
      simp [nested, hm, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        pure, Except.bind, Except.pure] at h
      exact h
    exact nomatch h'
  | ok p =>
    have h' : (Except.ok (p.1, { s with sc := { s.sc with nom := p.2.sc.nom } }) :
        Except String (α × TS)) = .ok r := by
      simpa [nested, hm, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set,
        StateT.set, pure, StateT.pure, Except.bind, Except.pure] using h
    exact ⟨_, by rw [← Except.ok.inj h']⟩

theorem track_congr {α : Type} {m : TM α} {a b a' b' : List String} (h : Track m a b)
    (ha : a = a') (hb : b = b') : Track m a' b' := by
  rw [← ha, ← hb]; exact h

theorem track_pushFunc (f : Wit.Binary.Sig) : Track (pushFunc f) [] [] :=
  track_modify (fun _ => rfl) (fun _ => rfl)

theorem track_pushInst (es : Externs) : Track (pushInst es) [] [] :=
  track_modify (fun _ => rfl) (fun _ => rfl)

theorem track_pushComp (c : Externs × Externs) : Track (pushComp c) [] [] :=
  track_modify (fun _ => rfl) (fun _ => rfl)

/-- Discharge `Track m [] []` for a step built from the tracked primitives. -/
macro "track_tac" : tactic => `(tactic| repeat (first
  | exact track_pure _ | exact track_throw _ | exact track_get | exact track_liftD _
  | exact track_nested _ | exact track_pushFunc _ | exact track_pushInst _
  | exact track_pushComp _ | refine track_bind0 ?_ (fun _ => ?_) | split))

theorem track_funcAt (i : Nat) : Track (funcAt i) [] [] := by unfold funcAt; track_tac
theorem track_instAt (i : Nat) : Track (instAt i) [] [] := by unfold instAt; track_tac
theorem track_compAt (i : Nat) : Track (compAt i) [] [] := by unfold compAt; track_tac
theorem track_pushKind (k : Kind) : Track (pushKind k) [] [] := by unfold pushKind; track_tac

/-- `track_tac` with the lookups. -/
macro "track_tac2" : tactic => `(tactic| repeat (first
  | exact track_funcAt _ | exact track_instAt _ | exact track_compAt _
  | exact track_pure _ | exact track_throw _ | exact track_liftD _ | exact track_pushFunc _
  | exact track_pushInst _ | exact track_pushComp _ | refine track_bind0 ?_ (fun _ => ?_) | split))

theorem track_itemKind (n : String) (x : SortIdx) (alloc : Bool) :
    Track (itemKind n x alloc) [] [] := by
  unfold itemKind; track_tac2

theorem track_alias (a : Alias) : Track (alias_ a) [] [] := by unfold alias_; track_tac2

theorem track_canon (c : Canon) : Track (canon_ c) [] [] := by unfold canon_; track_tac
theorem track_type (t : DefType) : Track (type_ t) [] [] := by unfold type_; track_tac

theorem track_forM {β : Type} (f : β → TM Unit) (g h : β → List String)
    (hf : ∀ x, Track (f x) (g x) (h x)) :
    ∀ xs : List β, Track (xs.forM f) (xs.flatMap g) (xs.flatMap h)
  | [] => track_pure ()
  | x :: xs => track_congr (track_bind (hf x) fun _ => track_forM f g h hf xs)
      (List.flatMap_cons ..).symm (List.flatMap_cons ..).symm

theorem track_forM0 {β : Type} (f : β → TM Unit) (hf : ∀ x, Track (f x) [] []) (xs : List β) :
    Track (xs.forM f) [] [] :=
  track_congr (track_forM f (fun _ => []) (fun _ => []) hf xs) (by simp) (by simp)

theorem track_mapM {β γ : Type} (f : β → TM γ) (hf : ∀ x, Track (f x) [] []) :
    ∀ xs : List β, Track (xs.mapM f) [] []
  | [] => track_pure []
  | x :: xs => by
    rw [List.mapM_cons]
    exact track_bind0 (hf x) fun _ => track_bind0 (track_mapM f hf xs) fun _ => track_pure _

theorem track_instance (e : InstanceExpr) : Track (instance_ e) [] [] := by
  cases e with
  | instantiate c _ => unfold instance_; exact track_bind0 (track_compAt c) fun _ => track_pushInst _
  | exports es =>
    unfold instance_
    exact track_bind0 (track_mapM _ (fun _ => track_bind0 (track_itemKind _ _ _)
      fun _ => track_pure _) es) fun _ => track_pushInst _

theorem track_import (i : Import) : Track (import_ i) [i.name.name] [] := by
  unfold import_
  refine track_congr (track_bind (track_liftD _) fun k =>
    track_bind (c := [i.name.name]) (d := []) (track_pushKind k) fun _ => ?_) (by simp) (by simp)
  intro s r h
  have hr : ((), { s with imports := s.imports ++ [(i.name.name, k)] }) = r := Except.ok.inj h
  rw [← hr]
  exact ⟨by simp, (List.append_nil _).symm⟩

theorem track_appendExport (n : String) (k : Kind) :
    Track (modify fun s : TS => { s with exports := s.exports ++ [(n, k)] }) [] [n] := by
  intro s r h
  have hr : ((), { s with exports := s.exports ++ [(n, k)] }) = r := Except.ok.inj h
  rw [← hr]
  exact ⟨(List.append_nil _).symm, by simp⟩

theorem track_export (e : Export) : Track (export_ e) [] [e.name.name] := by
  unfold export_
  split
  · exact track_congr (track_bind (track_liftD _) fun k => track_bind (track_pushKind k) fun _ =>
      track_bind (track_pure k) fun k => track_appendExport _ k) (by simp) (by simp)
  · exact track_congr (track_bind (track_itemKind _ _ _) fun k => track_appendExport _ k)
      (by simp) (by simp)

theorem flatMap_single {β : Type} (f : β → String) :
    ∀ xs : List β, xs.flatMap (fun x => [f x]) = xs.map f
  | [] => rfl
  | x :: xs => by rw [List.flatMap_cons, List.map_cons, flatMap_single f xs]; rfl

theorem track_ofSec (s : Section) : Track (ofSec s) (importNamesOf [s]) (exportNamesOf [s]) := by
  cases s with
  | imports xs =>
    rw [ofSec]
    exact track_congr (track_forM import_ (fun i => [i.name.name]) (fun _ => []) track_import xs)
      (by simp [importNamesOf, flatMap_single]) (by simp [exportNamesOf])
  | exports xs =>
    rw [ofSec]
    exact track_congr (track_forM export_ (fun _ => []) (fun e => [e.name.name]) track_export xs)
      (by simp [importNamesOf]) (by simp [exportNamesOf, flatMap_single])
  | component c =>
    rw [ofSec]
    exact track_bind0 (track_nested _) fun _ => track_pushComp _
  | instances xs => rw [ofSec]; exact track_forM0 _ track_instance xs
  | aliases xs => rw [ofSec]; exact track_forM0 _ track_alias xs
  | types xs => rw [ofSec]; exact track_forM0 _ track_type xs
  | canons xs => rw [ofSec]; exact track_forM0 _ track_canon xs
  | custom _ _ | coreModule _ | coreInstances _ | coreTypes _ | start _ | values _ =>
    rw [ofSec]; track_tac

theorem track_ofSecs : ∀ ss : List Section, Track (ofSecs ss) (importNamesOf ss) (exportNamesOf ss)
  | [] => by rw [ofSecs]; exact track_pure ()
  | s :: ss => by
    rw [ofSecs]
    exact track_congr (track_bind (track_ofSec s) fun _ => track_ofSecs ss)
      (by simp [importNamesOf]) (by simp [exportNamesOf])

end Names

open Names in
/-- The imports and exports `ofAst` reports have the component's own names, in order. -/
theorem ofAst_names (ss : List Section) {r : (Externs × Externs) × TS}
    (h : (ofAst (.mk ss)).run {} = .ok r) :
    r.1.1.map (·.1) = importNamesOf ss ∧ r.1.2.map (·.1) = exportNamesOf ss := by
  rw [ofAst] at h
  have hrun : ((do ofSecs ss; let s ← get; pure (s.imports, s.exports)) : TM _).run {} =
      ((ofSecs ss).run {} >>= fun p => .ok ((p.2.imports, p.2.exports), p.2)) := rfl
  rw [hrun] at h
  cases hs : (ofSecs ss).run {} with
  | error e => rw [hs] at h; exact nomatch h
  | ok p =>
    have hr : ((p.2.imports, p.2.exports), p.2) = r := by rw [hs] at h; exact Except.ok.inj h
    obtain ⟨hi, he⟩ := track_ofSecs ss {} p hs
    rw [← hr]
    exact ⟨by simpa using hi, by simpa using he⟩

end Silmaril.Wasm.Wac.TypeOf
