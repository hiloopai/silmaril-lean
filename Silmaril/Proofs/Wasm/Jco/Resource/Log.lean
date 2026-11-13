module

public import Silmaril.Wasm.Jco.Resource.Log.Defs
public import Silmaril.Proofs.Wasm.Jco.Resource.Table

/-!
# Handle tables that record their history: proofs

* `steps_snoc`: a successful history extended by a successful operation;
* `logTab_lawful`: the recording tables are lawful;
* `logEmpty_inv`: the empty table with the empty history satisfies the invariant;
* `logTab_accepts`: the history of a table satisfying the invariant is accepted by the handle
  protocol in both orientations (`table_steps_accepts` of `Silmaril.Wasm.Resource.Table`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Res

open Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Resource (handleProto Role tableEv table_steps_accepts freeOK_empty)
open Silmaril.Wasm.Component.Runtime (Table)

theorem steps_snoc {t t' t'' : Table HEntry} {evs : List (Table.Event HEntry)}
    {ev : Table.Event HEntry} (h : Table.Steps t evs t') (hs : t'.step? ev.op = some (ev, t'')) :
    Table.Steps t (evs ++ [ev]) t'' := by
  induction h with
  | nil t => exact .cons hs (.nil _)
  | cons h1 _ ih => exact .cons h1 (ih hs)

theorem logTab_add_spec (t : logTab.T) (e : HEntry) (i : Nat) (t' : logTab.T)
    (hI : logTab.Inv t) (h : logTab.add? t e = some (i, t')) :
    i < 2 ^ 32 ∧ logTab.get? t i = none ∧ logTab.get? t' i = some e ∧
      (∀ j, j ≠ i → logTab.get? t' j = logTab.get? t j) ∧ logTab.Inv t' ∧
        logTab.cap t' = (logTab.cap t).map (· - 1) := by
  obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.1 h
  have he1 : p.1 = i := (Prod.mk.inj hpe).1
  have he2 : (p.2, t.2 ++ [Table.Event.added p.1 e]) = t' := (Prod.mk.inj hpe).2
  have hp' : t.1.add? e = some (i, t'.1) := by rw [hp, ← he1, ← he2]
  have hr := refTab_add_spec t.1 e i t'.1 hI.1 hp'
  have hst : t.1.step? (Table.Event.added i e).op = some (.added i e, t'.1) := by
    simp only [Table.Event.op, Table.step?, hp', Option.map_some]
  have hlog : t'.2 = t.2 ++ [.added i e] := by rw [← he2, he1]
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, ⟨hr.2.2.2.2.1, hlog ▸ steps_snoc hI.2 hst⟩,
    hr.2.2.2.2.2⟩

theorem logTab_remove_spec (t : logTab.T) (i : Nat) (e : HEntry) (t' : logTab.T)
    (hI : logTab.Inv t) (h : logTab.remove? t i = some (e, t')) :
    logTab.get? t i = some e ∧ logTab.get? t' i = none ∧
      (∀ j, j ≠ i → logTab.get? t' j = logTab.get? t j) ∧ logTab.Inv t' ∧
        logTab.cap t' = (logTab.cap t).map (· + 1) := by
  obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.1 h
  have he1 : p.1 = e := (Prod.mk.inj hpe).1
  have he2 : (p.2, t.2 ++ [Table.Event.removed i p.1]) = t' := (Prod.mk.inj hpe).2
  have hp' : t.1.remove? i = some (e, t'.1) := by rw [hp, ← he1, ← he2]
  have hr := refTab_remove_spec t.1 i e t'.1 hI.1 hp'
  have hst : t.1.step? (Table.Event.removed i e).op = some (.removed i e, t'.1) := by
    simp only [Table.Event.op, Table.step?, hp', Option.map_some]
  have hlog : t'.2 = t.2 ++ [.removed i e] := by rw [← he2, he1]
  exact ⟨hr.1, hr.2.1, hr.2.2.1, ⟨hr.2.2.2.1, hlog ▸ steps_snoc hI.2 hst⟩, hr.2.2.2.2⟩

theorem logTab_touch_spec (t : logTab.T) (i : Nat) (e : HEntry) (hI : logTab.Inv t)
    (hg : logTab.get? t i = some e) :
    (∀ j, logTab.get? (logTab.touch t i) j = logTab.get? t j) ∧
      logTab.cap (logTab.touch t i) = logTab.cap t ∧ logTab.Inv (logTab.touch t i) := by
  have hg' : t.1.get? i = some e := hg
  have ht : logTab.touch t i = (t.1, t.2 ++ [.got i e]) := by
    simp only [logTab, hg']
  have hst : t.1.step? (Table.Event.got i e).op = some (.got i e, t.1) := by
    simp only [Table.Event.op, Table.step?, hg', Option.map_some]
  rw [ht]
  exact ⟨fun _ => rfl, rfl, hI.1, steps_snoc hI.2 hst⟩

/-- **The recording tables are lawful.** -/
theorem logTab_lawful : logTab.Lawful where
  add_some t e _ hc := by
    have h : (t.1.add? e).isSome := refTab_add_some t.1 e hc
    show ((t.1.add? e).map _).isSome
    rw [Option.isSome_map]
    exact h
  add_spec := logTab_add_spec
  touch_spec := logTab_touch_spec
  remove_some t i e h := by
    obtain ⟨t', ht'⟩ := refTab_remove_some t.1 i e h
    have ht'' : t.1.remove? i = some (e, t') := ht'
    exact ⟨(t', t.2 ++ [.removed i e]), by simp only [logTab, ht'']; rfl⟩
  remove_spec := logTab_remove_spec

theorem logEmpty_inv : logTab.Inv logEmpty :=
  ⟨⟨freeOK_empty, by show (#[none] : Array (Option HEntry)).size ≤ Table.maxLength + 1; simp⟩,
    .nil _⟩

/-- **The history of a table satisfying the invariant is accepted by the handle protocol**, in
both orientations. -/
theorem logTab_accepts {t : logTab.T} (hI : logTab.Inv t) (r : Role) :
    (handleProto ℕ r).Accepts (t.2.map tableEv) :=
  table_steps_accepts hI.2 r

end Silmaril.Proofs.Wasm.Jco.Res
