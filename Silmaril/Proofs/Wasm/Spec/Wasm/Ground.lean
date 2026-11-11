module

public import Silmaril.Wasm.Spec.Wasm.Defs
public import Silmaril.Wasm.Game.StatefulEnv.Thms

@[expose] public section

/-!
# Wasm traces and Core 3.0 behaviours: proofs

The traces of `wasmSem P` are grounded in Core 3.0 reduction at every profile:

* `call_ret_mem_iff`: the two-event trace "call export `j` on `a`, return `b`" is a trace exactly
  when a host-free Core run of `$invoke` reaches a result whose behaviour is `b`
  (`ScalarInstance.ask_ans_iff`);
* `exists_trace_of_sbehaviour`: every terminating closed-world behaviour of an export call
  against any stateful, nondeterministic environment `L` (the product of Core reduction with
  `L`'s host machine, `sbehavioursOf`) is the return event of a trace whose import events are
  `L`'s answers (adequacy M2, `ScalarInstance.sadequacy_answers`, and
  `SEnv.mem_comp_iff`).
-/

namespace Silmaril.Wasm.Spec

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-- Membership in the export events. -/
theorem mem_exportEvents_iff {Ty A R : Type} {X : Iface Ty} {t : List (Event A R X)}
    {x : SideEv A R X.exports.length} : x ∈ exportEvents t ↔ Sum.inr x ∈ t := by
  unfold exportEvents
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hget⟩
    rcases e with e | e
    · cases hget
    · cases hget
      exact he
  · intro h
    exact ⟨_, h, rfl⟩

/-- Membership in the import events. -/
theorem mem_importEvents_iff {Ty A R : Type} {X : Iface Ty} {t : List (Event A R X)}
    {x : SideEv A R X.imports.length} : x ∈ importEvents t ↔ Sum.inl x ∈ t := by
  unfold importEvents
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hget⟩
    rcases e with e | e
    · cases hget
      exact he
    · cases hget
  · intro h
    exact ⟨_, h, rfl⟩

/-- Export events of a mapped trace. -/
theorem filterMap_getRight_map {α β γ δ : Type} (g : α → γ) (h : β → δ) :
    ∀ l : List (α ⊕ β), (l.map (Sum.map g h)).filterMap Sum.getRight? =
      (l.filterMap Sum.getRight?).map h
  | [] => rfl
  | .inl _ :: l => filterMap_getRight_map g h l
  | .inr b :: l => by
    simp only [List.map_cons, Sum.map_inr, List.filterMap_cons, Sum.getRight?_inr]
    rw [filterMap_getRight_map g h l]

/-- Import events of a mapped trace. -/
theorem filterMap_getLeft_map {α β γ δ : Type} (g : α → γ) (h : β → δ) :
    ∀ l : List (α ⊕ β), (l.map (Sum.map g h)).filterMap Sum.getLeft? =
      (l.filterMap Sum.getLeft?).map g
  | [] => rfl
  | .inr _ :: l => filterMap_getLeft_map g h l
  | .inl a :: l => by
    simp only [List.map_cons, Sum.map_inl, List.filterMap_cons, Sum.getLeft?_inl]
    rw [filterMap_getLeft_map g h l]

/-- The export events of the trace of a play are its upper events. -/
theorem exportEvents_map {X : WIface} (t : List (Move (ifaceSig X.imports) (ifaceSig X.exports))) :
    exportEvents (t.map moveEvent) = (upper t).map evOf :=
  filterMap_getRight_map _ _ t

/-- The import events of the trace of a play are its lower events. -/
theorem importEvents_map {X : WIface} (t : List (Move (ifaceSig X.imports) (ifaceSig X.exports))) :
    importEvents (t.map moveEvent) = (lower t).map evOf :=
  filterMap_getLeft_map _ _ t

/-- **Closed world, stateful environments, every profile.** A terminating behaviour of an export
call against the host machine `L` is the return event of a trace whose import events are answers
of `L`. -/
theorem exists_trace_of_sbehaviour {P : Profile} {X : WIface} (p : WasmProg X)
    (hw : p.inst.WellFormed p.store) (L : SEnv (ifaceSig X.imports))
    (hL : L.ThrowsBelow p.store.exns.length) (q : L.S) (f : (ifaceSig X.exports).Op)
    {b : Behaviour Val} (hb : b ≠ .diverges)
    (h : b ∈ sbehavioursOf P L q (invoke p.store (p.inst.addr f.1) f.2.1)) :
    ∃ t ∈ (wasmSem P).traces p, exportEvents t = [.ask f.1 f.2.1, .ans f.1 b] ∧
      ∃ u : List (Ev (ifaceSig X.imports)), L.Agrees q u ∧ importEvents t = u.map evOf := by
  have hobs : b ∈ compositeObs (p.inst.closedS P p.store L q) f :=
    (ScalarInstance.sadequacy_answers hw L hL q f b hb).1 h
  obtain ⟨w, hresp, rfl⟩ : ∃ w, Responds (p.inst.closedS P p.store L q) f w ∧
      b = Answer.toBehaviour (ft := X.exports.get f.1) w := by
    rcases hobs with hobs | ⟨rfl, -⟩
    · exact hobs
    · exact absurd rfl hb
  obtain ⟨t, ht, hag, hup⟩ : ∃ t ∈ p.inst.strategy P p.store, L.Agrees q (lower t) ∧
      [.inr (.ask f), .inr (.ans f w)] = (upper t).map Sum.inr :=
    SEnv.mem_comp_iff.1 hresp
  have hup' : upper t = [.ask f, .ans f w] :=
    List.map_injective_iff.2 Sum.inr_injective (by rw [← hup]; rfl)
  have hex : exportEvents (t.map moveEvent) = (upper t).map evOf := exportEvents_map (X := X) t
  refine ⟨t.map moveEvent, ⟨t, ht, rfl⟩, hex.trans ?_, lower t, hag, importEvents_map t⟩
  rw [hup']
  rfl

/-- A mapped list of length two. -/
theorem map_eq_pair {α β : Type} {f : α → β} {t : List α} {x y : β} (h : t.map f = [x, y]) :
    ∃ m₁ m₂, t = [m₁, m₂] ∧ f m₁ = x ∧ f m₂ = y := by
  obtain ⟨m₁, t₁, rfl, h₁, ht₁⟩ := List.map_eq_cons_iff.1 h
  obtain ⟨m₂, t₂, rfl, h₂, ht₂⟩ := List.map_eq_cons_iff.1 ht₁
  have ht₂' : t₂ = [] := List.map_eq_nil_iff.1 ht₂
  exact ⟨m₁, m₂, by rw [ht₂'], h₁, h₂⟩

/-- The move read as a call event of export `j` on `a` is the question `⟨j, a⟩`. -/
theorem moveEvent_eq_call {X : WIface} {m : Move (ifaceSig X.imports) (ifaceSig X.exports)}
    {j : X.Exp} {a : Typed (X.exports.get j).params}
    (h : moveEvent m = Event.call j a.1) : m = .inr (.ask ⟨j, a⟩) := by
  rcases m with (e | e) | (⟨⟨j', a'⟩⟩ | ⟨f, w⟩)
  · cases h
  · cases h
  · simp only [moveEvent, Sum.map_inr, evOf, Event.call, Sum.inr.injEq, SideEv.ask.injEq] at h
    obtain ⟨rfl, ha⟩ := h
    have ha' : a' = a := Subtype.ext ha
    rw [ha']
  · cases h

/-- The move read as a return event of export `j` is an answer to a question of `j`. -/
theorem moveEvent_eq_ret {X : WIface} {m : Move (ifaceSig X.imports) (ifaceSig X.exports)}
    {j : X.Exp} {b : Behaviour Val} (h : moveEvent m = Event.ret j b) :
    ∃ f w, f.1 = j ∧ m = .inr (.ans f w) ∧ Answer.toBehaviour (ft := X.exports.get f.1) w = b := by
  rcases m with (e | e) | (e | ⟨f, w⟩)
  · cases h
  · cases h
  · cases h
  · simp only [moveEvent, Sum.map_inr, evOf, Event.ret, Sum.inr.injEq, SideEv.ans.injEq] at h
    exact ⟨f, w, h.1, rfl, h.2⟩

/-- In a legal play, the answer after a question answers that question. -/
theorem legal_ask_ans {E F : Sig.{0}} {f f' : F.Op} {w : F.Ar f'}
    (h : Legal ([.inr (.ask f), .inr (.ans f' w)] : List (Move E F))) : f' = f := by
  obtain ⟨y, hp⟩ := h
  cases hp with
  | cons h₁ hp₁ =>
    cases h₁
    cases hp₁ with
    | cons h₂ _ =>
      cases h₂
      rfl

/-- The trace of a two-move play "ask `f`, answer `w`". -/
theorem map_two {X : WIface} (f : (ifaceSig X.exports).Op) (w : Answer (X.exports.get f.1)) :
    ([.inr (.ask f), .inr (.ans f w)] : List (Move (ifaceSig X.imports) (ifaceSig X.exports))).map
      moveEvent = [Event.call f.1 f.2.1, Event.ret f.1 (Answer.toBehaviour w)] := rfl

/-- **Traces are Core runs (open world, every profile).** The trace "call export `j` on `a`,
return `b`" is a trace exactly when a host-free Core run of `$invoke` reaches a result, typed by
the export's result types, whose behaviour is `b`. -/
theorem call_ret_mem_iff {P : Profile} {X : WIface} (p : WasmProg X) (j : X.Exp)
    (a : Typed (X.exports.get j).params) (b : Behaviour Val) :
    [Event.call j a.1, Event.ret j b] ∈ (wasmSem P).traces p ↔
      ∃ (d : Config Nat) (r : Result) (w : Answer (X.exports.get j)),
        Steps P (Det.noHost : HostSemantics Nat) (invoke p.store (p.inst.addr j) a.1) d ∧
        d.code = r.toAdmin ∧ Answer.ofResult? (X.exports.get j) r = some w ∧
        Answer.toBehaviour w = b := by
  constructor
  · rintro ⟨t, ht, hmap⟩
    obtain ⟨m₁, m₂, htm, h₁, h₂⟩ := map_eq_pair hmap
    have hm₁ : m₁ = .inr (.ask ⟨j, a⟩) := moveEvent_eq_call h₁
    obtain ⟨f, w, -, hm₂, hwb⟩ := moveEvent_eq_ret h₂
    have ht' : [m₁, m₂] ∈ p.inst.strategy P p.store := htm ▸ ht
    have hplay : [.inr (.ask ⟨j, a⟩), .inr (.ans f w)] ∈ p.inst.strategy P p.store :=
      hm₁ ▸ hm₂ ▸ ht'
    have hff : f = ⟨j, a⟩ := legal_ask_ans ((p.inst.strategy P p.store).legal hplay)
    subst hff
    obtain ⟨d, r, hrun, hcode, hres⟩ := ScalarInstance.ask_ans_iff.1 hplay
    exact ⟨d, r, w, hrun, hcode, hres, hwb⟩
  · rintro ⟨d, r, w, hrun, hcode, hres, rfl⟩
    have hplay : [.inr (.ask ⟨j, a⟩), .inr (.ans ⟨j, a⟩ w)] ∈ p.inst.strategy P p.store :=
      ScalarInstance.ask_ans_iff.2 ⟨d, r, hrun, hcode, hres⟩
    exact ⟨_, hplay, map_two (X := X) ⟨j, a⟩ w⟩

end Silmaril.Wasm.Spec
