module

public import Silmaril.Wasm.Spec.Multi.Defs

@[expose] public section

/-!
# Multi-call specifications: proofs

Every profile `P`:

* `sessionPlay_mem_iff`: **the closed program plays a session exactly when Core runs it**: the
  closed play of the calls `l` is a play of `I.closedWith P s K` iff `Session P I K s l`. By
  induction from `ScalarInstance.closedWith_after_iff` (the closed program continues at the
  store left by *some* Core run of each answered call).
* `exists_trace_of_session`: a Core session is the export history of a trace of `wasmSem P`
  whose import events agree with `K`; `session_of_play`: conversely a play agreeing with `K`
  whose export events are a session's is a Core session.
* `exportHist_closed_world`: **export-history sentences are sound for Core sessions**;
  `retPost_session`: return postconditions hold of every call of every session.
-/

namespace Silmaril.Wasm.Spec.Multi

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- A session played as consecutive export questions and answers. -/
theorem sessionEv_cons {I : ScalarInstance} (f : I.F.Op) (w : I.F.Ar f) (rest : List (Call I)) :
    (sessionEv (⟨f, w⟩ :: rest)).map (Sum.inr : Ev I.F → Move Sig.empty I.F) =
      [.inr (.ask f), .inr (.ans f w)] ++ (sessionEv rest).map .inr := rfl

/-- **The closed program plays a session exactly when Core runs it** (every profile). -/
theorem sessionPlay_mem_iff {P : Profile} {I : ScalarInstance} {K : Env I.E} :
    ∀ (l : List (Call I)) (s : Store Nat),
      (sessionEv l).map .inr ∈ I.closedWith P s K ↔ Session P I K s l
  | [], s => ⟨fun _ => .nil s, fun _ => (I.closedWith P s K).nil_mem⟩
  | ⟨f, w⟩ :: rest, s => by
    rw [sessionEv_cons, ScalarInstance.closedWith_after_iff]
    constructor
    · rintro ⟨c', r, run, final, ans, hp⟩
      exact .cons c' r run final ans ((sessionPlay_mem_iff rest c'.store).1 hp)
    · intro h
      cases h with
      | cons c' r run final ans next =>
        exact ⟨c', r, run, final, ans, (sessionPlay_mem_iff rest c'.store).2 next⟩

/-- The specification events of a session are its moves read as events. -/
theorem sessionEv_map_evOf {X : WIface} (p : WasmProg X) :
    ∀ l : List (Call p.inst), (sessionEv l).map evOf = sessionEvents (X := X) l
  | [] => rfl
  | ⟨_, _⟩ :: rest => by
    show _ :: _ :: (sessionEv rest).map evOf = _ :: _ :: sessionEvents rest
    rw [sessionEv_map_evOf p rest]
    rfl

/-- **A Core session is the export history of a trace** (every profile). -/
theorem exists_trace_of_session {P : Profile} {X : WIface} (p : WasmProg X)
    {K : Env (ifaceSig X.imports)} {l : List (Call p.inst)} (h : Session P p.inst K p.store l) :
    ∃ t ∈ (wasmSem P).traces p, exportEvents t = sessionEvents l ∧
      ∃ u : List (Ev (ifaceSig X.imports)), K.Agrees u ∧ importEvents t = u.map evOf := by
  have hp : (sessionEv l).map .inr ∈ p.inst.closedWith P p.store K :=
    (sessionPlay_mem_iff l p.store).2 h
  obtain ⟨τ, hτ, hag, hup⟩ : ∃ τ ∈ p.inst.strategy P p.store, K.Agrees (lower τ) ∧
      (sessionEv l).map .inr = (upper τ).map Sum.inr :=
    Env.mem_comp_iff.1 hp
  have hup' : upper τ = sessionEv l := List.map_injective_iff.2 Sum.inr_injective hup.symm
  have hex : exportEvents (τ.map moveEvent) = (upper τ).map evOf := exportEvents_map (X := X) τ
  refine ⟨τ.map moveEvent, ⟨τ, hτ, rfl⟩, ?_, lower τ, hag, importEvents_map (X := X) τ⟩
  rw [hex, hup']
  exact sessionEv_map_evOf p l

/-- **A play agreeing with `K` whose export events are a session's is a Core session.** -/
theorem session_of_play {P : Profile} {X : WIface} (p : WasmProg X) {K : Env (ifaceSig X.imports)}
    {τ : List (Move (ifaceSig X.imports) (ifaceSig X.exports))}
    (hτ : τ ∈ p.inst.strategy P p.store) (hag : K.Agrees (lower τ)) {l : List (Call p.inst)}
    (hup : upper τ = sessionEv l) : Session P p.inst K p.store l := by
  have hp : (sessionEv l).map .inr ∈ p.inst.closedWith P p.store K :=
    Env.mem_comp_iff.2 ⟨τ, hτ, hag, (congrArg (List.map Sum.inr) hup).symm⟩
  exact (sessionPlay_mem_iff l p.store).1 hp

/-- **Export-history sentences are sound for Core sessions** (every profile): a sentence
verified in `inst exportHist (wasmSem P)` holds of every closed-world session of Core 3.0 runs
against the host induced by any environment. -/
theorem exportHist_closed_world {P : Profile} {X : WIface} (p : WasmProg X)
    {Φ : Hist (List Val) (Behaviour Val) X → Prop}
    (hM : Models (exportHist FnType (List Val) (Behaviour Val)) (wasmSem P) p Φ)
    {K : Env (ifaceSig X.imports)} {l : List (Call p.inst)} (h : Session P p.inst K p.store l) :
    Φ (sessionEvents l) := by
  obtain ⟨t, ht, hex, -⟩ := exists_trace_of_session p h
  have hsat := (models_iff (exportHist FnType (List Val) (Behaviour Val)) (wasmSem P) p Φ).1 hM
  exact hex ▸ hsat t ht

/-- Answers recorded in a session are its specification events. -/
theorem ans_mem_sessionEvents {X : WIface} :
    ∀ {l : List (Σ f : (ifaceSig X.exports).Op, (ifaceSig X.exports).Ar f)} {f w},
      ⟨f, w⟩ ∈ l → SideEv.ans f.1 (Answer.toBehaviour (ft := X.exports.get f.1) w) ∈ sessionEvents l
  | ⟨_, _⟩ :: rest, f, w, hm => by
    rcases List.mem_cons.1 hm with heq | hm'
    · cases heq
      exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ans_mem_sessionEvents hm'))

/-- **Return postconditions hold of every call of every Core session** (every profile). -/
theorem retPost_session {P : Profile} {X : WIface} (p : WasmProg X)
    {φ : RetPost.Fm (Behaviour Val) X}
    (hM : Models (retPost FnType (List Val) (Behaviour Val)) (wasmSem P) p φ)
    {K : Env (ifaceSig X.imports)} {l : List (Call p.inst)} (h : Session P p.inst K p.store l)
    {f : (ifaceSig X.exports).Op} {w : (ifaceSig X.exports).Ar f} (hm : ⟨f, w⟩ ∈ l)
    (hf : f.1 = φ.exp) : φ.post (Answer.toBehaviour (ft := X.exports.get f.1) w) := by
  have hH : Models (exportHist FnType (List Val) (Behaviour Val)) (wasmSem P) p
      ((RetPost.toHist FnType (List Val) (Behaviour Val)).fm φ) :=
    ((RetPost.toHist FnType (List Val) (Behaviour Val)).models_iff (wasmSem P) p φ).2 hM
  have hΦ := exportHist_closed_world p hH h
  exact hΦ _ (hf ▸ ans_mem_sessionEvents hm)

end Silmaril.Wasm.Spec.Multi
