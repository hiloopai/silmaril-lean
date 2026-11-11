module

public import Silmaril.Proofs.Wasm.Verify.Reach.Strategy
public import Silmaril.Wasm.Spec.Basic.Defs
public import Silmaril.Wasm.Spec.Format.Thms
public import Silmaril.Wasm.Game.Strategy.Thms
public import Silmaril.Wasm.Game.Env.Defs

/-!
# Function reachability: no play calls an avoided import

`ReachIn I G fs i` collects the facts the checker establishes about an instance `I`:
`FuncsClosed G fs`, `StoreIn G`, every export address in `G`, and `Avoids G _ i`. Under it,
every hidden state along every path of `I`'s transition system satisfies `HInv`
(`trans_hInv`, `path_hInv`), so no play of `I.strategy P I.store` contains an import question
of `i` (`strategy_no_icall`), and the Wasm program of `I` satisfies `neverCall i` in
`inst neverCall (wasmSem P)` (`neverCall_of_reachIn`). Every profile `P`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

variable {G : Nat → Prop} {fs : List Nat}

/-- What the checker establishes about an instance: the reachable set `G` is closed, holds
every reference of the store and every export, and avoids import `i`. -/
structure ReachIn (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (i : Nat) : Prop where
  closed : FuncsClosed G fs (InstrIn G fs) I.store.funcs
  store : StoreIn G I.store
  exports : ∀ j, G (I.addr j)
  avoids : Avoids G I.store.funcs i

/-- The invariant of the hidden states of the transition system of `I`. -/
def HInv (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) : I.HState → Prop
  | .idle s => StoreIn G s ∧ s.funcs = I.store.funcs
  | .running _ s t => CfgIn G fs (InstrIn G fs) (t.config s) ∧ s.funcs = I.store.funcs
  | .waiting _ s t _ => CfgIn G fs (InstrIn G fs) (t.config s) ∧ s.funcs = I.store.funcs

theorem ifaceOp?_snd {ts : List FnType} {h : Nat} {args : List Val} {e : (ifaceSig ts).Op}
    (he : ifaceOp? ts h args = some e) : e.2.1 = args := by
  unfold ifaceOp? at he
  split at he
  · split at he
    · cases he; rfl
    · cases he
  · cases he

theorem ifaceOp?_fst {ts : List FnType} {h : Nat} {args : List Val} {e : (ifaceSig ts).Op}
    (he : ifaceOp? ts h args = some e) : e.1.val = h := by
  unfold ifaceOp? at he
  split at he
  · split at he
    · cases he; rfl
    · cases he
  · cases he

theorem invoke_cfgIn {Pl : Instr → Prop} {s : Store Nat} (hs : StoreIn G s) {a : Nat} (ha : G a)
    {args : List Val} (hargs : ∀ r, Val.ref r ∈ args → RefIn G r) :
    CfgIn G fs Pl (invoke s a args) :=
  ⟨hs, ⟨.inr rfl, fun r hr => by simp [invoke] at hr⟩, CodeIn.vals_append hargs
    (CodeIn.cons (CodeIn.ref (by simpa using ha)) ⟨by simp, by simp, by simp⟩)⟩

section
variable {I : ScalarInstance} {i : Nat}

theorem trans_call {s : Store Nat} {f : I.F.Op} (hR : ReachIn I G fs i)
    (hq : HInv I G fs (.idle s)) : HInv I G fs (.running f s (I.initThread f)) :=
  ⟨invoke_cfgIn hq.1 (hR.exports f.1) (typed_refIn f.2.2), hq.2⟩

theorem trans_ucall {P : Profile} {f : I.F.Op} {s s' : Store Nat} {t t' : Thread} {h : Nat}
    {args : List Val} {e : I.E.Op} (hR : ReachIn I G fs i) (run : Reach P (s, t) (s', t'))
    (callout : CalloutAt s' t' h args) (op : I.importOp? h args = some e)
    (hq : HInv I G fs (.running f s t)) : HInv I G fs (.waiting f s' t' e) ∧ e.1.val ≠ i := by
  have hcl : FuncsClosed G fs (InstrIn G fs) s.funcs := hq.2 ▸ hR.closed
  have hr : CfgIn G fs (InstrIn G fs) (t'.config s') ∧ s'.funcs = s.funcs :=
    reach_cfgIn instrIn_plainOK run hcl hq.1
  have hav : Avoids G s'.funcs i := by rw [hr.2, hq.2]; exact hR.avoids
  have hne : h ≠ i := callout_ne callout hr.1 hav
  exact ⟨⟨hr.1, hr.2.trans hq.2⟩, (ifaceOp?_fst op).symm ▸ hne⟩

theorem trans_oret {P : Profile} {f : I.F.Op} {s s' : Store Nat} {t t' : Thread}
    (hR : ReachIn I G fs i) (run : Reach P (s, t) (s', t')) (hq : HInv I G fs (.running f s t)) :
    HInv I G fs (.idle s') := by
  have hcl : FuncsClosed G fs (InstrIn G fs) s.funcs := hq.2 ▸ hR.closed
  have hr : CfgIn G fs (InstrIn G fs) (t'.config s') ∧ s'.funcs = s.funcs :=
    reach_cfgIn instrIn_plainOK run hcl hq.1
  exact ⟨Thread.config_store s' t' ▸ hr.1.1, hr.2.trans hq.2⟩

/-- **One transition keeps the invariant, and never asks import `i`.** -/
theorem trans_hInv {P : Profile} {q q' : I.HState} {m : Move I.E I.F} (h : I.Trans P q m q')
    (hR : ReachIn I G fs i) (hq : HInv I G fs q) :
    HInv I G fs q' ∧ ∀ e, m = .inl (.ask e) → e.1.val ≠ i := by
  cases h with
  | call s f => exact ⟨trans_call hR hq, fun _ he => by cases he⟩
  | ucall run callout op =>
    obtain ⟨hq', hne⟩ := trans_ucall hR run callout op hq
    exact ⟨hq', fun _ he => by cases he; exact hne⟩
  | uret v =>
    exact ⟨⟨resume_cfgIn hq.1 (answer_refIn v), hq.2⟩, fun _ he => by cases he⟩
  | oret run final answer => exact ⟨trans_oret hR run hq, fun _ he => by cases he⟩

theorem path_hInv {P : Profile} {q q' : I.HState} {p : List (Move I.E I.F)}
    (h : I.Path P q p q') (hR : ReachIn I G fs i) (hq : HInv I G fs q) :
    ∀ e, (.inl (.ask e) : Move I.E I.F) ∈ p → e.1.val ≠ i := by
  induction h with
  | nil => intro e he; cases he
  | cons ht _ ih =>
    intro e he
    obtain ⟨hq', hm⟩ := trans_hInv ht hR hq
    rcases List.mem_cons.1 he with he | he
    · exact hm e he.symm
    · exact ih hq' e he

/-- **No play of the instance asks import `i`** (every profile). -/
theorem strategy_no_icall (hR : ReachIn I G fs i) (P : Profile) {q : List (Move I.E I.F)}
    (hq : q ∈ I.strategy P I.store) : ∀ e, (.inl (.ask e) : Move I.E I.F) ∈ q → e.1.val ≠ i := by
  obtain ⟨q', hpath⟩ := ScalarInstance.mem_strategy_iff.1 hq
  exact path_hInv hpath hR ⟨hR.store, rfl⟩

end

theorem moveEvent_icall {X : WIface} {m : Move (ifaceSig X.imports) (ifaceSig X.exports)}
    {i : X.Imp} {a : List Val} (h : moveEvent m = Event.icall i a) :
    ∃ e, e.1 = i ∧ m = .inl (.ask e) := by
  rcases m with (e | ⟨e, v⟩) | (f | ⟨f, w⟩)
  · simp only [moveEvent, Sum.map_inl, evOf, Event.icall, Sum.inl.injEq, SideEv.ask.injEq] at h
    exact ⟨e, h.1, rfl⟩
  · cases h
  · cases h
  · cases h

/-- **Soundness of reachability for "never calls import `i`"** (every profile): the Wasm
program of an instance satisfying `ReachIn` never calls import `i`. -/
theorem neverCall_of_reachIn {I : ScalarInstance} {i : (ifaceOf I).Imp}
    (hR : ReachIn I G fs i.val) (P : Profile) :
    Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem P) (WasmProg.ofInstance I) i := by
  rw [models_iff]
  rintro t ⟨q, hq, rfl⟩ a hc
  obtain ⟨m, hm, hme⟩ := List.mem_map.1 hc
  obtain ⟨e, hei, rfl⟩ := moveEvent_icall hme
  exact strategy_no_icall hR P hq e hm (by rw [hei])

/-! ## Closed world: Core runs against environments -/

/-- Core runs preserve the invariant (every profile, every host returning the store unchanged
with references in `G`). -/
theorem steps_cfgIn {P : Profile} {host : HostSemantics Nat} (hh : HostIn G host)
    {c d : Config Nat} (h : Steps P host c d) (hcl : FuncsClosed G fs (InstrIn G fs) c.store.funcs)
    (hc : CfgIn G fs (InstrIn G fs) c) :
    CfgIn G fs (InstrIn G fs) d ∧ d.store.funcs = c.store.funcs := by
  induction h with
  | refl => exact ⟨hc, rfl⟩
  | tail _ hst ih =>
    obtain ⟨hc', hf'⟩ := ih
    obtain ⟨hc'', hf''⟩ := Step.cfgIn_of_empty instrIn_plainOK hh hst (hf' ▸ hcl) hc'
    exact ⟨hc'', hf''.trans hf'⟩

/-- The host of a scalar environment returns the store unchanged and scalar results. -/
theorem hostIn_hostOf {ts : List FnType} {K : Env (ifaceSig ts)} : HostIn G (hostOf ts K) := by
  intro h s vs s' r hh
  obtain ⟨e, -, (⟨w, -, hout⟩ | ⟨-, hout⟩)⟩ := hh
  · cases hout
    exact ⟨rfl, answer_refIn w⟩
  · cases hout

/-- An invariant configuration is never about to call an avoided import. -/
theorem decompose_ne {c : Config Nat} (hc : CfgIn G fs (InstrIn G fs) c) {i : Nat}
    (hav : Avoids G c.store.funcs i)
    (E : Ctx) (a : Nat) (args : List Val) : decompose? c.store c.code ≠ some (E, a, i, args) := by
  intro hd
  obtain ⟨fi, yy, ps, rs, hf, hcode, -, -, -, hfill⟩ := decompose?_sound hd
  have hr : Ref.func a ∈ codeRefs c.code := by
    rw [hfill]
    exact codeRefs_fill E _ _ (by simp)
  have ha : RefIn G (.func a) := hc.2.2.1 _ hr
  exact hav a fi (by simpa using ha) hf hcode

/-- **Closed world**: in every Core run of an export call of an instance satisfying `ReachIn`,
against any environment `K` (the host `hostOf I.imports K`), no configuration is about to call
import `i` (`decompose?` finds no callout of `i`; by silmaril-lean's `step_iff`, host calls
happen exactly at such callouts). Every profile. -/
theorem neverCall_closed_world {I : ScalarInstance} {i : Nat} (hR : ReachIn I G fs i)
    (P : Profile) (K : Env I.E) (j : Fin I.exports.length) (args : Typed (I.exports.get j).params)
    {c : Config Nat} (h : Steps P (hostOf I.imports K) (invoke I.store (I.addr j) args.1) c) :
    ∀ E a args', decompose? c.store c.code ≠ some (E, a, i, args') := by
  have h₀ : CfgIn G fs (InstrIn G fs) (invoke I.store (I.addr j) args.1) :=
    invoke_cfgIn hR.store (hR.exports j) (typed_refIn args.2)
  have hc : CfgIn G fs (InstrIn G fs) c ∧ c.store.funcs = I.store.funcs :=
    steps_cfgIn hostIn_hostOf h hR.closed h₀
  exact decompose_ne hc.1 (hc.2 ▸ hR.avoids)

end Silmaril.Wasm.Verify
