module

public import Silmaril.Wasm.Verify.Start.Defs
public import Silmaril.Proofs.Wasm.Verify.Reach.Plays

/-!
# Reachability with an instantiation phase: no play asks an avoided import

Under `StartIn I s t₀ G fs i`, every transition of `(I.instSysT P s t₀).toLTS` keeps `SInv` and
never asks import `i` (`step_sInv`); hence no trace (`run_no_icall`) and no play of the
instantiable strategy `I.instStrategyT P s t₀` (`instStrategyT_no_icall`) asks import `i`.
Every profile `P`. Closed world: Core runs of the instantiation configuration against every
environment never reach a callout of `i` (`inst_closed_world`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

variable {I : ScalarInstance} {P : Profile} {s : Store Nat} {t₀ : Thread} {G : Nat → Prop}
  {fs : List Nat} {i : Nat}

/-- A host-free step keeps the thread invariant. -/
theorem thInv_internal (hR : StartIn I s t₀ G fs i) {x y : Store Nat × Thread}
    (h : InternalP P x y) (hx : ThInv G fs s.funcs x) : ThInv G fs s.funcs y := by
  have hcl : FuncsClosed G fs (InstrIn G fs) x.1.funcs := hx.2 ▸ hR.closed
  have hy : CfgIn G fs (InstrIn G fs) (y.2.config y.1) ∧ y.1.funcs = x.1.funcs :=
    internalP_cfgIn instrIn_plainOK h hcl hx.1
  exact ⟨hy.1, hy.2.trans hx.2⟩

/-- A callout of an invariant thread is an import question other than `i`, and every answer
resumes it into an invariant thread. -/
theorem thInv_callsOut (hR : StartIn I s t₀ G fs i) {x : Store Nat × Thread} {e : I.E.Op}
    (h : I.CallsOut x e) (hx : ThInv G fs s.funcs x) :
    e.1.val ≠ i ∧ ∀ n, ThInv G fs s.funcs (I.resumeK x.1 x.2 e n) := by
  obtain ⟨h', args, hco, hop⟩ := h
  have hav : Avoids G x.1.funcs i := hx.2 ▸ hR.avoids
  have hne : h' ≠ i := callout_ne hco hx.1 hav
  refine ⟨(ifaceOp?_fst hop).symm ▸ hne, fun n => ⟨?_, hx.2⟩⟩
  exact resume_cfgIn hx.1 (answer_refIn n)

/-- A finished invariant thread leaves a store whose references are in `G`. -/
theorem thInv_store {x : Store Nat × Thread} (hx : ThInv G fs s.funcs x) :
    StoreIn G x.1 ∧ x.1.funcs = s.funcs :=
  ⟨Thread.config_store x.1 x.2 ▸ hx.1.1, hx.2⟩

/-- An export call from an invariant store starts an invariant thread. -/
theorem thInv_start (hR : StartIn I s t₀ G fs i) {st : Store Nat} (hst : StoreIn G st)
    (hf : st.funcs = s.funcs) (q : I.F.Op) : ThInv G fs s.funcs (st, I.initThread q) :=
  ⟨invoke_cfgIn hst (hR.exports q.1) (typed_refIn q.2.2), hf⟩

/-- A callout transition keeps the invariant and does not ask import `i`. -/
theorem sInv_callsOut (hR : StartIn I s t₀ G fs i) {x : Store Nat × Thread} {e : I.E.Op}
    {k : I.E.Ar e → Store Nat × Thread} (hc : I.CallsOut x e ∧ k = I.resumeK x.1 x.2 e)
    (hx : ThInv G fs s.funcs x) :
    (∀ n, ThInv G fs s.funcs (k n)) ∧
      ∀ e', (some (.inl (.ask e)) : Option (Move I.E (I.F.withInst (Behaviour Val)))) =
        some (.inl (.ask e')) → e'.1.val ≠ i := by
  obtain ⟨hco, hk⟩ := hc
  obtain ⟨hne, hres⟩ := thInv_callsOut hR hco hx
  exact ⟨hk ▸ hres, fun _ he => by cases he; exact hne⟩

/-- **One transition keeps the invariant and never asks import `i`.** -/
theorem step_sInv (hR : StartIn I s t₀ G fs i) {x y : (I.instSysT P s t₀).St}
    {l : Option (Move I.E (I.F.withInst (Behaviour Val)))}
    (h : (I.instSysT P s t₀).toLTS.step x l y) (hx : SInv I P s t₀ G fs x) :
    SInv I P s t₀ G fs y ∧ ∀ e, l = some (.inl (.ask e)) → e.1.val ≠ i := by
  cases h with
  | askInst => exact ⟨⟨hR.cfg, rfl⟩, fun _ he => by cases he⟩
  | itau hst => exact ⟨thInv_internal hR hst hx, fun _ he => by cases he⟩
  | icall hc => exact sInv_callsOut hR hc hx
  | iresume m k n => exact ⟨hx n, fun _ he => by cases he⟩
  | iready hc => exact ⟨hc.2 ▸ thInv_store hx, fun _ he => by cases he⟩
  | ifail _ => exact ⟨trivial, fun _ he => by cases he⟩
  | askEx st q => exact ⟨thInv_start hR hx.1 hx.2 q, fun _ he => by cases he⟩
  | tau hst => exact ⟨thInv_internal hR hst hx, fun _ he => by cases he⟩
  | call hc => exact sInv_callsOut hR hc hx
  | resume q m k n => exact ⟨hx n, fun _ he => by cases he⟩
  | ret hc =>
    obtain ⟨r, -, -, hst⟩ := hc
    exact ⟨hst ▸ thInv_store hx, fun _ he => by cases he⟩

/-- An invariant of a transition system whose transitions never perform a bad move: no run
performs one. -/
theorem LTS.run_avoids {E F : Sig.{0}} {L : LTS E F} (Inv : L.State → Prop) (Bad : Move E F → Prop)
    (hstep : ∀ x l y, L.step x l y → Inv x → Inv y ∧ ∀ o, l = some o → ¬ Bad o) :
    ∀ {x y : L.State} {p : List (Move E F)}, L.Run x p y → Inv x → ∀ o ∈ p, ¬ Bad o := by
  intro x y p h hx
  induction h with
  | nil => intro o ho; cases ho
  | tau hst _ ih => exact ih (hstep _ _ _ hst hx).1
  | vis hst _ ih =>
    intro o ho
    have hs := hstep _ _ _ hst hx
    rcases List.mem_cons.1 ho with ho | ho
    · exact hs.2 o (by rw [ho])
    · exact ih hs.1 o ho

/-- **No run of the instantiable system asks import `i`.** -/
theorem run_no_icall (hR : StartIn I s t₀ G fs i) {x y : (I.instSysT P s t₀).St}
    {p : List (Move I.E (I.F.withInst (Behaviour Val)))}
    (h : (I.instSysT P s t₀).toLTS.Run x p y) (hx : SInv I P s t₀ G fs x) :
    ∀ e, (.inl (.ask e) : Move I.E (I.F.withInst (Behaviour Val))) ∈ p → e.1.val ≠ i := by
  have hav := LTS.run_avoids (L := (I.instSysT P s t₀).toLTS) (SInv I P s t₀ G fs)
    (fun o => ∃ e, o = .inl (.ask e) ∧ e.1.val = i)
    (fun _ _ _ hst hx' => ⟨(step_sInv hR hst hx').1, fun o ho ⟨e, hoe, hei⟩ =>
      (step_sInv hR hst hx').2 e (by rw [ho, hoe]) hei⟩) h hx
  exact fun e he hei => hav _ he ⟨e, rfl, hei⟩

/-- **No play of the strategy of an instance whose instantiation runs `t₀` asks import `i`**
(every profile). -/
theorem instStrategyT_no_icall (hR : StartIn I s t₀ G fs i) (P : Profile)
    {p : List (Move I.E (I.F.withInst (Behaviour Val)))}
    (hp : p ∈ (I.instStrategyT P s t₀).toStrategy) :
    ∀ e, (.inl (.ask e) : Move I.E (I.F.withInst (Behaviour Val))) ∈ p → e.1.val ≠ i := by
  obtain ⟨-, u, hu, hpu⟩ := hp
  have hu' : ∀ e, (.inl (.ask e) : Move I.E (I.F.withInst (Behaviour Val))) ∈ u →
      e.1.val ≠ i := by
    rcases hu with rfl | ⟨⟨y, hy⟩, -⟩
    · intro e he; cases he
    · exact run_no_icall hR hy trivial
  intro e he
  rcases hpu with hpu | ⟨p₀, o, rfl, hp₀, ho⟩
  · exact hu' e (hpu.subset he)
  · rcases List.mem_append.1 he with he | he
    · exact hu' e (hp₀.subset he)
    · have heo : o = .inl (.ask e) := (List.mem_singleton.1 he).symm
      subst heo
      exact absurd ho (by simp [Move.IsO])

/-- **Closed world for the instantiation phase**: every Core run of the instantiation
configuration, against every environment `K`, stays invariant and never reaches a callout of
import `i` (every profile). -/
theorem inst_closed_world (hR : StartIn I s t₀ G fs i) (P : Profile) (K : Env I.E)
    {c : Config Nat} (h : Steps P (hostOf I.imports K) (t₀.config s) c) :
    StoreIn G c.store ∧ c.store.funcs = s.funcs ∧
      ∀ E a args', decompose? c.store c.code ≠ some (E, a, i, args') := by
  have hcl : FuncsClosed G fs (InstrIn G fs) (t₀.config s).store.funcs := by
    rw [Thread.config_store]; exact hR.closed
  have hc : CfgIn G fs (InstrIn G fs) c ∧ c.store.funcs = (t₀.config s).store.funcs :=
    steps_cfgIn hostIn_hostOf h hcl hR.cfg
  have hf : c.store.funcs = s.funcs := by rw [hc.2, Thread.config_store]
  exact ⟨hc.1.1, hf, decompose_ne hc.1 (hf ▸ hR.avoids)⟩

/-- **Closed world after instantiation**: from any store `s'` left by a Core run of the
instantiation configuration (against any environment), every Core run of an export call against
every environment `K` never reaches a callout of import `i` (every profile). -/
theorem export_closed_world (hR : StartIn I s t₀ G fs i) (P : Profile) {K₀ K : Env I.E}
    {c₀ : Config Nat} (h₀ : Steps P (hostOf I.imports K₀) (t₀.config s) c₀)
    (j : Fin I.exports.length) (args : Typed (I.exports.get j).params) {c : Config Nat}
    (h : Steps P (hostOf I.imports K) (invoke c₀.store (I.addr j) args.1) c) :
    ∀ E a args', decompose? c.store c.code ≠ some (E, a, i, args') := by
  obtain ⟨hst, hf, -⟩ := inst_closed_world hR P K₀ h₀
  have h₁ : CfgIn G fs (InstrIn G fs) (invoke c₀.store (I.addr j) args.1) :=
    invoke_cfgIn hst (hR.exports j) (typed_refIn args.2)
  have hcl : FuncsClosed G fs (InstrIn G fs) (invoke c₀.store (I.addr j) args.1).store.funcs :=
    hf ▸ hR.closed
  have hc : CfgIn G fs (InstrIn G fs) c ∧
      c.store.funcs = (invoke c₀.store (I.addr j) args.1).store.funcs :=
    steps_cfgIn hostIn_hostOf h hcl h₁
  have hf' : c.store.funcs = s.funcs := hc.2.trans hf
  exact decompose_ne hc.1 (hf' ▸ hR.avoids)

end Silmaril.Wasm.Verify
