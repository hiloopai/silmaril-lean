module

public import Silmaril.Containers.SyncComponent.Defs
public import Silmaril.Containers.Executor.Thms
public import Silmaril.Wasi.Host.Thms
public import Silmaril.Wasi.Comp.Thms

public section
namespace Silmaril.Proofs.Containers.SyncComponent
open Silmaril.Containers Silmaril.Containers.SyncComponent
open Silmaril.Games (Sig Move Zip Path)
open Silmaril.Wasi (nsig CStep Reach)

theorem run_reaches {trap t s} (h : Run trap t s) :
    Reach body (t.map (Event.move trap)) (componentState trap s) := by
  induction h with
  | nil => exact .nil
  | @snoc t s s' e _ hs ih =>
    cases hs with
    | start trap =>
      simpa [Event.move, componentState] using ih.snoc (CStep.ask (sampleOp trap))
    | request =>
      simpa [Event.move, componentState, body, sampleOp] using
        ih.snoc (CStep.call (sampleOp false) chooseOp afterChoice)
    | reply trap b =>
      simpa [Event.move, componentState] using
        ih.snoc (CStep.reply (sampleOp trap) chooseOp afterChoice (values (some b)))
    | negate trap b => simpa [componentState, values, afterChoice] using ih
    | trap => simpa [componentState, body, sampleOp, values] using ih
    | ret trap r =>
      simpa [Event.move, componentState] using ih.snoc (CStep.ret (sampleOp trap) (values r))

def beforeReturn (trap choice : Bool) : List Event :=
  if trap then [.call true] else [.call false, .choose, .chosen choice]

def resultOf (trap choice : Bool) : Option Bool := if trap then none else some (!choice)

def Shape (trap : Bool) (t : List Event) : Phase → Prop
  | .idle => t = []
  | .started => t = [.call trap]
  | .waiting => trap = false ∧ t = [.call false, .choose]
  | .computing b => trap = false ∧ t = [.call false, .choose, .chosen b]
  | .result r => ∃ choice, t = beforeReturn trap choice ∧ r = resultOf trap choice
  | .finished r => ∃ choice, t = completedTrace trap choice ∧ r = resultOf trap choice

theorem run_shape {trap t s} (h : Run trap t s) : Shape trap t s := by
  induction h with
  | nil => rfl
  | @snoc t s s' e _ hs ih =>
    cases hs with
    | start trap => simp [Shape, show t = [] from ih]
    | request => exact ⟨rfl, by simp [show t = [.call false] from ih]⟩
    | reply trap b =>
      obtain ⟨rfl, rfl⟩ := ih
      exact ⟨rfl, rfl⟩
    | negate trap b =>
      obtain ⟨rfl, rfl⟩ := ih
      exact ⟨b, rfl, rfl⟩
    | trap =>
      exact ⟨false, by simpa [beforeReturn] using (show t = [.call true] from ih), rfl⟩
    | ret trap r =>
      obtain ⟨choice, rfl, rfl⟩ := ih
      exact ⟨choice, by cases trap <;> rfl, rfl⟩

theorem complete_run (trap choice : Bool) :
    Run trap (completedTrace trap choice) (.finished (resultOf trap choice)) := by
  cases trap with
  | false =>
    exact (((((Run.nil.snoc (.start false)).snoc .request).snoc (.reply false choice)).snoc
      (.negate false choice)).snoc (.ret false (some (!choice))))
  | true => exact ((Run.nil.snoc (.start true)).snoc .trap).snoc (.ret true none)

theorem zip_trace (trap : Bool) (t : List Event) :
    Zip (t.filterMap Event.host) (t.map (Event.move trap))
      (t.filterMap (Event.closed trap)) := by
  induction t with
  | nil => exact .nil
  | cons e t ih =>
    cases e with
    | call b => exact .right _ ih
    | choose => exact .sync _ ih
    | chosen b => exact .sync _ ih
    | returned r => exact .right _ ih

theorem source_simulates {host trap b} (hb : source host trap b) :
    linked host trap b := by
  rcases hb with ⟨t, r, hr, hh, rfl⟩ | ⟨htrap, hb⟩
  · obtain ⟨choice, ht, hout⟩ := run_shape hr
    refine Or.inl ⟨r, ?_, ?_⟩
    · have hp : t.filterMap (Event.closed trap) ∈
          Silmaril.Wasi.link host (Silmaril.Wasi.ofBody body) :=
        ⟨_, hh, _, ⟨_, run_reaches hr⟩, zip_trace trap t⟩
      cases trap <;> simpa [ht, hout, completedTrace, resultOf, List.filterMap, Event.closed] using hp
    · cases trap <;> simp [report, ht, hout, completedTrace, resultOf, List.filter, Event.isExport]
  · subst trap
    refine Or.inr ⟨rfl, ?_, hb⟩
    exact ⟨[], host.nil_mem, [.inr (.ask (sampleOp false))],
      ⟨_, Reach.nil.snoc (CStep.ask (sampleOp false))⟩, .right _ .nil⟩

theorem hostPlay_loose (b : Bool) : hostPlay b ∈ looseHost := by
  constructor
  · exact ⟨_, Path.cons (.ask chooseOp) (Path.cons (.ret chooseOp (values (some b))) (.nil _))⟩
  · intro e he
    simp [hostPlay, Silmaril.Wasi.htrace, Silmaril.Wasi.hev] at he
    exact ⟨b, he.symm⟩

theorem loose_admitted : Admitted looseHost :=
  ⟨Silmaril.Wasi.ofPred_sat _ _, false, hostPlay_loose false⟩

theorem source_nonempty (host : ClosedHost) (ha : Admitted host) (trap : Bool) :
    ∃ b, source host trap b := by
  obtain ⟨choice, hc⟩ := ha.2
  refine ⟨report (completedTrace trap choice) (resultOf trap choice), Or.inl
    ⟨_, _, complete_run trap choice, ?_, rfl⟩⟩
  cases trap with
  | false => exact hc
  | true => exact host.nil_mem

theorem certificate : executor.Certificate := by
  constructor
  · exact ⟨(), trivial⟩
  · intro _ _; exact ⟨looseHost, false, loose_admitted⟩
  · intro _ _ trap; cases trap <;> rfl
  · intro _ host trap _ _; exact ⟨(host, trap), rfl⟩
  · intro _ host trap _ ha
    obtain ⟨b, hb⟩ := source_nonempty host ha trap
    exact ⟨b, b, hb, rfl⟩
  · intro _ host trap _ _ b hb
    obtain ⟨b₀, hs, rfl⟩ := hb
    rcases hs with ⟨_, _, _, _, rfl⟩ | ⟨_, rfl⟩ <;> trivial
  · intro _ host trap _ ha b hb
    obtain ⟨b₀, hs, rfl⟩ := hb
    exact source_simulates hs

def ProgramOK (args : List Silmaril.Wasm.Component.Val) (p : Silmaril.Wasi.BProg world.imports) :
    Prop :=
  (∃ r, p = .pure r ∧ ReturnOK args r) ∨
  (args = [.bool false] ∧ p = .call chooseOp afterChoice)

def StateOK : Silmaril.Wasi.CSt world.imports world.exports → Prop
  | .idle => True
  | .run q p => ProgramOK q.2 p
  | .wait q m k => q.2 = [.bool false] ∧ m = chooseOp ∧ k = afterChoice

theorem body_ok (q : (nsig world.exports).Op) : ProgramOK q.2 (body q) := by
  by_cases h : q.2 = [.bool false]
  · exact Or.inr ⟨h, by simp [body, h]⟩
  · refine Or.inl ⟨none, ?_, ⟨fun _ => rfl, fun hh => (h hh).elim⟩⟩
    unfold body
    split <;> simp_all

theorem step_ok {c c' o} (hc : CStep body c o c') (hi : StateOK c)
    (ha : TypedAnswers (Silmaril.Wasi.hostView [Silmaril.Wasi.wev o])) :
    StateOK c' ∧ GoodEvent (Silmaril.Wasi.wev o) := by
  cases hc with
  | ask q => exact ⟨body_ok q, trivial⟩
  | call q m k =>
    rcases hi with ⟨r, heq, _⟩ | ⟨hargs, heq⟩
    · cases heq
    · cases heq
      exact ⟨⟨hargs, rfl, rfl⟩, trivial⟩
  | reply q m k n =>
    obtain ⟨hargs, rfl, rfl⟩ := hi
    obtain ⟨b, hb⟩ := ha (.imp chooseName [] n) (by
      simp [Silmaril.Wasi.hostView, Silmaril.Wasi.wev, Silmaril.Wasi.WEv.isImp, chooseOp])
    have hn : n = values (some b) := (Silmaril.Wasi.WEv.imp.inj hb).2.2
    subst n
    refine ⟨Or.inl ⟨values (some (!b)), rfl, ?_⟩, trivial⟩
    cases b <;> simp [ReturnOK, hargs]
  | ret q r =>
    rcases hi with ⟨r', heq, hg⟩ | ⟨_, heq⟩
    · cases heq; exact ⟨trivial, hg⟩
    · cases heq

theorem reach_good {t c} (hr : Reach body t c)
    (ha : TypedAnswers (Silmaril.Wasi.hostView (Silmaril.Wasi.wtrace t))) :
    StateOK c ∧ GoodEvents (Silmaril.Wasi.wtrace t) := by
  induction hr with
  | nil => exact ⟨trivial, by simp [GoodEvents, Silmaril.Wasi.wtrace]⟩
  | @snoc t c c' o hr hc ih =>
    rw [Silmaril.Wasi.wtrace_concat, Silmaril.Wasi.hostView_append] at ha
    have ha₀ : TypedAnswers (Silmaril.Wasi.hostView (Silmaril.Wasi.wtrace t)) :=
      fun e he => ha e (List.mem_append_left _ he)
    have ha₁ : TypedAnswers (Silmaril.Wasi.hostView [Silmaril.Wasi.wev o]) :=
      fun e he => ha e (List.mem_append_right _ he)
    obtain ⟨hi, hg⟩ := ih ha₀
    obtain ⟨hi', hg'⟩ := step_ok hc hi ha₁
    refine ⟨hi', ?_⟩
    intro e he
    rw [Silmaril.Wasi.wtrace_concat, List.mem_append, List.mem_singleton] at he
    exact he.elim (hg e) (fun he => he ▸ hg')

theorem component_sat :
    (Silmaril.Wasi.ag (fun t => TypedAnswers (Silmaril.Wasi.hostView t))
      (fun t => GoodEvents (Silmaril.Wasi.expView t))).holds (Silmaril.Wasi.ofBody body) := by
  rintro t ⟨c, hr⟩ ha e he
  exact (reach_good hr ha).2 e (List.mem_filter.mp he).1

theorem linked_good (host : ClosedHost)
    (ha : (Silmaril.Wasi.hostSat TypedAnswers).holds host) :
    ∀ p ∈ Silmaril.Wasi.link host (Silmaril.Wasi.ofBody body),
      GoodEvents (Silmaril.Wasi.xtrace p) :=
  Silmaril.Wasi.link_sat component_sat ha

theorem linked_returns {host trap b} (ha : Admitted host) (hb : linked host trap b) :
    Reports trap b := by
  rcases hb with ⟨r, hp, rfl⟩ | ⟨ht, _, hb⟩
  · refine Or.inl ⟨r, ?_, rfl⟩
    exact linked_good host ha.1 _ hp (.ret sampleName [.bool trap] (values r)) (by
      simp [Silmaril.Wasi.xtrace, Silmaril.Wasi.xev, sampleOp])
  · exact Or.inr ⟨ht, hb⟩

theorem runtime_returns (host : ClosedHost) (trap : Bool) (ha : Admitted host) :
    (runtime.beh ((), host, trap)).Sat (fun b => Spec.noUB b ∧ Reports trap b) :=
  certificate.sat trivial ha (fun _ hb => linked_returns ha hb)

theorem runtime_choice (host : ClosedHost) (choice : Bool) (hc : hostPlay choice ∈ host) :
    runtime.beh ((), host, false)
      (.done [.call false, .returned (some (!choice))] (.exited 0)) := by
  refine ⟨_, Or.inl ⟨completedTrace false choice, some (!choice),
    complete_run false choice, hc, rfl⟩, ?_⟩
  rfl

theorem runtime_complements (host : ClosedHost) :
    (runtime.beh ((), host, false)).Sat (fun b => b = .blocked [.call false] ∨ ∃ choice,
      hostPlay choice ∈ host ∧
      b = .done [.call false, .returned (some (!choice))] (.exited 0)) := by
  intro b hb
  obtain ⟨b₀, hs, rfl⟩ := hb
  rcases hs with ⟨t, r, hr, hh, rfl⟩ | ⟨_, hb⟩
  · obtain ⟨choice, rfl, rfl⟩ := run_shape hr
    exact Or.inr ⟨choice, hh, rfl⟩
  · exact Or.inl hb

theorem runtime_waits (host : ClosedHost) :
    runtime.beh ((), host, false) (.blocked [.call false]) :=
  ⟨_, Or.inr ⟨rfl, rfl⟩, rfl⟩

theorem runtime_trap (host : ClosedHost) :
    runtime.beh ((), host, true) (.done [.call true, .returned none] (.exited 70)) :=
  ⟨_, Or.inl ⟨_, _, complete_run true false, host.nil_mem, rfl⟩, rfl⟩

theorem trapPolicy_reflects : trapPolicy.ReflectsNoUB := by
  intro b hb
  cases b with
  | done t stop =>
    change Spec.noUB (if Event.returned none ∈ t then
      Beh.done t (.undefined .unmodeled) else .done t stop) at hb
    split at hb
    · exact hb.elim
    · exact hb
  | blocked _ => trivial
  | spins _ => trivial
  | reactive _ => trivial

theorem untyped_reply_rejected :
    ¬ TypedAnswers [.imp chooseName [] (some [.u64 0])] := by
  intro h
  obtain ⟨b, hb⟩ := h _ (List.mem_singleton_self _)
  cases b <;> cases hb

end Silmaril.Proofs.Containers.SyncComponent
