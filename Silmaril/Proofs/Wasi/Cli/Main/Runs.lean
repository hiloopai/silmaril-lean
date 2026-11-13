module

public import Silmaril.Wasi.Cli.Main.Defs
public import Silmaril.Wasi.Comp.Thms
public import Silmaril.Wasi.Cli.Thms

/-!
# Runs of programs over WASI imports, and the plays of their components

Proofs for `Silmaril.Wasi.Cli.Main.Thms`.

* `PRun` inversion (`PRun.pure_inv`, `PRun.call_inv`) and sequencing (`PRun.bind_inv`,
  `PRun.bind_left`, `PRun.bind_right`, `PRun.bind_mono`); `bind_assoc` for `Silmaril.Games.Prog`.
* **`plays_run`**: a play of `ofBody h` that calls the export at most once is empty, or the
  export call followed by a run of its program (`runTrace`); **`play_of_run`**: every run of
  the program is such a play.
* **`guar_of_runs`**: a guarantee of `ofBody h'` transfers to `ofBody h` when every run of
  `h` the assumption admits is a run of `h'`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli

open Silmaril.Cli Silmaril.Games
open Silmaril.Wasm.Component (Val)

variable {I X : Set FnName} {α β γ : Type}

/-! ## Programs -/

/-- Sequencing programs is associative. -/
theorem prog_bind_assoc (p : WProg I α) (f : α → WProg I β) (g : β → WProg I γ) :
    (p.bind f).bind g = p.bind fun a => (f a).bind g := by
  induction p with
  | pure a => rfl
  | call m k ih =>
    show Prog.call m (fun n => ((k n).bind f).bind g) = Prog.call m fun n => (k n).bind _
    exact congrArg _ (funext ih)

namespace PRun

/-- A returned program made no call. -/
theorem pure_inv {a : α} {t : List WEv} {r : Option α} (h : PRun (I := I) (.pure a) t r) :
    t = [] ∧ (r = none ∨ r = some a) := by
  cases h
  · exact ⟨rfl, .inl rfl⟩
  · exact ⟨rfl, .inr rfl⟩

/-- A call: nothing yet, the request, or the request, an answer and a run of the rest. -/
theorem call_inv {m : (nsig I).Op} {k : Option (List Val) → WProg I α} {t : List WEv}
    {r : Option α} (h : PRun (.call m k) t r) :
    (t = [] ∧ r = none) ∨ (t = [.req m.1.1 m.2] ∧ r = none) ∨
      ∃ n t', t = .req m.1.1 m.2 :: .imp m.1.1 m.2 n :: t' ∧ PRun (k n) t' r := by
  cases h with
  | stop => exact .inl ⟨rfl, rfl⟩
  | ask => exact .inr (.inl ⟨rfl, rfl⟩)
  | step _ _ n h' => exact .inr (.inr ⟨n, _, rfl, h'⟩)

/-- **The runs of a sequence**: a run of the first program that has not returned, or a
finished run of it followed by a run of the second. -/
theorem bind_inv {p : WProg I α} {f : α → WProg I β} {t : List WEv} {r : Option β}
    (h : PRun (p.bind f) t r) :
    (PRun p t none ∧ r = none) ∨
      ∃ t₁ t₂ a, t = t₁ ++ t₂ ∧ PRun p t₁ (some a) ∧ PRun (f a) t₂ r := by
  induction p generalizing t with
  | pure a => exact .inr ⟨[], t, a, rfl, .done a, h⟩
  | call m k ih =>
    have h0 : PRun (.call m fun n => (k n).bind f) t r := h
    rcases call_inv h0 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨n, t', rfl, h'⟩
    · exact .inl ⟨.stop _, rfl⟩
    · exact .inl ⟨.ask m k, rfl⟩
    · rcases ih n h' with ⟨h1, rfl⟩ | ⟨t₁, t₂, a, rfl, h1, h2⟩
      · exact .inl ⟨.step m k n h1, rfl⟩
      · exact .inr ⟨_ :: _ :: t₁, t₂, a, rfl, .step m k n h1, h2⟩

/-- Both directions of sequencing, by induction on the first run. -/
theorem bind_of {p : WProg I α} {f : α → WProg I β} {t : List WEv} {r : Option α}
    (h : PRun p t r) :
    (r = none → PRun (p.bind f) t none) ∧
      ∀ a, r = some a → ∀ t₂ r', PRun (f a) t₂ r' → PRun (p.bind f) (t ++ t₂) r' := by
  induction h with
  | stop p => exact ⟨fun _ => .stop _, fun _ h => absurd h (by simp)⟩
  | done a =>
    refine ⟨fun h => absurd h (by simp), fun a' ha t₂ r' h₂ => ?_⟩
    have ha' : a = a' := Option.some.inj ha
    exact ha' ▸ h₂
  | ask m k => exact ⟨fun _ => .ask m _, fun _ h => absurd h (by simp)⟩
  | step m k n _ ih =>
    exact ⟨fun hr => .step m _ n (ih.1 hr), fun a ha t₂ r' h₂ => .step m _ n (ih.2 a ha t₂ r' h₂)⟩

/-- A run of the first program that has not returned is a run of the sequence. -/
theorem bind_left {p : WProg I α} {f : α → WProg I β} {t : List WEv} (h : PRun p t none) :
    PRun (p.bind f) t none :=
  (bind_of h).1 rfl

/-- A finished run of the first program followed by a run of the second. -/
theorem bind_right {p : WProg I α} {f : α → WProg I β} {t₁ t₂ : List WEv} {a : α}
    {r : Option β} (h₁ : PRun p t₁ (some a)) (h₂ : PRun (f a) t₂ r) :
    PRun (p.bind f) (t₁ ++ t₂) r :=
  (bind_of h₁).2 a rfl t₂ r h₂

/-- **Changing the continuation** where it is reached. -/
theorem bind_mono {p : WProg I α} {f g : α → WProg I β} {t : List WEv} {r : Option β}
    (h : PRun (p.bind f) t r)
    (hfg : ∀ t₁ t₂ a, t = t₁ ++ t₂ → PRun p t₁ (some a) → PRun (f a) t₂ r → PRun (g a) t₂ r) :
    PRun (p.bind g) t r := by
  rcases bind_inv h with ⟨h1, rfl⟩ | ⟨t₁, t₂, a, rfl, h1, h2⟩
  · exact bind_left h1
  · exact bind_right h1 (hfg t₁ t₂ a rfl h1 h2)

/-- **A scripted run is a run.** -/
theorem traceOf_run (host : FnName → List Val → Option (List Val)) :
    ∀ (p : WProg I α) (n : Nat), PRun p (traceOf host p n).1 (traceOf host p n).2
  | .pure a, _ => .done a
  | .call m k, 0 => .ask m k
  | .call m k, n + 1 => .step m k _ (traceOf_run host (k (host m.1.1 m.2)) n)

end PRun

/-! ## Plays and runs -/

/-- The return event of the export call `q` when its program returned `a`. -/
def retEv (q : (nsig X).Op) : Option (Option (List Val)) → List WEv
  | some a => [.ret q.1.1 q.2 a]
  | none => []

/-- The events of the export call `q` running its program along `t`, with its return when
`r = some a`. -/
def runTrace (q : (nsig X).Op) (t : List WEv) (r : Option (Option (List Val))) : List WEv :=
  .call q.1.1 q.2 :: (t ++ retEv q r)

/-- The calls of `f` along a concatenation. -/
theorem calls_append (f : FnName) (t u : List WEv) : calls f (t ++ u) = calls f t + calls f u :=
  List.countP_append

/-- The invariant of the plays of a component: what the play is, given the control state. -/
def PlayInv (h : Body I X) (f : FnName) (t : List WEv) : CSt I X → Prop
  | .idle => t = [] ∨ (∃ q u a, PRun (h q) u (some a) ∧ t = runTrace q u (some a)) ∨
      2 ≤ calls f t
  | .run q p => (∃ u, t = .call q.1.1 q.2 :: u ∧ ∀ u' r, PRun p u' r → PRun (h q) (u ++ u') r) ∨
      2 ≤ calls f t
  | .wait q m k => (∃ u, t = .call q.1.1 q.2 :: (u ++ [.req m.1.1 m.2]) ∧
      PRun (h q) (u ++ [.req m.1.1 m.2]) none ∧
      ∀ n u' r, PRun (k n) u' r → PRun (h q) (u ++ .req m.1.1 m.2 :: .imp m.1.1 m.2 n :: u') r) ∨
      2 ≤ calls f t

/-- Junk stays junk. -/
theorem two_le_calls_snoc {f : FnName} {t : List WEv} (e : WEv) (h : 2 ≤ calls f t) :
    2 ≤ calls f (t ++ [e]) := by
  rw [calls_append]; omega

/-- An export call of a play that already has one is junk. -/
theorem two_le_calls_of_call {f : FnName} {t : List WEv} (h : 1 ≤ calls f t) (q : (nsig X).Op)
    (hq : q.1.1 = f) : 2 ≤ calls f (t ++ [.call q.1.1 q.2]) := by
  have h1 : calls f [.call q.1.1 q.2] = 1 := by simp [calls, hq]
  rw [calls_append, h1]; omega

/-- A finished run's trace has its call. -/
theorem one_le_calls_runTrace {f : FnName} (q : (nsig X).Op) (hq : q.1.1 = f) (u : List WEv)
    (a : Option (List Val)) : 1 ≤ calls f (runTrace q u (some a)) := by
  simp [runTrace, calls, hq]

/-- An idle step: a new export call. -/
theorem playInv_ask {h : Body I X} {f : FnName} (hX : ∀ q : (nsig X).Op, q.1.1 = f)
    {t : List WEv} (hJ : PlayInv h f t .idle) (q : (nsig X).Op) :
    PlayInv h f (t ++ [.call q.1.1 q.2]) (.run q (h q)) := by
  rcases hJ with rfl | ⟨q', u, a, -, rfl⟩ | hj
  · exact .inl ⟨[], rfl, fun u' r hr => by simpa using hr⟩
  · exact .inr (two_le_calls_of_call (one_le_calls_runTrace q' (hX q') u a) q (hX q))
  · exact .inr (two_le_calls_snoc _ hj)

/-- One move keeps the invariant. -/
theorem playInv_step {h : Body I X} {f : FnName} (hX : ∀ q : (nsig X).Op, q.1.1 = f)
    {s : List (Move (nsig I) (nsig X))} {c c' : CSt I X} {o : Move (nsig I) (nsig X)}
    (hJ : PlayInv h f (wtrace s) c) (hc : CStep h c o c') :
    PlayInv h f (wtrace (s ++ [o])) c' := by
  rw [wtrace_concat]
  cases hc with
  | ask q => exact playInv_ask hX hJ q
  | call q m k =>
    rcases hJ with ⟨u, hu, hres⟩ | hj
    · refine .inl ⟨u, by rw [hu]; rfl, ?_, fun n u' r hr => hres _ _ (.step m k n hr)⟩
      exact hres _ _ (.ask m k)
    · exact .inr (two_le_calls_snoc _ hj)
  | reply q m k n =>
    rcases hJ with ⟨u, hu, -, hres⟩ | hj
    · refine .inl ⟨u ++ [.req m.1.1 m.2, .imp m.1.1 m.2 n], by rw [hu]; simp [wev], ?_⟩
      exact fun u' r hr => by simpa using hres n u' r hr
    · exact .inr (two_le_calls_snoc _ hj)
  | ret q r =>
    rcases hJ with ⟨u, hu, hres⟩ | hj
    · refine .inr (.inl ⟨q, u, r, by simpa using hres [] _ (.done r), ?_⟩)
      rw [hu]; simp [runTrace, retEv, wev]
    · exact .inr (.inr (two_le_calls_snoc _ hj))

/-- The invariant along the reachable plays. -/
theorem playInv_reach {h : Body I X} {f : FnName} (hX : ∀ q : (nsig X).Op, q.1.1 = f)
    {s : List (Move (nsig I) (nsig X))} {c : CSt I X} (hs : Reach h s c) :
    PlayInv h f (wtrace s) c := by
  induction hs with
  | nil => exact .inl rfl
  | snoc _ hc ih => exact playInv_step hX ih hc

/-- **The plays of a component with at most one export call**: empty, or the call followed by
a run of its program (with the return when it returned). -/
theorem plays_run {h : Body I X} {f : FnName} (hX : ∀ q : (nsig X).Op, q.1.1 = f)
    {s : List (Move (nsig I) (nsig X))} (hs : s ∈ ofBody h) (h1 : calls f (wtrace s) ≤ 1) :
    wtrace s = [] ∨ ∃ q u r, PRun (h q) u r ∧ wtrace s = runTrace q u r := by
  obtain ⟨c, hc⟩ := hs
  have hJ : PlayInv h f (wtrace s) c := playInv_reach hX hc
  cases c with
  | idle =>
    rcases hJ with h0 | ⟨q, u, a, hr, ht⟩ | hj
    · exact .inl h0
    · exact .inr ⟨q, u, some a, hr, ht⟩
    · omega
  | run q p =>
    rcases hJ with ⟨u, hu, hres⟩ | hj
    · exact .inr ⟨q, u, none, by simpa using hres [] none (.stop p), by rw [hu]; simp [runTrace, retEv]⟩
    · omega
  | wait q m k =>
    rcases hJ with ⟨u, hu, hp, -⟩ | hj
    · exact .inr ⟨q, u ++ [.req m.1.1 m.2], none, hp, by rw [hu]; simp [runTrace, retEv]⟩
    · omega

/-- Runs from a running state extend the play. -/
theorem reach_of_run {h : Body I X} {q : (nsig X).Op} {s₀ : List (Move (nsig I) (nsig X))}
    {p : BProg I} {u : List WEv} {r : Option (Option (List Val))} (hr : PRun p u r)
    (h₀ : Reach h s₀ (.run q p)) :
    ∃ s, s₀ ++ s ∈ ofBody h ∧ wtrace s = u ++ retEv q r := by
  induction hr generalizing s₀ with
  | stop p => exact ⟨[], ⟨_, by simpa using h₀⟩, rfl⟩
  | done a => exact ⟨[.inr (.ans q a)], ⟨_, h₀.snoc (.ret q a)⟩, rfl⟩
  | ask m k => exact ⟨[.inl (.ask m)], ⟨_, h₀.snoc (.call q m k)⟩, rfl⟩
  | step m k n _ ih =>
    have h₁ : Reach h (s₀ ++ [.inl (.ask m), .inl (.ans m n)]) (.run q (k n)) := by
      simpa using (h₀.snoc (.call q m k)).snoc (.reply q m k n)
    obtain ⟨s, hs, ht⟩ := ih h₁
    refine ⟨[.inl (.ask m), .inl (.ans m n)] ++ s, by simpa using hs, ?_⟩
    have hw : wtrace ([.inl (.ask m), .inl (.ans m n)] ++ s) =
        [.req m.1.1 m.2, .imp m.1.1 m.2 n] ++ wtrace s := List.map_append
    rw [hw, ht]; rfl

/-- **Every run of the program of an export call is a play of the component.** -/
theorem play_of_run {h : Body I X} {q : (nsig X).Op} {u : List WEv}
    {r : Option (Option (List Val))} (hr : PRun (h q) u r) :
    ∃ s ∈ ofBody h, wtrace s = runTrace q u r := by
  obtain ⟨s, hs, ht⟩ := reach_of_run hr (Reach.nil.snoc (.ask q))
  refine ⟨_, hs, ?_⟩
  have hw : wtrace ([] ++ [Sum.inr (Ev.ask q)] ++ s) = .call q.1.1 q.2 :: wtrace s :=
    List.map_append
  rw [hw, ht]; rfl

/-! ## Transferring guarantees -/

/-- `Spec.Partial` at one invocation depends only on the specification there. -/
theorem partial_mono_at {S S' : Spec} {i : Input} {s : Seen} (h : S.Partial i s)
    (hS : ∀ o, S i o → S' i o) : S'.Partial i s := by
  obtain ⟨o, ho, hle⟩ := h
  exact ⟨o, hS _ ho, hle⟩

/-- **A guarantee of `ofBody h'` holds of `ofBody h`** when each run of `h` with at most one
call that the assumption admits is a run of `h'` (the plays are then plays of `h'`). -/
theorem guar_of_runs {h h' : Body I X} {V : View} (hX : ∀ q : (nsig X).Op, q.1.1 = V.run)
    {A : List WEv → Prop} {S S' : Spec} {i : Input}
    (h₀ : (ag (I := I) (X := X) A (V.Guar S' i)).holds (ofBody h'))
    (hS : ∀ o, S' i o → S i o)
    (hsim : ∀ q u r, PRun (h q) u r → A (runTrace q u r) → PRun (h' q) u r) :
    (ag (I := I) (X := X) A (V.Guar S i)).holds (ofBody h) := by
  intro s hs hA h1
  rcases plays_run hX hs h1 with h0 | ⟨q, u, r, hr, ht⟩
  · have hA0 : A (wtrace ([] : List (Move (nsig I) (nsig X)))) := by
      have he : wtrace ([] : List (Move (nsig I) (nsig X))) = wtrace s := h0.symm
      rw [he]; exact hA
    have hg : V.Guar S' i (wtrace ([] : List (Move (nsig I) (nsig X)))) :=
      h₀ [] (ofBody h').nil_mem hA0
    have hg' : S'.Partial i (V.seen i (wtrace ([] : List (Move (nsig I) (nsig X))))) :=
      hg (by simp [wtrace, calls])
    rw [h0]; exact partial_mono_at hg' hS
  · obtain ⟨s', hs', ht'⟩ := play_of_run (hsim q u r hr (ht ▸ hA))
    have hg : V.Guar S' i (wtrace s') := h₀ s' hs' (ht' ▸ ht ▸ hA)
    exact partial_mono_at (by simpa [ht, ht'] using hg (ht' ▸ ht ▸ h1)) hS

end Silmaril.Wasi.Cli

end
