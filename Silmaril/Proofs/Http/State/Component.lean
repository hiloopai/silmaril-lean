module

public import Silmaril.Http.State.Component.Defs
public import Silmaril.Http.State.Thms

@[expose] public section

/-!
# Proofs: component-state servers

* `counter_resp`, `counter_pairwise`: a sequential run of a counter from `n` answers `f m`
  for `m ≥ n`, pairwise differently when `f` is injective;
* `pairwise_mem_ne`: a pairwise relation holds between distinct members (when symmetric);
* **`counter_distinct`**: in every history of a counter server whose `f` is injective,
  distinct requests get distinct answers (however the requests overlap);
* `perRequest_counter`, `perRequest_kv_get`: with a fresh instance per request.
-/

namespace Silmaril.Proofs.Http.State.Component

open Silmaril.Http.State Silmaril.Http.State.Component Silmaril.Net.Http

variable {Req Resp : Type}

theorem counter_resp {f : Nat → Resp} {n n' : Nat} {L : List (Op Req Resp)}
    (h : Legal (counterBy f) n L n') : ∀ o ∈ L, ∃ m, n ≤ m ∧ o.resp = f m := by
  induction L generalizing n with
  | nil => intro o ho; cases ho
  | cons x L ih =>
    obtain ⟨s', ⟨h1, rfl⟩, h2⟩ := h
    intro o ho
    rcases List.mem_cons.1 ho with rfl | ho
    · exact ⟨n, Nat.le_refl n, h1⟩
    · obtain ⟨m, hm, e⟩ := ih h2 o ho; exact ⟨m, by omega, e⟩

theorem counter_pairwise {f : Nat → Resp} (hf : Function.Injective f) {n n' : Nat}
    {L : List (Op Req Resp)} (h : Legal (counterBy f) n L n') :
    L.Pairwise fun x y => x.resp ≠ y.resp := by
  induction L generalizing n with
  | nil => exact List.Pairwise.nil
  | cons x L ih =>
    obtain ⟨s', ⟨h1, rfl⟩, h2⟩ := h
    refine List.Pairwise.cons (fun y hy => ?_) (ih h2)
    obtain ⟨m, hm, e⟩ := counter_resp h2 y hy
    rw [h1, e]; intro he; have := hf he; omega

theorem pairwise_mem_ne {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a)
    {l : List α} (h : l.Pairwise R) {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    R a b := by
  induction l with
  | nil => cases ha
  | cons x l ih =>
    rcases List.pairwise_cons.1 h with ⟨hx, hl⟩
    have ha' := List.mem_cons.1 ha
    have hb' := List.mem_cons.1 hb
    rcases ha' with hax | ha'
    · rcases hb' with hbx | hb'
      · exact absurd (hax.trans hbx.symm) hne
      · subst hax; exact hx b hb'
    · rcases hb' with hbx | hb'
      · subst hbx; exact hs _ _ (hx a ha')
      · exact ih hl ha' hb'

theorem counter_distinct {f : Nat → Resp} (hf : Function.Injective f) {H : Hist Req Resp}
    (hH : (counterServer f).Hists H) {i j : Nat} {a b : Resp} (hi : Ev.ret i a ∈ H)
    (hj : Ev.ret j b ∈ H) (hij : i ≠ j) : a ≠ b := by
  obtain ⟨L, ⟨⟨_, hL⟩, -, -, hans⟩, -⟩ := closed_linearizable (counterBy f) 0 H hH
  obtain ⟨x, hx, rfl, rfl⟩ := hans i a hi
  obtain ⟨y, hy, rfl, rfl⟩ := hans _ b hj
  exact pairwise_mem_ne (fun _ _ h e => h e.symm) (counter_pairwise hf hL) hx hy
    (fun e => hij (congrArg Op.id e))

theorem perRequest_counter {f : Nat → Resp} {H : Hist Req Resp}
    (hH : (Server.perRequest (counterBy f) 0).Hists H) {i : Nat} {r : Req} {s : Resp}
    (hc : Ev.call i r ∈ H) (hr : Ev.ret i s ∈ H) : s = f 0 :=
  let ⟨_, h, _⟩ := perRequest_answer hH hc hr; h

theorem perRequest_kv_get {S₀ : Store} {H : Hist Request Response}
    (hH : (Server.perRequest kv S₀).Hists H) {i : Nat} {r : Request} {s : Response}
    (hc : Ev.call i r ∈ H) (hr : Ev.ret i s ∈ H) (hm : r.method = .get) :
    s = S₀.get r.target := by
  obtain ⟨S', h⟩ := perRequest_answer hH hc hr
  simp only [kv, Atomic.ofFun, storeStep, hm] at h
  exact (Prod.mk.inj h).1.symm

end Silmaril.Proofs.Http.State.Component
