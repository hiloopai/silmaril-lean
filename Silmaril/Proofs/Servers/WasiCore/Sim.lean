module

public import Silmaril.Servers.WasiCore.Defs

/-!
# Simulation of bodies over typed hosts

`sim_runsTy`: a body `d` each of whose programs simulates the program of `h` on typed answers
(`Sim AnsTy`) runs `h` over typed hosts: every play of `ofBody d` whose answers are typed is a
play of `ofBody h`. The proof follows a play of `ofBody d` move by move with a play of
`ofBody h`, relating the control states (`Rel`).
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.WasiCore

open Silmaril.Games Silmaril.Wasi Silmaril.Servers.WasiHttp Silmaril.Servers.WasiCore
open Silmaril.Wasm.Component (Val)

variable {I X : Set FnName} {T : FnName → Option (List Val) → Prop}

/-- Related control states. -/
def Rel (T : FnName → Option (List Val) → Prop) : CSt I X → CSt I X → Prop
  | .idle, .idle => True
  | .run q p, .run q' p' => q = q' ∧ Sim T p p'
  | .wait q m k, .wait q' m' k' => q = q' ∧ m = m' ∧ ∀ n, T m.1.1 n → Sim T (k n) (k' n)
  | _, _ => False

/-- The typing of the answer of a move. -/
def TyMove (T : FnName → Option (List Val) → Prop) : Move (nsig I) (nsig X) → Prop
  | .inl (.ans m n) => T m.1.1 n
  | _ => True

theorem sim_reach {d h : Body I X} (hs : ∀ q, Sim T (d q) (h q))
    {s : List (Move (nsig I) (nsig X))} {c : CSt I X} (hr : Reach d s c)
    (ht : ∀ o ∈ s, TyMove T o) : ∃ c', Reach h s c' ∧ Rel T c c' := by
  induction hr with
  | nil => exact ⟨.idle, .nil, trivial⟩
  | @snoc s c c'' o hr hc ih =>
    obtain ⟨c', hr', hrel⟩ := ih fun o ho => ht o (List.mem_append_left _ ho)
    have hto : TyMove T o := ht o (List.mem_append_right _ (List.mem_singleton_self _))
    cases hc with
    | ask q =>
      cases c' with
      | idle => exact ⟨_, hr'.snoc (.ask q), rfl, hs q⟩
      | run => exact hrel.elim
      | wait => exact hrel.elim
    | call q m k =>
      cases c' with
      | run q' p' =>
        obtain ⟨rfl, hp⟩ := hrel
        cases hp with
        | call _ _ k' hk => exact ⟨_, hr'.snoc (.call q m k'), rfl, rfl, hk⟩
      | idle => exact hrel.elim
      | wait => exact hrel.elim
    | reply q m k n =>
      cases c' with
      | wait q' m' k' =>
        obtain ⟨rfl, rfl, hk⟩ := hrel
        exact ⟨_, hr'.snoc (.reply q m k' n), rfl, hk n hto⟩
      | idle => exact hrel.elim
      | run => exact hrel.elim
    | ret q r =>
      cases c' with
      | run q' p' =>
        obtain ⟨rfl, hp⟩ := hrel
        cases hp with
        | pure => exact ⟨_, hr'.snoc (.ret q r), trivial⟩
      | idle => exact hrel.elim
      | wait => exact hrel.elim

/-- One import call of the simulation, by the next calls and the continuations (so that each
side can be computed separately). -/
theorem sim_step {p p' : BProg I} {m : (nsig I).Op} (hp : next p = some m)
    (hp' : next p' = some m) (h : ∀ n, T m.1.1 n → Sim T (cont p n) (cont p' n)) :
    Sim T p p' := by
  cases p with
  | pure => cases hp
  | call m1 k =>
    cases p' with
    | pure => cases hp'
    | call m2 k' =>
      cases hp; cases hp'; exact .call _ k k' h

/-- The end of the simulation. -/
theorem sim_pure {p p' : BProg I} {r : Option (List Val)} (hp : p = .pure r) (hp' : p' = .pure r) :
    Sim T p p' := by
  subst hp hp'; exact .pure r

/-- **Simulation on typed answers gives runs over typed hosts.** -/
theorem sim_runsTy {d h : Body proxyImports X} (hs : ∀ q, Sim AnsTy (d q) (h q)) :
    RunsTy (ofBody d) h := by
  rintro s ⟨c, hr⟩ ht
  obtain ⟨c', hr', -⟩ := sim_reach hs hr fun o ho => by
    have := ht (wev o) (List.mem_map_of_mem ho)
    rcases o with (_ | ⟨m, n⟩) | _
    · trivial
    · exact this
    · trivial
  exact ⟨c', hr'⟩

end Silmaril.Proofs.Servers.WasiCore
