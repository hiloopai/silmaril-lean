module

public import Silmaril.Raw.Wasi.Versions.P2OverP3.FsTop
public import Silmaril.Raw.Wasi.Versions.P2OverP3.FsPoll

/-!
# Proofs (unrefined): every export call, and the invariant method

* `wp_progF`: every export call of `p2OverP3Fs` establishes `PostF`;
* `wpInvF`: the invariant method applies with `JF`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Versions.P2

variable {F : BitVec 32 → List (BitVec 8)}

/-- A `p2OverP3` call routed to `baseP`. -/
theorem wp_baseAny (cap : Nat) {s : StF} {f : FnName} {a : List Val} {g : Option (BitVec 64)}
    {q2 : RdSt} {qT : ClockSt × RdSt} (hJ : JF s qT ((s.io, g, (), ()), q2)) (hf : f ∈ exp2)
    (hdisp : (ioOp f).isStream = true → s.fs (selfOf a) = none) :
    Wp (t3F F) (baseP cap s f a) (PostF F s f a g q2) qT := by
  by_cases hn : f = clockNow
  · subst hn; exact wp_base_now cap hJ
  · exact wp_base cap hJ hf hn hdisp

/-- **Every export call establishes `PostF`.** -/
theorem wp_progF (cap : Nat) (s : StF) {f : FnName} (hf : f ∈ expF) (a : List Val)
    (g : Option (BitVec 64)) (q2 : RdSt) (qT : ClockSt × RdSt)
    (hJ : JF s qT ((s.io, g, (), ()), q2)) :
    Wp (t3F F) (progF cap s f a) (PostF F s f a g q2) qT := by
  unfold progF
  split
  · next h1 => subst h1; exact wp_getDirs hJ
  split
  · next h2 => subst h2; exact wp_openAt hJ
  split
  · next h3 => subst h3; exact wp_rvs hJ
  split
  · next h4 => subst h4; exact wp_fdDrop hJ
  next h1 h2 h3 h4 =>
  have hmem : f ∈ exp2 := mem_exp2_of hf h1 h2 h3 h4
  split
  · next hp => exact wp_pollF hJ hp hmem
  split
  · next e he =>
    split
    · next hm => exact wp_fsStream hJ he hm hmem
    · next hm =>
      exact wp_baseAny cap hJ hmem fun hst => by
        rw [fsMethod_stream (Bool.of_not_eq_true hm)] at hst; exact absurd hst (by decide)
  · next he => exact wp_baseAny cap hJ hmem fun _ => he

/-- **The invariant method applies.** -/
theorem wpInvF (cap : Nat) (F : BitVec 32 → List (BitVec 8)) :
    WpInv (bodyF cap) StF.init (t3F F) (p2F F) JF where
  init := by
    show ioInit = ioInit ∧ ClkLe none none ∧ RdInv StF.init [] []
    have hc : ClkLe none none := fun x hx => absurd hx (Option.not_mem_none x)
    exact ⟨rfl, hc, rdInv_init⟩
  call := fun s qT qG q hJ => by
    obtain ⟨⟨f, hf⟩, a⟩ := q
    obtain ⟨⟨io, g, ⟨⟩, ⟨⟩⟩, q2⟩ := qG
    have hio : io = s.io := hJ.1
    subst hio
    unfold bodyF
    rw [Wp.bind]
    refine Wp.mono (fun x q hx => ?_) (wp_progF cap s hf a g q2 qT hJ)
    exact hx

end Silmaril.Wasi.Versions.P2OverP3
