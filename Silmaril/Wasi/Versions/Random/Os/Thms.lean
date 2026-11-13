module

public import Silmaril.Wasi.Versions.Random.Os.Defs
public import Silmaril.Wasi.Versions.Random.Thms
public import Silmaril.Wasi.Versions.Stateful.Thms
public import Silmaril.Wasi.Comp.Thms

@[expose] public section

/-!
# `wasi:random` 0.3 over 0.2: the OS image

PROVED (standard axioms):

* `osEvR_to2`: a 0.3 call and the 0.2 call it is forwarded to have the same OS image.
* **`reach_os`**: for every play `s` of `p3OverP2R` reaching the control state `c`, the OS image
  of the 0.2 answers is the OS image of the 0.3 returns followed by the pending answer
  (`osTraceR ch (hostView (wtrace s)) = osTraceR ch (retAsImp (wtrace s)) ++ pendR ch c`).
* **`p3OverP2R_os`**: over the concrete 0.2 host `rand2Impl src`, every play of the composite
  returns device bytes in order: its OS image is `devTrace ch src m`, the first `m` bytes of
  the device read on `ch`, for some `m`. This is the `IoSpec` connection of the composite: the
  same LPS `readEv` events as the 0.2 host's (`rand2Impl_os`).
-/

namespace Silmaril.Wasi.Versions.Random

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- A forwarded call has the image of the original. -/
theorem osEvR_to2 (ch : Silmaril.Process.LPS.Word) {f : FnName} (hf : f ∈ rand3Fns)
    (a : List Val) (n : Option (List Val)) : osEvR ch (.imp (to2 f) a n) = osEvR ch (.imp f a n) := by
  simp only [rand3Fns_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases n with _ | ⟨_ | ⟨v, _ | _⟩⟩ <;>
    rcases hf with rfl | rfl | rfl | rfl | rfl <;>
    simp [osEvR, to2, randBytes2, randBytes3, insBytes2, insBytes3, randU64_2, randU64_3,
      insU64_2, insU64_3, insSeed2, insSeed3]

/-- The OS image of an appended event list. -/
theorem osTraceR_append (ch : Silmaril.Process.LPS.Word) (t u : List WEv) :
    osTraceR ch (t ++ u) = osTraceR ch t ++ osTraceR ch u := by
  simp [osTraceR]

/-- One more move: the host view and the returns grow by the move's answer or return. -/
theorem views_snoc (t : List (Move (nsig rand2Fns) (nsig rand3Fns)))
    (o : Move (nsig rand2Fns) (nsig rand3Fns)) :
    hostView (wtrace (t ++ [o])) = hostView (wtrace t) ++ hostView [wev o] ∧
      retAsImp (wtrace (t ++ [o])) = retAsImp (wtrace t) ++ retAsImp [wev o] := by
  rw [wtrace_concat]
  exact ⟨hostView_append _ _, List.filterMap_append⟩

/-- **The OS image along the plays of `p3OverP2R`.** -/
theorem reach_os (ch : Silmaril.Process.LPS.Word) {s : List (Move (nsig rand2Fns) (nsig rand3Fns))}
    {c : SCSt Unit rand2Fns rand3Fns} (hs : SReach p3OverP2R () s c) :
    RShape c ∧ osTraceR ch (hostView (wtrace s)) =
      osTraceR ch (retAsImp (wtrace s)) ++ pendR ch c := by
  induction hs with
  | nil => exact ⟨.idle, rfl⟩
  | @snoc t c c' o _ hc ih =>
    show RShape c' ∧ osTraceR ch (hostView (wtrace (t ++ [o]))) =
      osTraceR ch (retAsImp (wtrace (t ++ [o]))) ++ pendR ch c'
    obtain ⟨hsh, heq⟩ := ih
    obtain ⟨hh, hr⟩ := views_snoc t o
    rw [hh, hr, osTraceR_append, osTraceR_append, heq]
    cases hc with
    | ask s q =>
      cases hsh
      exact ⟨.start q, by simp [pendR, p3OverP2R, hostView, retAsImp, retImp, wev, WEv.isImp, osTraceR]⟩
    | call q m k =>
      cases hsh with
      | start q =>
        exact ⟨.wait q, by simp [pendR, hostView, retAsImp, retImp, wev, WEv.isImp, osTraceR]⟩
    | reply q m k n =>
      cases hsh with
      | wait q =>
        refine ⟨.done q n, ?_⟩
        show _ ++ osTraceR ch [WEv.imp (to2 q.1.1) q.2 n] = (_ ++ osTraceR ch []) ++ _
        simp [pendR, osTraceR, osEvR_to2 ch q.1.2]
    | ret q s r =>
      cases hsh with
      | done q n =>
        exact ⟨.idle, by simp [pendR, hostView, retAsImp, retImp, wev, WEv.isImp, osTraceR]⟩

/-- A prefix of the device trace is a device trace. -/
theorem devTrace_prefix (ch : Silmaril.Process.LPS.Word) (src : Nat → BitVec 8) {l l' :
    List Silmaril.Process.LPS.Event} {n : Nat} (h : devTrace ch src n = l ++ l') :
    l = devTrace ch src l.length := by
  have hl : l.length ≤ n := by
    have := congrArg List.length h
    simp [devTrace] at this
    omega
  have ht : (devTrace ch src n).take l.length = l := by rw [h]; simp
  calc l = (devTrace ch src n).take l.length := ht.symm
    _ = devTrace ch src l.length := by
      simp only [devTrace]
      rw [← List.map_take, List.take_range, Nat.min_eq_left hl]

/-- **The OS image of `wasi:random` 0.3 over the concrete 0.2 host**: the composite returns
device bytes in order. -/
theorem p3OverP2R_os {Y : Sig.{0}} (ch : Silmaril.Process.LPS.Word) (src : Nat → BitVec 8) :
    ∀ p ∈ link (concrete (Y := Y) (rand2Impl src)) (ofSBody p3OverP2R ()),
      ∃ m, osTraceR ch (htrace p) = devTrace ch src m := by
  intro p hp
  have hG := link_sat (η := concrete (Y := Y) (rand2Impl src)) (σ := ofSBody p3OverP2R ())
    (A := Follows (rand2Impl src))
    (G := fun t => ∃ m, osTraceR ch (retAsImp t) = devTrace ch src m)
    (fun s hs hA => by
      obtain ⟨c, hs⟩ := hs
      obtain ⟨-, heq⟩ := reach_os ch hs
      rw [rand2Impl_os ch src hA] at heq
      exact ⟨_, retAsImp_expView (wtrace s) ▸ devTrace_prefix ch src heq⟩)
    (fun _ hs => hs.2) p hp
  rw [htrace_eq_retAsImp]
  exact hG

end Silmaril.Wasi.Versions.Random
