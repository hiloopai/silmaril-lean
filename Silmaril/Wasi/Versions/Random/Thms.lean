module

public import Silmaril.Wasi.Versions.Random.Defs
public import Silmaril.Wasi.Versions.Random.Wit.Thms
public import Silmaril.Wasi.Theory.Thms
public import Silmaril.Wasi.Host.Thms

@[expose] public section

/-!
# `wasi:random` 0.2 and 0.3: hosts, separation, OS image

PROVED (standard axioms):

* `rand2Impl_sat`, `rand3Impl_sat`: the concrete hosts over a device are models of `randTh2`
  and `randTh3`; `loose_sat` gives the loose hosts.
* `shortOk_of_exactOk`: an exact answer is an admissible short answer (the 0.2 constraint is
  stronger); `short_not_exact`: a one-byte answer to `get-random-bytes(2)` is accepted by 0.3
  and its 0.2 counterpart is not (`ok3_short`, `ok2_short`).
* **OS image** (`rand2Impl_os`, `rand3Impl_os`): every run of either host reads the device
  sequentially; its image `osTraceR ch t` is the first `drawn t` device bytes read on `ch`.
-/

namespace Silmaril.Wasi.Versions.Random

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Encodings -/

/-- The bytes of an encoded byte list. -/
@[simp] theorem bytesOf_bytesV (bs : List (BitVec 8)) : bytesOf (bytesV bs) = bs := by
  simp [bytesOf, bytesV, List.filterMap_map]

/-- An encoded byte list is a `list<u8>`. -/
@[simp] theorem allU8_bytesV (bs : List (BitVec 8)) : allU8 (bytesV bs) = true := by
  simp [allU8, bytesV]

/-- A byte list answer of a given length. -/
theorem bytesAns_bytesV (P : Nat → Bool) (bs : List (BitVec 8)) :
    bytesAns P (some [bytesV bs]) = P bs.length := by
  simp [bytesAns]

/-- An exact answer is an admissible short answer. -/
theorem shortOk_of_exactOk {n k : Nat} (h : exactOk n k = true) : shortOk n k = true := by
  have hk : k = n := by simpa [exactOk] using h
  subst hk
  by_cases h0 : k = 0
  · simp [shortOk, h0]
  · simp [shortOk, h0]; omega

/-- `min n (c + 1)` is an admissible short length. -/
theorem shortOk_min (n c : Nat) : shortOk n (min n (c + 1)) = true := by
  by_cases h0 : n = 0
  · simp [shortOk, h0]
  · simp [shortOk, h0]; omega

/-! ## The hosts are models -/

/-- Every answer of the 0.2 host is accepted. -/
theorem rand2Impl_ok (src : Nat → BitVec 8) (p : List WEv) (f : FnName) (a : List Val) :
    ok2 (.imp f a (rand2Impl src p f a)) = true := by
  rw [ok2_eq_hand]
  unfold ok2H rand2Impl
  by_cases h1 : f = randBytes2
  · subst h1
    rcases a with _ | ⟨_ | _ | _ | _ | _ | _ | _ | n | _, _ | _⟩ <;>
      simp [bytesM, bytesAns_bytesV, exactOk, devBytes]
  by_cases h2 : f = insBytes2
  · subst h2
    rcases a with _ | ⟨_ | _ | _ | _ | _ | _ | _ | n | _, _ | _⟩ <;>
      simp [bytesM, bytesAns_bytesV, exactOk, insBytes2, randBytes2]
  by_cases h3 : f = randU64_2 ∨ f = insU64_2
  · rcases h3 with rfl | rfl <;> rcases a with _ | _ <;> simp [nullM, u64Ans, randBytes2, insBytes2, randU64_2, insU64_2]
  by_cases h4 : f = insSeed2
  · subst h4
    rcases a with _ | _ <;> simp [nullM, seedAns, randBytes2, insBytes2, randU64_2, insU64_2, insSeed2]
  simp [h1, h2, h3, h4]

/-- **The concrete 0.2 host is a model of `randTh2`.** -/
theorem rand2Impl_sat {Y : Silmaril.Games.Sig.{0}} {I : Set FnName} (src : Nat → BitVec 8) :
    (hostSat randTh2.Accepts).holds (concrete (Y := Y) (I := I) (rand2Impl src)) :=
  concrete_sat _ fun _ ht => follows_pointwise (rand2Impl_ok src)
    (fun e he => by cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-- Every answer of the 0.3 host is accepted. -/
theorem rand3Impl_ok (src : Nat → BitVec 8) (c : Nat) (p : List WEv) (f : FnName) (a : List Val) :
    ok3 (.imp f a (rand3Impl src c p f a)) = true := by
  rw [ok3_eq_hand]
  unfold ok3H rand3Impl
  by_cases h1 : f = randBytes3
  · subst h1
    rcases a with _ | ⟨_ | _ | _ | _ | _ | _ | _ | n | _, _ | _⟩ <;>
      simp [bytesM, bytesAns_bytesV, devBytes, shortOk_min]
  by_cases h2 : f = insBytes3
  · subst h2
    rcases a with _ | ⟨_ | _ | _ | _ | _ | _ | _ | n | _, _ | _⟩ <;>
      simp [bytesM, bytesAns_bytesV, shortOk_min, insBytes3, randBytes3]
  by_cases h3 : f = randU64_3 ∨ f = insU64_3
  · rcases h3 with rfl | rfl <;> rcases a with _ | _ <;> simp [nullM, u64Ans, randBytes3, insBytes3, randU64_3, insU64_3]
  by_cases h4 : f = insSeed3
  · subst h4
    rcases a with _ | _ <;> simp [nullM, seedAns, randBytes3, insBytes3, randU64_3, insU64_3, insSeed3]
  simp [h1, h2, h3, h4]

/-- **The concrete 0.3 host is a model of `randTh3`.** -/
theorem rand3Impl_sat {Y : Silmaril.Games.Sig.{0}} {I : Set FnName} (src : Nat → BitVec 8) (c : Nat) :
    (hostSat randTh3.Accepts).holds (concrete (Y := Y) (I := I) (rand3Impl src c)) :=
  concrete_sat _ fun _ ht => follows_pointwise (rand3Impl_ok src c)
    (fun e he => by cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-! ## Separation -/

/-- A one-byte answer to `get-random-bytes(2)` is a 0.3 short read. -/
theorem ok3_short : ok3 (.imp randBytes3 [.u64 2] (some [bytesV [0]])) = true := by
  rw [ok3_eq_hand]; decide

/-- The same answer to the 0.2 call is rejected. -/
theorem ok2_short : ok2 (.imp randBytes2 [.u64 2] (some [bytesV [0]])) = false := by
  rw [ok2_eq_hand]; decide

/-- **0.3's short reads are not 0.2 answers.** -/
theorem short_not_exact :
    randTh3.Accepts [.imp randBytes3 [.u64 2] (some [bytesV [0]])] ∧
      ¬ randTh2.Accepts [.imp randBytes2 [.u64 2] (some [bytesV [0]])] := by
  refine ⟨(pointwise_accepts_iff _ _).2 ?_, fun h => ?_⟩
  · intro e he
    rw [List.mem_singleton.1 he]
    exact ok3_short
  · have h' := (pointwise_accepts_iff _ _).1 h _ List.mem_cons_self
    rw [ok2_short] at h'
    exact Bool.noConfusion h'

/-! ## The OS image -/

/-- An answer read in order from the device after the answers `t`. -/
def InOrder (ch : Silmaril.Process.LPS.Word) (src : Nat → BitVec 8) (t : List WEv) (e : WEv) :
    Prop :=
  osEvR ch e = (List.range (drawnEv e)).map fun i => .readEv ch (src (drawn t + i))

/-- The image of a run whose answers are all read in order is the device prefix. -/
theorem os_of_inOrder (ch : Silmaril.Process.LPS.Word) (src : Nat → BitVec 8) {impl : Impl}
    (hans : ∀ p f a, InOrder ch src p (.imp f a (impl p f a)))
    (hother : ∀ e : WEv, e.isImp = false → osEvR ch e = [] ∧ drawnEv e = 0) :
    ∀ {t : List WEv}, Follows impl t → osTraceR ch t = devTrace ch src (drawn t) := by
  intro t ht
  induction t using List.reverseRecOn with
  | nil => rfl
  | append_singleton t e ih =>
    have ht' : Follows impl t := (prefixClosed_follows impl).2 (List.prefix_append t [e]) ht
    have he : InOrder ch src t e := by
      cases e with
      | imp f a r =>
        have hr : r = impl t f a := ht t f a r (List.prefix_refl _)
        rw [hr]
        exact hans t f a
      | req f a => simp [InOrder, hother (.req f a) rfl]
      | call f a => simp [InOrder, hother (.call f a) rfl]
      | ret f a r => simp [InOrder, hother (.ret f a r) rfl]
    have hd : drawn (t ++ [e]) = drawn t + drawnEv e := by simp [drawn]
    rw [show osTraceR ch (t ++ [e]) = osTraceR ch t ++ osEvR ch e by simp [osTraceR], ih ht', he,
      hd]
    simp [devTrace, List.range_add]

/-- Events that are not answers have no image. -/
theorem osEvR_not_imp (ch : Silmaril.Process.LPS.Word) (e : WEv) (he : e.isImp = false) :
    osEvR ch e = [] ∧ drawnEv e = 0 := by
  cases e <;> simp_all [osEvR, drawnEv, WEv.isImp]

/-- Answers outside the secure byte functions have no image. -/
theorem inOrder_other (ch : Silmaril.Process.LPS.Word) (src : Nat → BitVec 8) (t : List WEv)
    {f : FnName} (a : List Val) (r : Option (List Val)) (h2 : f ≠ randBytes2) (h3 : f ≠ randBytes3) :
    InOrder ch src t (.imp f a r) := by
  rcases r with _ | ⟨_ | ⟨v, _ | _⟩⟩ <;> simp [InOrder, osEvR, drawnEv, h2, h3]

/-- A device answer is read in order. -/
theorem inOrder_dev (ch : Silmaril.Process.LPS.Word) (src : Nat → BitVec 8) (t : List WEv)
    {f : FnName} (a : List Val) (n : Nat) (hf : f = randBytes2 ∨ f = randBytes3) :
    InOrder ch src t (.imp f a (some [bytesV (devBytes src t n)])) := by
  simp [InOrder, osEvR, drawnEv, hf, devBytes]

/-- Every answer of the 0.2 host is read in order. -/
theorem rand2Impl_inOrder (ch : Silmaril.Process.LPS.Word) (src : Nat → BitVec 8) (p : List WEv)
    (f : FnName) (a : List Val) : InOrder ch src p (.imp f a (rand2Impl src p f a)) := by
  by_cases h1 : f = randBytes2
  · subst h1
    rcases a with _ | ⟨_ | _ | _ | _ | _ | _ | _ | n | _, _ | _⟩ <;>
      first
        | exact inOrder_dev ch src p _ _ (Or.inl rfl)
        | simp [rand2Impl, InOrder, osEvR, drawnEv]
  by_cases h3 : f = randBytes3
  · subst h3
    simp [rand2Impl, InOrder, osEvR, drawnEv, randBytes2, randBytes3, insBytes2, randU64_2,
      insU64_2, insSeed2]
  exact inOrder_other ch src p a _ h1 h3

/-- **The OS image of the 0.2 host**: the device prefix. -/
theorem rand2Impl_os (ch : Silmaril.Process.LPS.Word) (src : Nat → BitVec 8) {t : List WEv}
    (ht : Follows (rand2Impl src) t) : osTraceR ch t = devTrace ch src (drawn t) :=
  os_of_inOrder ch src (rand2Impl_inOrder ch src) (osEvR_not_imp ch) ht

/-- Every answer of the 0.3 host is read in order. -/
theorem rand3Impl_inOrder (ch : Silmaril.Process.LPS.Word) (src : Nat → BitVec 8) (c : Nat)
    (p : List WEv) (f : FnName) (a : List Val) :
    InOrder ch src p (.imp f a (rand3Impl src c p f a)) := by
  by_cases h1 : f = randBytes3
  · subst h1
    rcases a with _ | ⟨_ | _ | _ | _ | _ | _ | _ | n | _, _ | _⟩ <;>
      first
        | exact inOrder_dev ch src p _ _ (Or.inr rfl)
        | simp [rand3Impl, InOrder, osEvR, drawnEv]
  by_cases h2 : f = randBytes2
  · subst h2
    simp [rand3Impl, InOrder, osEvR, drawnEv, randBytes2, randBytes3, insBytes3, randU64_3,
      insU64_3, insSeed3]
  exact inOrder_other ch src p a _ h2 h1

/-- **The OS image of the 0.3 host**: the device prefix. -/
theorem rand3Impl_os (ch : Silmaril.Process.LPS.Word) (src : Nat → BitVec 8) (c : Nat)
    {t : List WEv} (ht : Follows (rand3Impl src c) t) : osTraceR ch t = devTrace ch src (drawn t) :=
  os_of_inOrder ch src (rand3Impl_inOrder ch src c) (osEvR_not_imp ch) ht

end Silmaril.Wasi.Versions.Random
