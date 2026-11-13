module

public import Silmaril.Wasi.Examples.Defs
public import Silmaril.Wasi.Comp.Thms
public import Silmaril.Wasi.Theory.Thms
public import Silmaril.Wasi.World.Thms
public import Silmaril.Wasi.Host.Thms
public import Silmaril.Proofs.Wasi.Examples.Hello
public import Silmaril.Proofs.Wasi.Examples.WriteFile

@[expose] public section

/-!
# Example WASI components: correctness for every host

* **`checker_sat`**: the clock checker satisfies `agP clockTh (onExp retTrue)`: under the
  monotonic clock theory, with otherwise uninterpreted imports, `check` always returns `true`.
  **`checker_every_host`**: linked over *any* host satisfying the clock theory (whatever its
  lower interface), every export return of the system is `true`; `checker_tick` instantiates it
  with the concrete tick clock. **`checker_needs_theory`** (a refutation): without the theory
  the guarantee fails, on a play where the clock goes back from `5` to `3`.
* `checker_in_cli`: the same sentence for the checker read as a component of the larger world
  with all the imports of `cliWorld` (a reduct along a world morphism, `World.ag_reduct`).
* **`hello_sat`**, **`writeFile_sat`**: `hello` and `writeFile` use and drop stream handles and
  descriptors only while they are live, with no assumption on the host
  (`agP topP stdoutHandles`, `agP topP fsHandles`); `hello_every_host`, `writeFile_every_host`:
  in every interaction with every host. Proofs in `Silmaril.Proofs.Wasi.Examples`.
-/

namespace Silmaril.Wasi.Examples

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Protocol steps -/

/-- An answer of `now` accepted by the clock theory is an instant, not smaller than the last. -/
theorem nowStep_inv {q q' : Option (BitVec 64)} {n : Option (List Val)} (h : nowStep q n = some q') :
    ∃ x, n = some [.u64 x] ∧ q' = some x ∧ q.all (fun l => decide (l ≤ x)) = true := by
  unfold nowStep at h
  split at h
  · rename_i x
    by_cases hx : q.all (fun l => decide (l ≤ x)) = true
    · rw [ite_eq_left hx] at h
      exact ⟨x, rfl, (Option.some.inj h).symm, hx⟩
    · rw [ite_eq_right hx] at h
      exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The clock theory on an answer of `now`. -/
theorem clock_run_now {qT qT' : Option (BitVec 64)} {a : List Val} {n : Option (List Val)}
    (h : clockTh.run qT (hostView [WEv.imp clockNow a n]) = some qT') : nowStep qT n = some qT' := by
  have h1 : clockTh.run qT (hostView [WEv.imp clockNow a n]) =
      (clockStep qT (WEv.imp clockNow a n)).bind fun q => some q := rfl
  have h2 : clockStep qT (WEv.imp clockNow a n) = nowStep qT n := ite_eq_left rfl
  rw [h1, h2] at h
  cases hn : nowStep qT n <;> simp_all

/-- A protocol does not move on an event outside the host view. -/
theorem run_hostView_of_not_imp {S : Type} {T : Protocol S WEv} {q q' : S} {e : WEv}
    (he : e.isImp = false) (h : T.run q (hostView [e]) = some q') : q' = q := by
  rw [hostView_single_of_not_imp he] at h
  exact (Option.some.inj h).symm

/-- `onExp G` skips non-export events. -/
theorem onExp_step_of_not_exp {S : Type} {G : Protocol S WEv} {q : S} {e : WEv}
    (he : e.isExp = false) : (onExp G).step q e = some q := by
  simp [onExp, he]

/-! ## The clock checker -/

/-- The control state of the checker and the clock theory's state. -/
def CheckInv (c : CSt clocksWorld.imports clocksWorld.exports) (qT : Option (BitVec 64))
    (_ : Unit) : Prop :=
  c = .idle ∨ (∃ q, c = .run q checkProg) ∨ (∃ q, c = .wait q nowOp checkK1) ∨
    (∃ q x, qT = some x ∧ c = .run q (checkK1 (some [.u64 x]))) ∨
    (∃ q x, qT = some x ∧ c = .wait q nowOp (checkK2 (some [.u64 x]))) ∨
    (∃ q, c = .run q (.pure (some [.bool true])))

/-- The conclusion of one step of the checker. -/
abbrev CheckStep (o : Move (nsig clocksWorld.imports) (nsig clocksWorld.exports))
    (c' : CSt clocksWorld.imports clocksWorld.exports) (qT' : Option (BitVec 64)) : Prop :=
  ∃ qG', (onExp retTrue).step () (wev o) = some qG' ∧ CheckInv c' qT' qG'

theorem check_idle {o c' qT qT'} (hc : CStep checker .idle o c')
    (hT : clockTh.run qT (hostView [wev o]) = some qT') : CheckStep o c' qT' := by
  obtain ⟨q, rfl, rfl⟩ := hc.idle_inv
  exact ⟨(), rfl, Or.inr (Or.inl ⟨q, rfl⟩)⟩

theorem check_start {q o c' qT qT'} (hc : CStep checker (.run q checkProg) o c')
    (hT : clockTh.run qT (hostView [wev o]) = some qT') : CheckStep o c' qT' := by
  obtain ⟨rfl, rfl⟩ := CStep.call_inv (m := nowOp) (k := checkK1) hc
  exact ⟨(), rfl, Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))⟩

theorem check_first {q o c' qT qT'} (hc : CStep checker (.wait q nowOp checkK1) o c')
    (hT : clockTh.run qT (hostView [wev o]) = some qT') : CheckStep o c' qT' := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  obtain ⟨x, rfl, rfl, -⟩ := nowStep_inv (clock_run_now hT)
  exact ⟨(), rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨q, x, rfl, rfl⟩)))⟩

theorem check_mid {q x o c' qT'} (hc : CStep checker (.run q (checkK1 (some [.u64 x]))) o c')
    (hT : clockTh.run (some x) (hostView [wev o]) = some qT') : CheckStep o c' qT' := by
  obtain ⟨rfl, rfl⟩ := CStep.call_inv (m := nowOp) (k := checkK2 (some [.u64 x])) hc
  have hq : qT' = some x := run_hostView_of_not_imp rfl hT
  exact ⟨(), rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, x, hq, rfl⟩))))⟩

theorem check_second {q x o c' qT'}
    (hc : CStep checker (.wait q nowOp (checkK2 (some [.u64 x]))) o c')
    (hT : clockTh.run (some x) (hostView [wev o]) = some qT') : CheckStep o c' qT' := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  obtain ⟨y, rfl, -, hxy⟩ := nowStep_inv (clock_run_now hT)
  have hle : decide (x ≤ y) = true := hxy
  have hc' : checkK2 (some [.u64 x]) (some [.u64 y]) = .pure (some [.bool true]) := by
    show Prog.pure _ = _
    rw [show le2 (some [.u64 x]) (some [.u64 y]) = decide (x ≤ y) from rfl, hle]
  exact ⟨(), rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨q, hc' ▸ rfl⟩))))⟩

theorem check_ret {q o c' qT qT'} (hc : CStep checker (.run q (.pure (some [.bool true]))) o c')
    (hT : clockTh.run qT (hostView [wev o]) = some qT') : CheckStep o c' qT' := by
  obtain ⟨rfl, rfl⟩ := hc.pure_inv
  exact ⟨(), rfl, Or.inl rfl⟩

/-- **The invariant of the clock checker.** -/
theorem checker_inv : Inv checker clockTh (onExp retTrue) CheckInv where
  init := Or.inl rfl
  step := fun hc hJ hT => by
    rcases hJ with rfl | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, x, rfl, rfl⟩ | ⟨q, x, rfl, rfl⟩ | ⟨q, rfl⟩
    · exact check_idle hc hT
    · exact check_start hc hT
    · exact check_first hc hT
    · exact check_mid hc hT
    · exact check_second hc hT
    · exact check_ret hc hT

/-- **The clock checker under the monotonic clock theory**: it always returns `true`. -/
theorem checker_sat : (agP clockTh (onExp retTrue)).holds (ofBody checker) :=
  ag_of_inv checker_inv

/-- **The clock checker over every host satisfying the clock theory.** -/
theorem checker_every_host (Y : Sig.{0}) (η : Host Y clocksWorld.imports)
    (hη : (hostSat clockTh.Accepts).holds η) :
    ∀ p ∈ link η (ofBody checker), retTrue.Accepts (xtrace p) :=
  link_satP checker_sat hη

/-- The clock checker over the concrete tick clock. -/
theorem checker_tick (Y : Sig.{0}) :
    ∀ p ∈ link (concrete (Y := Y) clockImpl) (ofBody checker), retTrue.Accepts (xtrace p) :=
  checker_every_host Y _ clockImpl_sat

/-- The export call of the checker. -/
def checkQ : (nsig clocksWorld.exports).Op := (⟨clockCheck, rfl⟩, [])

/-- A play where the clock goes back. -/
def backwards : List (Move (nsig clocksWorld.imports) (nsig clocksWorld.exports)) :=
  [.inr (.ask checkQ), .inl (.ask nowOp), .inl (.ans nowOp (some [.u64 5])), .inl (.ask nowOp),
    .inl (.ans nowOp (some [.u64 3])), .inr (.ans checkQ (some [.bool false]))]

theorem backwards_mem : backwards ∈ ofBody checker :=
  ⟨_, (((((Reach.nil.snoc (.ask checkQ)).snoc (.call checkQ nowOp checkK1)).snoc
    (.reply checkQ nowOp checkK1 (some [.u64 5]))).snoc
    (.call checkQ nowOp (checkK2 (some [.u64 5])))).snoc
    (.reply checkQ nowOp (checkK2 (some [.u64 5])) (some [.u64 3]))).snoc
    (.ret checkQ (some [.bool false]))⟩

/-- **The theory is needed** (a refutation): with no assumption on the clock, the checker can
return `false`. -/
theorem checker_needs_theory : ¬ (agP topP (onExp retTrue)).holds (ofBody checker) := by
  intro h
  have hA : topP.Accepts (hostView (wtrace backwards)) :=
    (Protocol.acceptsB_iff _ _).1 (by decide)
  have hG : ¬ (onExp retTrue).Accepts (wtrace backwards) := fun hG =>
    absurd ((Protocol.acceptsB_iff _ _).2 hG) (by decide)
  exact hG (h backwards backwards_mem hA)

/-- The world of the checker with all the imports of `cliWorld`. -/
def clocksInCli : World := ⟨cliWorld.imports, clocksWorld.exports⟩

/-- The checker's world fits it. -/
def toClocks : clocksInCli ⟶ clocksWorld := ⟨⟨fun _ hx => Or.inl (Or.inl hx), subset_rfl⟩⟩

/-- **The checker as a component of a larger world** satisfies the same sentence. -/
theorem checker_in_cli :
    (agP clockTh (onExp retTrue)).holds (Game.reduct (World.toGame.map toClocks) (ofBody checker)) :=
  World.ag_reduct toClocks checker_sat

/-! ## Handles -/

/-- **`hello` uses stream handles only while live**, for every host. -/
theorem hello_sat : (agP topP stdoutHandles).holds (ofBody hello) := ag_of_inv hello_inv

/-- **`writeFile` uses descriptors only while live**, for every host. -/
theorem writeFile_sat : (agP topP fsHandles).holds (ofBody writeFile) := ag_of_inv writeFile_inv

/-- `topP` accepts everything. -/
theorem topP_accepts (t : List WEv) : topP.Accepts t :=
  (pointwise_accepts_iff _ t).2 fun _ _ => rfl

/-- `hello` in every interaction with every host. -/
theorem hello_every_host (Y : Sig.{0}) (η : Host Y stdoutWorld.imports) {s t p}
    (_ : s ∈ η) (ht : t ∈ ofBody hello) (_ : Zip (γ := Ev (nsig stdoutWorld.exports)) s t p) :
    stdoutHandles.Accepts (wtrace t) :=
  hello_sat t ht (topP_accepts _)

/-- `writeFile` in every interaction with every host. -/
theorem writeFile_every_host (Y : Sig.{0}) (η : Host Y fsWorld.imports) {s t p}
    (_ : s ∈ η) (ht : t ∈ ofBody writeFile) (_ : Zip (γ := Ev (nsig fsWorld.exports)) s t p) :
    fsHandles.Accepts (wtrace t) :=
  writeFile_sat t ht (topP_accepts _)

end Silmaril.Wasi.Examples
