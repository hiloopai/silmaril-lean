module

public import Silmaril.Compiler.C.Sem.C2Prefix.Defs
public import Silmaril.Compiler.C.Sem.C2Mono.Defs
/-!
# Contracts for source fragments ending in a function return

These contracts start at an explicit internal configuration. They require a
finite successful execution on every permitted entry, retain the complete
returned environment, and hide interpreter fuel from clients. An internal-entry
contract does not imply reachability from the public function entry.
-/

@[expose] public section

namespace Silmaril.Compile.C.Sem.C2

/-- Internal control and ownership preconditions with a returned observation. -/
structure FragmentContract (ι : Type) where
  pre : ι → Configuration → Prop
  post : ι → Configuration → Option Val → C1.Env → Prop

namespace FragmentContract

variable {ι : Type}

def Implements (spec : FragmentContract ι) (P : Prog) (fd : C1.FunDef) : Prop :=
  ∀ i before, spec.pre i before →
    ∃ fuel value after,
      loop P fuel fd before.focus before.kont before.env = .ok (value, after) ∧
        spec.post i before value after

/-- A successful finite source run is unique across all interpreter budgets. -/
theorem success_unique (P : Prog) (fd : C1.FunDef) (before : Configuration)
    (fuel₁ fuel₂ : Nat) (value₁ value₂ : Option Val) (after₁ after₂ : C1.Env)
    (first : loop P fuel₁ fd before.focus before.kont before.env = .ok (value₁, after₁))
    (second : loop P fuel₂ fd before.focus before.kont before.env = .ok (value₂, after₂)) :
    value₁ = value₂ ∧ after₁ = after₂ := by
  have left : loop P (fuel₁ + fuel₂) fd before.focus before.kont before.env =
      .ok (value₁, after₁) := by
    simpa only [first] using
      loop_mono P fuel₁ fuel₂ fd before.focus before.kont before.env (by simp [first])
  have right : loop P (fuel₁ + fuel₂) fd before.focus before.kont before.env =
      .ok (value₂, after₂) := by
    simpa only [Nat.add_comm fuel₂ fuel₁, second] using
      loop_mono P fuel₂ fuel₁ fd before.focus before.kont before.env (by simp [second])
  exact Prod.mk.inj (Except.ok.inj (left.symm.trans right))

/-- Clients can choose any budget above the implementation's finite witness. -/
theorem Implements.run {spec : FragmentContract ι} {P : Prog} {fd : C1.FunDef}
    (implementation : spec.Implements P fd) (i : ι) (before : Configuration)
    (entry : spec.pre i before) :
    ∃ threshold value after, spec.post i before value after ∧
      ∀ fuel, threshold ≤ fuel →
        loop P fuel fd before.focus before.kont before.env = .ok (value, after) := by
  obtain ⟨threshold, value, after, run, post⟩ := implementation i before entry
  refine ⟨threshold, value, after, post, ?_⟩
  intro fuel bound
  have stable := loop_mono P threshold (fuel - threshold) fd before.focus before.kont before.env
    (by simp [run])
  simpa only [Nat.add_sub_of_le bound, run] using stable

/-- The postcondition applies to every successful run, not only its witness. -/
theorem Implements.post_of_loop {spec : FragmentContract ι} {P : Prog} {fd : C1.FunDef}
    (implementation : spec.Implements P fd) (i : ι) (before : Configuration)
    (entry : spec.pre i before) (fuel : Nat) (value : Option Val) (after : C1.Env)
    (run : loop P fuel fd before.focus before.kont before.env = .ok (value, after)) :
    spec.post i before value after := by
  obtain ⟨witness, expected, final, execution, post⟩ := implementation i before entry
  obtain ⟨rfl, rfl⟩ := success_unique P fd before fuel witness value expected after final run execution
  exact post

/-- Strengthening or forgetting logical observations changes no source code. -/
theorem Implements.consequence {κ : Type} {strong : FragmentContract ι}
    {weak : FragmentContract κ} {P : Prog} {fd : C1.FunDef}
    (implementation : strong.Implements P fd) (index : κ → ι)
    (pre : ∀ i before, weak.pre i before → strong.pre (index i) before)
    (post : ∀ i before value after, weak.pre i before →
      strong.post (index i) before value after → weak.post i before value after) :
    weak.Implements P fd := by
  intro i before entry
  obtain ⟨fuel, value, after, run, result⟩ := implementation (index i) before (pre i before entry)
  exact ⟨fuel, value, after, run, post i before value after entry result⟩

/-- Compose an internal source prefix with an independently verified returning
fragment. Prefix and suffix may have different minimum interpreter budgets,
including a separate threshold for nested callees. The public precondition is
still responsible for establishing the actual entry configuration. -/
theorem Implements.prepend {κ : Type} {suffix : FragmentContract ι}
    {whole : FragmentContract κ} {P : Prog} {fd : C1.FunDef}
    (implementation : suffix.Implements P fd) (index : κ → Configuration → ι)
    (path : ∀ i before, whole.pre i before →
      ∃ cost reserve middle,
        suffix.pre (index i before) middle ∧
        (∀ fuel, reserve ≤ fuel → Prefix P fd (fuel + cost) before fuel middle) ∧
        (∀ value after, suffix.post (index i before) middle value after →
          whole.post i before value after)) :
    whole.Implements P fd := by
  intro i before entry
  obtain ⟨cost, reserve, middle, nextEntry, pathProof, post⟩ := path i before entry
  obtain ⟨threshold, value, after, result, runs⟩ :=
    implementation.run (index i before) middle nextEntry
  let fuel := max reserve threshold
  exact ⟨fuel + cost, value, after,
    (pathProof fuel (Nat.le_max_left _ _)).append_success value after
      (runs fuel (Nat.le_max_right _ _)), post value after result⟩

end FragmentContract

end Silmaril.Compile.C.Sem.C2
