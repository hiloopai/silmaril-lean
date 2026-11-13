module

public import Silmaril.Compiler.Mir.Pass.Defs
public import Silmaril.Compiler.Mir.UnreachableLimit.Defs
/-! # Placement-aware Mir pass contract: isolated review draft

Nothing imports this module; neither the frozen contracts nor the registry change.
`mirPassDraft` weakens `Contract.mirPass` by testing only output placements induced
by some valid input placement, with equal initial memory. The observation remains
the complete returned/trapped memory and values, at the identity convention.
`Induced` preserves addresses of output-reachable symbols and the heap boundary;
it allows additional input placements for symbols the output no longer reaches.
It is an eligibility condition on the output placement, not a requirement that
the existential refinement witness use a particular allocation.

The old contract implies the draft, so every currently proved pass satisfies it,
including passes not imported here. `Deletion.correct` admits the deletion from
`UnreachableLimit`. This is not sufficient for the frozen link contract: its
existential placement need not be eligible. `link_comp` states the exact extra
link obligation; `Counterexample.not_compositional` disproves composition from
the two stage contracts alone, using an unreachable byte initialized to one.
The counterexample has ample memory, entries, terminating non-stuck behaviour,
and a nonempty domain of compatible placements. No compiler is installed here.
-/

@[expose] public section

namespace Silmaril.Compile.Mir.MirPassDraft

open Silmaril.Machine Silmaril.Compile.Contract
open Silmaril.Compile.Contract.MirSem

/-- Output-visible addresses, heap boundary, and every initial byte agree.
Unreachable input objects may still occupy storage, but their bytes must be
retained in the output image under the identity memory observation. -/
def Induced (us vs : Array Mir.Unit) (memSize : Nat) (P P' : Placement) : Prop :=
  P.heap = P'.heap ∧
  (∀ s, Reach vs s → symValue us P s = symValue vs P' s) ∧
  initMem us P memSize = initMem vs P' memSize

/-- An output placement has at least one valid input extension with the same
observable initial memory. This domain is deliberately narrower than `Valid`. -/
def Eligible (us vs : Array Mir.Unit) (memSize : Nat) (P' : Placement) : Prop :=
  ∃ P, P.Valid us memSize ∧ Induced us vs memSize P P'

/-- **Draft only.** The frozen backward refinement and entry clauses, restricted
to eligible output placements. The data-memory bound is unchanged. -/
def mirPassDraft (f : Array Mir.Unit → Array Mir.Unit) : Prop :=
  ∀ us,
    (∀ base, need (f us) base ≤ need us base) ∧
    ∀ memSize, memSize ≤ 2 ^ 64 → ∀ P', P'.Valid (f us) memSize →
      Eligible us (f us) memSize P' →
      ∃ P, P.Valid us memSize ∧
        ∀ s, start us P memSize = some s →
          (∃ t, start (f us) P' memSize = some t) ∧
          ∀ t, start (f us) P' memSize = some t → ∀ b, Behaves (f us) P' t b →
            ∃ b', Behaves us P s b' ∧ (b' = .stuck ∨ b' = b)

/-- Applies to ConstProp, DeadCode, loadForward and deadCall through their
existing `Contract.mirPass` proofs; no new proof of their implementation is needed. -/
theorem of_mirPass {f : Array Mir.Unit → Array Mir.Unit} (hf : Contract.mirPass f) :
    mirPassDraft f := by
  intro us
  exact ⟨(hf us).1, fun m hm P' hv _ => (hf us).2 m hm P' hv⟩

/-- In particular every registered/bundled old-style pass satisfies the draft. -/
theorem currentPass (p : Mir.Pass) : mirPassDraft p.run := of_mirPass p.correct

/-- The existing registered pass-list composition also satisfies the draft. -/
theorem currentPasses (ps : List Mir.Pass) : mirPassDraft (Mir.Pass.runAll ps) :=
  of_mirPass (Mir.Pass.runAll_correct ps)

/-- **Additional open integration obligation.** A successful downstream link
must supply an eligible placement *and* its semantic simulation at that same
placement. Separate existential witnesses are insufficient. This is a named
proposition, not an assumed axiom or a claim about the current linker. -/
def PlacementAwareLink (f : Array Mir.Unit → Array Mir.Unit)
    (L : Array Mir.Unit → Except String Mir.Linked) : Prop :=
  ∀ us l, L (f us) = .ok l → ∀ memSize,
    need us Target.layout.dataBase ≤ memSize → memSize ≤ 2 ^ 64 →
    ∃ P', P'.Valid (f us) memSize ∧ Eligible us (f us) memSize P' ∧
      ∀ t, start (f us) P' memSize = some t → ∀ b,
        Behaves (f us) P' t b → b ≠ .stuck →
        ∃ u, l.prog.start 0 [] (linkedMem l memSize) = some u ∧ Lir.Behaves l.prog u b

/-- With a compatible link witness the existing `Contract.link` conclusion is
recovered verbatim, so its downstream spill/codegen/object clients need no change.
This theorem does not derive `PlacementAwareLink` from `Contract.link`. -/
theorem link_comp {f : Array Mir.Unit → Array Mir.Unit}
    {L : Array Mir.Unit → Except String Mir.Linked}
    (hf : mirPassDraft f) (hL : PlacementAwareLink f L) :
    Contract.link (fun us => L (f us)) := by
  intro us l hl memSize hn hm
  obtain ⟨P', hv', he, hlink⟩ := hL us l hl memSize hn hm
  obtain ⟨P, hv, hsim⟩ := (hf us).2 memSize hm P' hv' he
  refine ⟨P, hv, fun s hs b hb hns => ?_⟩
  obtain ⟨⟨t, ht⟩, hback⟩ := hsim s hs
  obtain ⟨bo, hbo⟩ := Behaves.exists (f us) P' t
  obtain ⟨b', hb', hh⟩ := hback t ht bo hbo
  obtain rfl := Behaves.unique hb hb'
  rcases hh with hh | rfl
  · exact absurd hh hns
  · exact hlink t ht b hbo hns

namespace Deletion

open UnreachableLimit (inputFunc outputFunc)

/-- The same three-block example, parameterized by the retained data object. -/
def units (fn : Func) (d : Data) : Array Mir.Unit := #[{ funcs := #[fn], data := #[d] }]

/-- Mathematical test transformation; classical equality is used only to select
this single example. This function is not an executable compiler stage. -/
noncomputable def erase (d : Data) (us : Array Mir.Unit) : Array Mir.Unit := by
  classical
  exact if us = units inputFunc d then units outputFunc d else us

def entryState (fn : Func) (m : Lir.Memory) : State :=
  ⟨fn, 0, 0, Lir.Frame.empty, [], m⟩

theorem start_eq (fn : Func) (d : Data) (P : Placement) (m : Nat)
    (hp : fn.params = []) (hw : fn.weak = false) :
    start (units fn d) P m = some (entryState fn (initMem (units fn d) P m)) := by
  simp [start, funcDefs, units, enter, hp, hw, entryState, Lir.Frame.writeAll]

/-- Both entries jump directly to the return, independently of all symbols. -/
theorem returns (fn : Func) (hfn : fn = inputFunc ∨ fn = outputFunc)
    (us : Array Mir.Unit) (P : Placement) (m : Lir.Memory) :
    Behaves us P (entryState fn m) (.returned [] m) := by
  refine ⟨{ entryState fn m with label := 2 }, Relation.ReflTransGen.single ?_, ?_⟩
  all_goals rcases hfn with rfl | rfl
  all_goals simp [Step, step, entryState, inputFunc, outputFunc, Lir.Frame.readAll]

/-- The counterexample rewrite satisfies the draft whenever its output placement
has a memory-preserving input extension. No reachability premise is assumed. -/
theorem correct (d : Data) : mirPassDraft (erase d) := by
  classical
  intro us
  by_cases hu : us = units inputFunc d
  · subst us
    have he : erase d (units inputFunc d) = units outputFunc d := by simp [erase]
    rw [he]
    refine ⟨fun _ => le_rfl, fun m _ P' _ hel => ?_⟩
    obtain ⟨P, hv, _, _, hm⟩ := hel
    refine ⟨P, hv, fun s hs => ?_⟩
    rw [start_eq _ _ _ _ rfl rfl] at hs
    cases hs
    refine ⟨⟨_, start_eq _ _ _ _ rfl rfl⟩, fun t ht b hb => ?_⟩
    rw [start_eq _ _ _ _ rfl rfl] at ht
    cases ht
    have hr := returns outputFunc (.inr rfl) (units outputFunc d) P'
      (initMem (units outputFunc d) P' m)
    obtain rfl := Behaves.unique hb hr
    refine ⟨_, returns inputFunc (.inl rfl) (units inputFunc d) P
      (initMem (units inputFunc d) P m), .inr ?_⟩
    rw [hm]
  · have he : erase d us = us := by simp [erase, hu]
    simpa only [he, id_eq] using of_mirPass Mir.Pass.mirPass_id us

/-- This is exactly the rewrite disproved under the frozen contract. -/
theorem original_rewrite : erase UnreachableLimit.object UnreachableLimit.input =
    UnreachableLimit.output := by
  classical
  simp [erase, units, UnreachableLimit.input, UnreachableLimit.output]

theorem original_not_old : ¬ Contract.mirPass (erase UnreachableLimit.object) :=
  UnreachableLimit.deletion_not_mirPass _ original_rewrite

end Deletion

namespace Counterexample

open Deletion
open UnreachableLimit (inputFunc outputFunc)

def datum : Data := { UnreachableLimit.object with init := ByteArray.mk #[1] }
def input := units inputFunc datum
def output := units outputFunc datum

def fullPlacement : Placement :=
  ⟨fun s => if s = "object" then some 1 else none,
   fun s => if s = "main" then some 1 else none, 2⟩

theorem full_valid (fn : Func) (hfn : fn = inputFunc ∨ fn = outputFunc)
    (m : Nat) (hm : 2 ≤ m) : fullPlacement.Valid (units fn datum) m := by
  rcases hfn with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_, ?_, hm, ?_, ?_⟩
    · intro s _ hd
      by_cases hs : s = "object"
      · simp [fullPlacement, hs]
      · simp [dataOf, dataDefs, units, datum, UnreachableLimit.object] at hd
        exact (hs hd.symm).elim
    · intro s _ _ hf
      by_cases hs : s = "main"
      · simp [fullPlacement, hs]
      · simp [funcOf, funcDefs, units, inputFunc, outputFunc] at hf
        exact (hs hf.symm).elim
    · simp [dataDefs, units, datum, UnreachableLimit.object, fullPlacement]
    · simp [dataDefs, units, datum, UnreachableLimit.object]
    · intro s a hs
      by_cases hn : s = "main"
      · simp [fullPlacement, hn] at hs
        omega
      · simp [fullPlacement, hn] at hs
    · intro s s' a hs hs'
      simp only [fullPlacement] at hs hs'
      split at hs <;> split at hs' <;> simp_all

private theorem output_reach {s : String} (h : Reach output s) : s = "main" := by
  induction h with
  | entry hf =>
    simp [funcDefs, output, units, outputFunc, inputFunc] at hf
    subst hf
    rfl
  | func hn hf hb hi hs ih =>
    subst ih
    simp [funcOf, funcDefs, output, units, outputFunc, inputFunc] at hf
    subst hf
    simp at hb
    rcases hb with rfl | rfl | rfl <;> simp at hi
  | data hn hd hr ih =>
    subst ih
    simp [dataOf, dataDefs, output, units, datum, UnreachableLimit.object] at hd

/-- The link contract permits omitting the initialized but unreferenced object. -/
theorem empty_valid (m : Nat) : UnreachableLimit.emptyPlacement.Valid output m := by
  refine ⟨?_, ?_, ?_, ?_, Nat.zero_le _, ?_, ?_⟩
  · intro s hs
    obtain rfl := output_reach hs
    simp [dataOf, dataDefs, output, units, datum, UnreachableLimit.object]
  · intro s hs
    obtain rfl := output_reach hs
    simp [funcOf, funcDefs, output, units, outputFunc, inputFunc,
      UnreachableLimit.emptyPlacement]
  · simp [UnreachableLimit.emptyPlacement]
  · simp [UnreachableLimit.emptyPlacement]
  · intro s a hs
    by_cases hn : s = "main"
    · simp [UnreachableLimit.emptyPlacement, hn] at hs
      omega
    · simp [UnreachableLimit.emptyPlacement, hn] at hs
  · intro s s' a hs hs'
    simp only [UnreachableLimit.emptyPlacement] at hs hs'
    split at hs <;> split at hs' <;> simp_all

/-- Compatibility is satisfiable: retain the old storage and heap, even though
the output no longer requires them. This rules out an empty eligibility domain. -/
theorem eligible_exists :
    fullPlacement.Valid output 16384 ∧ Eligible input output 16384 fullPlacement := by
  refine ⟨full_valid _ (.inr rfl) _ (by decide),
    fullPlacement, full_valid _ (.inl rfl) _ (by decide), rfl, ?_, ?_⟩
  · intro s hs
    obtain rfl := output_reach hs
    simp [symValue, heapSymbol, input, output, units, dataOf, dataDefs, funcOf,
      funcDefs, datum, UnreachableLimit.object, inputFunc, outputFunc]
  · simp [initMem, dataDefs, input, output, units, datum, UnreachableLimit.object,
      objectByte]
    funext a
    split_ifs <;> simp_all

def zeroMem (m : Nat) : Lir.Memory := ⟨m, fun _ => 0⟩

theorem empty_mem (m : Nat) :
    initMem output UnreachableLimit.emptyPlacement m = zeroMem m := by
  rfl

/-- Every valid input placement exposes a byte equal to one in final memory. -/
theorem input_mem_ne (m : Nat) (P : Placement) (hv : P.Valid input m) :
    initMem input P m ≠ zeroMem m := by
  have hentry : Reach input "main" := .entry (f := inputFunc) (by
    simp [funcDefs, input, units, inputFunc])
  have href : Reach input "object" := .func (f := inputFunc) hentry
    (by simp [funcOf, funcDefs, input, units, inputFunc])
    (b := ⟨#[.addr 0 "object" 0], .trap⟩) (i := .addr 0 "object" 0)
    (by simp [inputFunc]) (by simp) (by simp [instrRefs])
  have hp := hv.1 "object" href (by
    simp [dataOf, dataDefs, input, units, datum, UnreachableLimit.object])
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hp
  intro he
  have hb := congrArg (fun mem : Lir.Memory => mem.bytes a) he
  simp [initMem, dataDefs, input, units, datum, UnreachableLimit.object, ha,
    objectByte, zeroMem] at hb
  have hz := hb (by decide)
  change (1 : BitVec 8) = 0 at hz
  exact (by decide : (1 : BitVec 8) ≠ 0) hz

/-- A link result that immediately returns, with an empty memory image. -/
def linked : Mir.Linked :=
  { prog := ⟨[⟨[], 0, [⟨[], .ret []⟩]⟩]⟩,
    funcs := {}, data := {}, dataBase := 0, dataEnd := 0, image := ByteArray.empty }

def lirState (m : Lir.Memory) : Lir.State Nat :=
  ⟨⟨0, 0, 0⟩, Lir.Frame.empty, [], m⟩

theorem lir_start (m : Lir.Memory) : linked.prog.start 0 [] m = some (lirState m) := rfl

theorem lir_returns (m : Lir.Memory) :
    Lir.Behaves linked.prog (lirState m) (.returned [] m) := by
  exact ⟨_, .refl, rfl⟩

theorem linked_mem (m : Nat) : linkedMem linked m = zeroMem m := by
  simp [linkedMem, linked, zeroMem]

/-- Mathematical downstream stage accepting only this output example. Its
contract is proved below; this is a countermodel, not a compiler implementation. -/
noncomputable def linker (us : Array Mir.Unit) : Except String Mir.Linked := by
  classical
  exact if us = output then .ok linked else .error "outside counterexample"

/-- The existing link contract is satisfied at the zero-image placement. -/
theorem linker_correct : Contract.link linker := by
  classical
  intro us l hl m _ _
  by_cases hu : us = output
  · subst us
    simp only [linker, ite_true, Except.ok.injEq] at hl
    subst l
    refine ⟨UnreachableLimit.emptyPlacement, empty_valid m, fun s hs b hb _ => ?_⟩
    rw [show output = units outputFunc datum from rfl,
      start_eq outputFunc datum _ _ rfl rfl] at hs
    cases hs
    have hr := returns outputFunc (.inr rfl) output UnreachableLimit.emptyPlacement
      (initMem output UnreachableLimit.emptyPlacement m)
    obtain rfl := Behaves.unique hb hr
    refine ⟨_, lir_start _, ?_⟩
    rw [linked_mem, empty_mem]
    exact lir_returns _
  · simp [linker, hu] at hl

/-- With ample memory the composite loses an initialized byte that the identity
convention observes. Entry and every behaviour used here are non-stuck. -/
theorem composite_not_link : ¬ Contract.link (fun us => linker (erase datum us)) := by
  classical
  intro hc
  have he : linker (erase datum input) = .ok linked := by
    simp [erase, input, linker, output]
  obtain ⟨P, hv, hsim⟩ := hc input linked he 16384 (by decide) (by decide)
  have hs := start_eq inputFunc datum P 16384 rfl rfl
  have hb := returns inputFunc (.inl rfl) input P (initMem input P 16384)
  obtain ⟨t, ht, hbt⟩ := hsim _ hs _ hb (by intro h; cases h)
  rw [lir_start] at ht
  cases ht
  have hu := Lir.Behaves.unique hbt (lir_returns (linkedMem linked 16384))
  have hm : initMem input P 16384 = zeroMem 16384 := by
    simpa only [Lir.Behavior.returned.injEq, true_and, linked_mem] using hu
  exact input_mem_ne _ P hv hm

/-- A revised pass contract alone cannot retain the old composition theorem.
Consequently the unchanged codegen/object contracts cannot repair this gap. -/
theorem not_compositional :
    ¬ (∀ (f : Array Mir.Unit → Array Mir.Unit)
        (L : Array Mir.Unit → Except String Mir.Linked),
      mirPassDraft f → Contract.link L → Contract.link (fun us => L (f us))) := by
  intro h
  exact composite_not_link (h (erase datum) linker (Deletion.correct datum) linker_correct)

end Counterexample

-- Keep the axiom boundary visible in the targeted review build.
#print axioms of_mirPass
#print axioms link_comp
#print axioms Deletion.correct
#print axioms Deletion.original_not_old
#print axioms Counterexample.eligible_exists
#print axioms Counterexample.not_compositional

end Silmaril.Compile.Mir.MirPassDraft
