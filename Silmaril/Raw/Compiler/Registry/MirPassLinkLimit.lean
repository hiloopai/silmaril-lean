module

public import Silmaril.Compiler.Mir.MirPassDraft.Defs
public import Silmaril.Compiler.Mir.WhileId.Defs
public import Silmaril.Compiler.Registry.Defs
/-! # The actual checked linker does not supply placement-aware composition

The linker roots the first data object, so the earlier one-object mathematical
countermodel does not demonstrate a failure of the implementation. Here a rooted
zero-size sentinel precedes the initialized object. Removing the dead `addr` makes the
second object unreferenced; the real checked linker discards it. Its zero image
cannot simulate the input's nonzero initial memory under the identity observation.
This is a limitation of the proposed contract revision, not a new compiler pass.
-/

set_option maxRecDepth 4096

@[expose] public section

attribute [local cbv_eval] Silmaril.Compile.Mir.WhileId.repeatM_eq
  Std.Legacy.Range.forIn'_eq_forIn'_range'
  Std.HashMap.size_emptyWithCapacity Std.HashMap.size_insert

namespace Silmaril.Compile.Mir.MirPassLinkLimit

open Silmaril.Machine Silmaril.Compile.Contract
open Silmaril.Compile.Contract.MirSem
open MirPassDraft
open UnreachableLimit (inputFunc outputFunc)

/-- The zero-size first object is always a linker root. -/
def root : Data := { name := "root", size := 0, align := 1 }
def datum : Data := MirPassDraft.Counterexample.datum

def units (fn : Func) : Array Mir.Unit :=
  #[{ funcs := #[fn], data := #[root, datum] }]
def input := units inputFunc
def output := units outputFunc

theorem dataDefs_eq (fn : Func) : dataDefs (units fn) = [root, datum] := by
  simp [dataDefs, units, root, datum, MirPassDraft.Counterexample.datum,
    UnreachableLimit.object]

theorem symValue_eq (P : Placement) (s : String) :
    symValue input P s = symValue output P s := by
  simp only [symValue, dataOf, input, output, dataDefs_eq]
  simp [funcOf, funcDefs, units, root, datum, MirPassDraft.Counterexample.datum,
    UnreachableLimit.object, inputFunc, outputFunc]

theorem initMem_eq (P : Placement) (m : Nat) :
    initMem input P m = initMem output P m := by
  have hs := funext (symValue_eq P)
  change symValue (units inputFunc) P = symValue (units outputFunc) P at hs
  simp only [initMem, input, output, dataDefs_eq]
  congr 1
  funext a
  split
  · simp only [objectByte, ← hs]
  · rfl

/-- Mathematical test rewrite, used only to test the proposed contract. -/
noncomputable def erase (us : Array Mir.Unit) : Array Mir.Unit := by
  classical
  exact if us = input then output else us

theorem start_eq (fn : Func) (P : Placement) (m : Nat)
    (hp : fn.params = []) (hw : fn.weak = false) :
    start (units fn) P m =
      some (Deletion.entryState fn (initMem (units fn) P m)) := by
  simp [start, funcDefs, units, enter, hp, hw, Deletion.entryState, Lir.Frame.writeAll]

/-- The rewrite meets the draft contract for every input and memory size. -/
theorem erase_correct : mirPassDraft erase := by
  classical
  intro us
  by_cases hu : us = input
  · subst us
    have he : erase input = output := by simp [erase]
    rw [he]
    refine ⟨fun _ => le_rfl, fun m _ P' _ hel => ?_⟩
    obtain ⟨P, hv, _, _, hm⟩ := hel
    refine ⟨P, hv, fun s hs => ?_⟩
    change start (units inputFunc) P m = some s at hs
    rw [start_eq inputFunc _ _ rfl rfl] at hs
    cases hs
    refine ⟨⟨_, start_eq outputFunc _ _ rfl rfl⟩, fun t ht b hb => ?_⟩
    change start (units outputFunc) P' m = some t at ht
    rw [start_eq outputFunc _ _ rfl rfl] at ht
    cases ht
    have hr := Deletion.returns outputFunc (.inr rfl) output P'
      (initMem output P' m)
    obtain rfl := Behaves.unique hb hr
    refine ⟨_, Deletion.returns inputFunc (.inl rfl) input P
      (initMem input P m), .inr ?_⟩
    rw [hm]
  · have he : erase us = us := by simp [erase, hu]
    simpa only [he, id_eq] using of_mirPass Mir.Pass.mirPass_id us

/-- The concrete link of the output, with only the zero-size sentinel retained. -/
def linked : Mir.Linked :=
  { prog := ⟨[⟨[], 0, [⟨[], .jump 2⟩, ⟨[], .trap⟩, ⟨[], .ret []⟩]⟩]⟩,
    funcs := ({} : Std.HashMap String Nat).insert "main" 0,
    data := (({} : Std.HashMap String Nat).insert "root" 4096).insert
      Mir.dataEndSymbol 4096,
    dataBase := 4096, dataEnd := 4096,
    image := ByteArray.empty }



private theorem singleton_toList (k : String) (v c : Nat) :
    ((Std.HashMap.emptyWithCapacity c : Std.HashMap String Nat).insert k v).toList =
      [(k, v)] := by
  apply List.Perm.eq_singleton
  simpa using (Std.HashMap.toList_insert_perm
    (m := (Std.HashMap.emptyWithCapacity c : Std.HashMap String Nat)) (k := k) (v := v))

private theorem insert_all (m : Std.HashMap String Nat) (k : String) (v : Nat)
    (p : String × Nat → Bool) :
    (m.insert k v).toList.all p = (p (k, v) &&
      (m.toList.filter (¬k == ·.1)).all p) := by
  exact (Std.HashMap.toList_insert_perm (m := m) (k := k) (v := v)).all_eq (f := p)

attribute [local cbv_eval] singleton_toList
  Std.HashMap.toList_emptyWithCapacity Nat.all_zero Nat.fold_zero

set_option maxHeartbeats 0 in
/-- Evaluation of the existing unmodified linker, with its real layout. -/
theorem raw_link : Mir.link Target.layout output = .ok linked := by
  cbv

set_option maxHeartbeats 0 in
/-- The existing semantic checker accepts the concrete link result. -/
theorem check_linked :
    LinkCheck.check Target.layout Target.layout.dataBase output linked = true := by
  simp only [LinkCheck.check, linked, insert_all]
  cbv
  exact Nat.all_zero

/-- Both the actual linker and its semantic checker accept the output. -/
theorem checked_link : Registry.Stage.link output = .ok linked := by
  simp only [Registry.Stage.link, raw_link, check_linked, ↓reduceIte]

def zeroMem (m : Nat) : Lir.Memory := ⟨m, fun _ => 0⟩

theorem linked_mem (m : Nat) : linkedMem linked m = zeroMem m := by
  apply congrArg (Lir.Memory.mk m)
  funext a
  have h : ¬(linked.dataBase ≤ a ∧ a < linked.dataBase + linked.image.size) := by
    change ¬(4096 ≤ a ∧ a < 4096 + 0)
    omega
  exact dite_eq_right h

/-- The linked entry jumps over the dead block and returns its initial memory. -/
def lirState (m : Lir.Memory) : Lir.State Nat :=
  ⟨⟨0, 0, 0⟩, Lir.Frame.empty, [], m⟩

theorem lir_start (m : Lir.Memory) : linked.prog.start 0 [] m = some (lirState m) := rfl

theorem lir_returns (m : Lir.Memory) :
    Lir.Behaves linked.prog (lirState m) (.returned [] m) := by
  refine ⟨{ lirState m with point := ⟨0, 2, 0⟩ }, Relation.ReflTransGen.single ?_, ?_⟩
  all_goals rfl

/-- Every valid input placement must retain the nonzero byte, independently of
where the initialized object is placed. -/
theorem input_mem_ne (m : Nat) (P : Placement) (hv : P.Valid input m) :
    initMem input P m ≠ zeroMem m := by
  have hentry : Reach input "main" := .entry (f := inputFunc) (by
    simp [funcDefs, input, units, inputFunc])
  have href : Reach input "object" := .func (f := inputFunc) hentry
    (by simp [funcOf, funcDefs, input, units, inputFunc])
    (b := ⟨#[.addr 0 "object" 0], .trap⟩) (i := .addr 0 "object" 0)
    (by simp [inputFunc]) (by simp) (by simp [instrRefs])
  have hp := hv.1 "object" href (by
    simp [dataOf, dataDefs, input, units, root, datum,
      MirPassDraft.Counterexample.datum, UnreachableLimit.object])
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hp
  intro he
  have hb := congrArg (fun mem : Lir.Memory => mem.bytes a) he
  cases hr : P.data "root" with
  | none =>
    simp [initMem, dataDefs, input, units, root, datum, List.find?,
      MirPassDraft.Counterexample.datum, UnreachableLimit.object, ha, hr,
      objectByte, zeroMem] at hb
    have hz := hb (by decide)
    exact (by decide : (1 : BitVec 8) ≠ 0) hz
  | some ar =>
    simp [initMem, dataDefs, input, units, root, datum, List.find?,
      MirPassDraft.Counterexample.datum, UnreachableLimit.object, ha, hr,
      objectByte, zeroMem] at hb
    have hz := hb (by decide)
    exact (by decide : (1 : BitVec 8) ≠ 0) hz

/-- Retaining both objects gives compatible placements in ample memory. -/
def fullPlacement : Placement :=
  ⟨fun s => if s = "root" then some 1 else if s = "object" then some 2 else none,
   fun s => if s = "main" then some 1 else none, 3⟩

theorem full_valid (fn : Func) (hfn : fn = inputFunc ∨ fn = outputFunc) :
    fullPlacement.Valid (units fn) 16384 := by
  rcases hfn with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_, ?_, by decide, ?_, ?_⟩
    · intro s _ hd
      by_cases hs : s = "root"
      · simp [fullPlacement, hs]
      by_cases ht : s = "object"
      · simp [fullPlacement, ht]
      simp [dataOf, dataDefs, units, root, datum, MirPassDraft.Counterexample.datum,
        UnreachableLimit.object] at hd
      rcases hd with hd | hd
      · exact (hs hd.symm).elim
      · exact (ht hd.symm).elim
    · intro s _ _ hf
      by_cases hs : s = "main"
      · simp [fullPlacement, hs]
      simp [funcOf, funcDefs, units, inputFunc, outputFunc] at hf
      exact (hs hf.symm).elim
    · simp [dataDefs, units, root, datum, MirPassDraft.Counterexample.datum,
        UnreachableLimit.object, fullPlacement]
    · simp [dataDefs, units, root, datum, MirPassDraft.Counterexample.datum,
        UnreachableLimit.object, fullPlacement]
    · intro s a hs
      by_cases hn : s = "main"
      · simp [fullPlacement, hn] at hs
        omega
      · simp [fullPlacement, hn] at hs
    · intro s s' a hs hs'
      simp only [fullPlacement] at hs hs'
      split at hs <;> split at hs' <;> simp_all

/-- The eligibility restriction admits this transformation on a nonempty domain;
its initial memory and heap can be retained while the reference is deleted. -/
theorem eligible_exists :
    fullPlacement.Valid output 16384 ∧ Eligible input output 16384 fullPlacement := by
  refine ⟨full_valid _ (.inr rfl), fullPlacement, full_valid _ (.inl rfl), rfl, ?_, ?_⟩
  · intro s _
    exact symValue_eq _ s
  · exact initMem_eq _ _

/-- Even with ample memory, the actual registered checked linker cannot compose
with this draft-certified deletion at the identity memory observation. -/
theorem composite_not_link :
    ¬ Contract.link (fun us => Registry.Stage.link (erase us)) := by
  classical
  intro hc
  have he : Registry.Stage.link (erase input) = .ok linked := by
    simpa [erase] using checked_link
  obtain ⟨P, hv, hsim⟩ := hc input linked he 16384 (by decide) (by decide)
  have hs := start_eq inputFunc P 16384 rfl rfl
  have hb := Deletion.returns inputFunc (.inl rfl) input P (initMem input P 16384)
  obtain ⟨t, ht, hbt⟩ := hsim _ hs _ hb (by intro h; cases h)
  rw [lir_start] at ht
  cases ht
  have hu := Lir.Behaves.unique hbt (lir_returns (linkedMem linked 16384))
  have hm : initMem input P 16384 = zeroMem 16384 := by
    simpa only [Lir.Behavior.returned.injEq, true_and, linked_mem] using hu
  exact input_mem_ne _ P hv hm

/-- The named open obligation is false for the real linker and this pass. -/
theorem not_placementAwareLink : ¬ PlacementAwareLink erase Registry.Stage.link := by
  intro h
  exact composite_not_link (MirPassDraft.link_comp erase_correct h)

/-- Fixing the downstream stage to the actual linker does not repair the draft's
composition gap. This statement does not concern the current old-contract passes. -/
theorem not_all_draft_passes :
    ¬ (∀ f, mirPassDraft f → PlacementAwareLink f Registry.Stage.link) := by
  intro h
  exact not_placementAwareLink (h erase erase_correct)

/-- The joint obligation is inhabited for the identity pass and actual linker. -/
theorem identity_placementAwareLink : PlacementAwareLink id Registry.Stage.link := by
  intro us l hl m hn hm
  obtain ⟨P, hv, hsim⟩ := Registry.Proof.link us l hl m hn hm
  exact ⟨P, hv, ⟨P, hv, rfl, fun _ _ => rfl, rfl⟩, hsim⟩

/-- The active pipeline still satisfies the existing contract: every registered
pass retains its old-contract certificate, which already composes with link. -/
theorem current_pipeline :
    Contract.link (fun us => Registry.Stage.link (Registry.Stage.mirOpt us)) :=
  Mir.Pass.link_comp Registry.Proof.link Registry.Proof.mirOpt

#print axioms checked_link
#print axioms erase_correct
#print axioms eligible_exists
#print axioms composite_not_link
#print axioms not_placementAwareLink
#print axioms identity_placementAwareLink
#print axioms current_pipeline

end Silmaril.Compile.Mir.MirPassLinkLimit
