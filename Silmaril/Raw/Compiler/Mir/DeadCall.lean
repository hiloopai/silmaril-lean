module

public import Silmaril.Compiler.Mir.ConstProp.Defs
/-! # Dead calls to undefined symbols

`DeadCall.run` deletes the direct calls to symbols that **no unit defines** (no function
and no data object of that name, weak or not) from the blocks of a function that are
**unreachable** from its entry block. Everything else stays: every other instruction, the
terminators, the number of blocks, the data. This is the `link_error` idiom of the gcc
torture tests (`if (0) link_error ();`): after constant propagation turns the branch into a
jump, the call is dead, and the link must not fail on its undefined symbol.

Reachability comes from an unverified worklist (`explore`) and is **checked** per function
(`check`): block 0 is reachable, and every successor of a reachable block is reachable.
A function whose exploration fails the check counts every block as reachable (`live`
falls back to `#[]`) and is left unchanged.

Correctness (`DeadCall.correct : Contract.mirPass run`, through `FuncPass.mirPass_of`):

* the pass keeps every `addr` and every reference to a defined symbol, so the names in
  force, `MirSem.taken` (indirect-call targets), the data and the initial memory are the
  input's (`FuncPass.Iface`);
* it drops only references to undefined symbols, which `MirSem.Placement.Valid` places
  nowhere, so every valid placement of the output is one of the input
  (`FuncPass.valid_of`). This is why `UnreachableLimit.deletion_not_mirPass` does not
  apply: its counterexample deletes an `addr` of a *defined* object, which the input must
  place and the output need not;
* the blocks that can run are unchanged, so the pass is a lock-step simulation with equal
  frames (`FuncPass.Sim` with `PR f l i fr i' fr' := i' = i ∧ fr' = fr ∧` block `l` is
  reachable by the check, which a jump or branch carries to its target). -/

@[expose] public section

namespace Silmaril.Compile.Mir.DeadCall

open Silmaril.Machine
open Silmaril.Compile.Contract.MirSem
open Silmaril.Compile.Mir.FuncPass

/-! ## The pass -/

/-- No unit has a function or a data object named `s` (weak or not). -/
def undefined (us : Array Mir.Unit) (s : String) : Bool :=
  !(us.any fun u => u.funcs.any (·.name == s) || u.data.any (·.name == s))

/-- A direct call to a symbol that no unit defines. -/
def deadCall (us : Array Mir.Unit) : Instr → Bool
  | .call s _ _ => undefined us s
  | _ => false

/-- Whether block `l` may run under the reachability `R`; a label past `R` may. -/
def liveAt (R : Array Bool) (l : Nat) : Bool := R[l]?.getD true

/-- Block 0 may run, and every successor of a block that may run may run. -/
def check (f : Func) (R : Array Bool) : Bool :=
  liveAt R 0 &&
  (List.range f.blocks.size).all fun l =>
    match f.blocks[l]? with
    | some b => !liveAt R l || (ConstProp.succs b.term).all (liveAt R)
    | none => true

/-- The unverified worklist: mark the blocks reached from the labels `ws`, with `k` steps
at most. -/
def explore (f : Func) : Nat → List Nat → Array Bool → Array Bool
  | 0, _, R => R
  | _, [], R => R
  | k + 1, l :: ws, R =>
    match f.blocks[l]? with
    | some b =>
      if liveAt R l then explore f k ws R
      else explore f k (ConstProp.succs b.term ++ ws) (R.set! l true)
    | none => explore f k ws R

/-- The checked reachable blocks of `f`; every block when the check fails. Each block is
marked once and pushes two labels at most, so `2 * size + 2` steps suffice. -/
def live (f : Func) : Array Bool :=
  let R := explore f (2 * f.blocks.size + 2) [0] (Array.replicate f.blocks.size false)
  if check f R then R else #[]

/-- A block without its dead calls. -/
def dropBlock (us : Array Mir.Unit) (b : Block) : Block :=
  { b with instrs := b.instrs.filter fun i => !deadCall us i }

/-- Drop the dead calls of the unreachable blocks of `f`. -/
def dcFunc (us : Array Mir.Unit) (f : Func) : Func :=
  let R := live f
  { f with blocks := f.blocks.mapIdx fun l b => if liveAt R l then b else dropBlock us b }

/-- The pass on units. -/
def run (us : Array Mir.Unit) : Array Mir.Unit := mapFuncs (dcFunc us) us

/-! ## Correctness -/

theorem check_live (f : Func) : check f (live f) = true := by
  unfold live
  dsimp only
  split
  · assumption
  · simp only [check, liveAt, Array.getElem?_empty, Option.getD_none, Bool.not_true,
      Bool.false_or, Bool.true_and, List.all_eq_true, List.mem_range]
    intro l _
    split <;> simp [liveAt]

theorem check_sound {f : Func} {R : Array Bool} (h : check f R = true) :
    liveAt R 0 = true ∧ ∀ l b, f.blocks[l]? = some b → liveAt R l = true →
      ∀ l' ∈ ConstProp.succs b.term, liveAt R l' = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  refine ⟨h.1, fun l b hb hl l' hl' => ?_⟩
  have hs := h.2 l (Array.getElem?_eq_some_iff.mp hb).1
  rw [hb] at hs
  simp only [hl, Bool.not_true, Bool.false_or, List.all_eq_true] at hs
  exact hs l' hl'

theorem blocks_get (us : Array Mir.Unit) (f : Func) (l : Nat) :
    (dcFunc us f).blocks[l]? =
      f.blocks[l]?.map fun b => if liveAt (live f) l then b else dropBlock us b := by
  simp [dcFunc, Array.getElem?_mapIdx]

theorem blocks_live {us : Array Mir.Unit} {f : Func} {l : Nat} (h : liveAt (live f) l = true) :
    (dcFunc us f).blocks[l]? = f.blocks[l]? := by
  rw [blocks_get]
  simp [h]

theorem undefined_spec {us : Array Mir.Unit} {n : String} (h : undefined us n = true) :
    Undefined us n := by
  simp only [undefined, Bool.not_eq_true', Array.any_eq_false] at h
  have hu : ∀ u ∈ us.toList, (∀ f ∈ u.funcs.toList, f.name ≠ n) ∧ ∀ d ∈ u.data.toList, d.name ≠ n := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
    have hi' := h i (by simpa using hi)
    refine ⟨fun f hf' heq => hi' ?_, fun d hd' heq => hi' ?_⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf'
      simp only [Bool.or_eq_true, Array.any_eq_true, beq_iff_eq]
      exact .inl ⟨j, by simpa using hj, by simpa using heq⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd'
      simp only [Bool.or_eq_true, Array.any_eq_true, beq_iff_eq]
      exact .inr ⟨j, by simpa using hj, by simpa using heq⟩
  constructor
  · rw [funcOf, List.find?_eq_none]
    intro f hf
    simp only [funcDefs, List.mem_filter, List.mem_flatMap] at hf
    obtain ⟨⟨u, hu', hf⟩, -⟩ := hf
    simpa using (hu u hu').1 f hf
  · rw [dataOf, List.find?_eq_none]
    intro d hd
    simp only [dataDefs, List.mem_filter, List.mem_flatMap] at hd
    obtain ⟨⟨u, hu', hd⟩, -⟩ := hd
    simpa using (hu u hu').2 d hd

theorem mem_blocks {us : Array Mir.Unit} {f : Func} {b' : Block}
    (h : b' ∈ (dcFunc us f).blocks.toList) :
    ∃ b ∈ f.blocks.toList, b' = b ∨ b' = dropBlock us b := by
  obtain ⟨l, hl⟩ := List.mem_iff_getElem?.mp h
  rw [Array.getElem?_toList, blocks_get, Option.map_eq_some_iff] at hl
  obtain ⟨b, hb, rfl⟩ := hl
  refine ⟨b, List.mem_iff_getElem?.mpr ⟨l, by rw [Array.getElem?_toList]; exact hb⟩, ?_⟩
  split <;> simp

theorem mem_blocks' {us : Array Mir.Unit} {f : Func} {b : Block} (h : b ∈ f.blocks.toList) :
    ∃ b' ∈ (dcFunc us f).blocks.toList, b' = b ∨ b' = dropBlock us b := by
  obtain ⟨l, hl⟩ := List.mem_iff_getElem?.mp h
  rw [Array.getElem?_toList] at hl
  refine ⟨_, List.mem_iff_getElem?.mpr ⟨l, by rw [Array.getElem?_toList, blocks_get, hl]; rfl⟩, ?_⟩
  split <;> simp

theorem mem_drop {us : Array Mir.Unit} {b : Block} {i : Instr} :
    i ∈ (dropBlock us b).instrs.toList ↔ i ∈ b.instrs.toList ∧ deadCall us i = false := by
  simp [dropBlock]

/-- The output's references are the input's. -/
theorem refs_fwd {us : Array Mir.Unit} {f : Func} {k : Bool} {n : String}
    (h : (k, n) ∈ funcRefs (dcFunc us f)) : (k, n) ∈ funcRefs f := by
  obtain ⟨b', hb', i, hi, hk⟩ := (mem_refs_iff _ k n).mp h
  obtain ⟨b, hb, rfl | rfl⟩ := mem_blocks hb'
  · exact (mem_refs_iff f k n).mpr ⟨_, hb, i, hi, hk⟩
  · exact (mem_refs_iff f k n).mpr ⟨_, hb, i, (mem_drop.mp hi).1, hk⟩

/-- The input's references are the output's, but for calls to undefined symbols. -/
theorem refs_back {us : Array Mir.Unit} {f : Func} {k : Bool} {n : String}
    (h : (k, n) ∈ funcRefs f) :
    (k, n) ∈ funcRefs (dcFunc us f) ∨ (k = false ∧ undefined us n = true) := by
  obtain ⟨b, hb, i, hi, hk⟩ := (mem_refs_iff f k n).mp h
  obtain ⟨b', hb', rfl | rfl⟩ := mem_blocks' (us := us) hb
  · exact .inl ((mem_refs_iff _ k n).mpr ⟨_, hb', i, hi, hk⟩)
  · cases hd : deadCall us i
    · exact .inl ((mem_refs_iff _ k n).mpr ⟨_, hb', i, mem_drop.mpr ⟨hi, hd⟩, hk⟩)
    · right
      cases i <;> simp_all [deadCall, refKey]

theorem iface (us : Array Mir.Unit) : Iface (dcFunc us) where
  name _ := rfl
  params _ := rfl
  results _ := rfl
  weak _ := rfl
  size _ := by simp [dcFunc]
  addrs _ _ := ⟨refs_fwd, fun h => (refs_back h).resolve_right (by simp)⟩

/-- The point relation: same index and frame, at a block the check reaches. -/
def PR (f : Func) (l i : Nat) (fr : Lir.Frame Nat) (i' : Nat) (fr' : Lir.Frame Nat) : Prop :=
  i' = i ∧ fr' = fr ∧ liveAt (live f) l = true

theorem termOut_succs {fr : Lir.Frame Nat} {t : Lir.Term Nat} {l : Nat}
    (h : termOut fr t = .goto l) : l ∈ ConstProp.succs t := by
  cases t with
  | jump l' => cases h; simp [ConstProp.succs]
  | branch c l₁ l₂ =>
    simp only [termOut] at h
    split at h
    · simp only [TermOut.goto.injEq] at h
      split at h <;> simp [ConstProp.succs, ← h]
    · cases h
  | ret locs =>
    simp only [termOut] at h
    split at h <;> cases h
  | trap => cases h

theorem sim (us : Array Mir.Unit) : Sim (dcFunc us) PR := fun f =>
  have hc := check_sound (check_live f)
  { entry := fun _ => ⟨rfl, rfl, hc.1⟩
    instr := by
      intro l b b' i fr i' fr' x hb hb' hp hx
      obtain ⟨rfl, rfl, hl⟩ := hp
      rw [blocks_live hl, hb] at hb'
      cases hb'
      rw [hx]
      cases x with
      | op o => exact fun m fr₁ m₁ he => .inr ⟨o, rfl, fr₁, he, rfl, rfl, hl⟩
      | fop op d a c => exact fun fr₁ he => ⟨op, d, a, c, rfl, fr₁, he, rfl, rfl, hl⟩
      | addr d s off => exact ⟨rfl, fun _ => ⟨rfl, rfl, hl⟩⟩
      | call c args res =>
        exact fun vals hv => ⟨args, rfl, hv,
          fun _ _ _ hw hw' => by rw [hw] at hw'; cases hw'; exact ⟨rfl, rfl, hl⟩⟩
      | callIndirect t args res =>
        exact fun v vals ht hv => ⟨t, args, rfl, ht, hv,
          fun _ _ _ hw hw' => by rw [hw] at hw'; cases hw'; exact ⟨rfl, rfl, hl⟩⟩
    term := by
      intro l b b' i fr i' fr' hb hb' hp hi
      obtain ⟨rfl, rfl, hl⟩ := hp
      rw [blocks_live hl, hb] at hb'
      cases hb'
      exact ⟨hi, fun _ => ⟨rfl, fun l' hl' => ⟨rfl, rfl, hc.2 l b hb hl l' (termOut_succs hl')⟩⟩⟩ }

/-- **Deleting dead calls to undefined symbols refines the input** (`Contract.mirPass`). -/
theorem correct : Contract.mirPass run :=
  mirPass_of (G := dcFunc) (PR := fun _ => PR) iface sim fun us _ _ =>
    valid_of (iface us) us fun _ _ _ h => (refs_back h).imp id fun h => undefined_spec h.2

end Silmaril.Compile.Mir.DeadCall
