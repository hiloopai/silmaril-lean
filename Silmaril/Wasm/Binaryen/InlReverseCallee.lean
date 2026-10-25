module

public import Silmaril.Wasm.Binaryen.InlI
public import Silmaril.Wasm.Binaryen.InlReverseHead
public import Silmaril.Wasm.Binaryen.SimplifyLocalsLiteMacro
public import Silmaril.Wasm.Binaryen.RemoveUnusedBrsGuardSim

@[expose] public section

/-! # Chosen reverse steps in a relocated callee

Each theorem starts with an actual step of the relocated code and preserves its
chosen result. The numerical profile is arbitrary. For local access, the bound
is on the original local index: the fallback in `xIdx` means that a successful
relocated access alone would not imply a valid original access.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Validation SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Numerics.Profile}

/-- The index relocation is exact for an original in-bounds local. -/
theorem reverse_callee_index (ok : PrmOk p) {F : Frame} {x : LocalIdx}
    (locals : F.locals.length = p.ext) (bound : x.toNat < F.locals.length) :
    (InlineTy.xIdx p.base x).toNat = p.base + x.toNat :=
  InlineTy.xIdx_toNat (by have := ok.bound; omega)

/-- A chosen relocated load reads exactly the same callee local. -/
theorem reverse_callee_localGet (ok : PrmOk p) {d : Nat} {L : List (Option Val)}
    {s t : Store H} {F : Frame} {x : LocalIdx} {args : List Val} {next : Config H}
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext) (bound : x.toNat < F.locals.length)
    (stores : SR p s t)
    (selected : Det.Head P t ⟨L ++ F.locals, p.mi⟩ args
      (.plain (.localGet (InlineTy.xIdx p.base x))) next) :
    ∃ originalNext : Config H,
      Det.Head P s F args (.plain (.localGet x)) originalNext ∧
      MR p (.i d L) originalNext next ∧ SR p originalNext.store next.store := by
  obtain ⟨rfl, v, lookup, rfl⟩ := GuardSim.head_localGet selected
  have index := reverse_callee_index ok locals bound
  have originalLookup : F.local? x = some (some v) := by
    simp only [Frame.local?] at lookup ⊢
    rw [index, List.getElem?_append_right (by omega), prefixLength,
      Nat.add_sub_cancel_left] at lookup
    exact lookup
  exact ⟨⟨s, F, [v.toAdmin]⟩, .variable (.localGet originalLookup),
    ⟨moduleEq, prefixLength, locals, rfl, LI.of_vals d [v]⟩, stores⟩

/-- A chosen relocated store changes only the corresponding callee local. -/
theorem reverse_callee_localSet (ok : PrmOk p) {d : Nat} {L : List (Option Val)}
    {s t : Store H} {F : Frame} {x : LocalIdx} {args : List Val} {next : Config H}
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext) (bound : x.toNat < F.locals.length)
    (stores : SR p s t)
    (selected : Det.Head P t ⟨L ++ F.locals, p.mi⟩ args
      (.plain (.localSet (InlineTy.xIdx p.base x))) next) :
    ∃ originalNext : Config H,
      Det.Head P s F args (.plain (.localSet x)) originalNext ∧
      MR p (.i d L) originalNext next ∧ SR p originalNext.store next.store := by
  obtain ⟨v, rfl, _, rfl⟩ := SimplifyLocalsLite.head_localSet selected
  have index := reverse_callee_index ok locals bound
  refine ⟨⟨s, F.setLocal x v, []⟩, .variable (.localSet bound),
    ⟨?_, prefixLength, ?_, ?_, .nil⟩, stores⟩
  · simp [Frame.setLocal, moduleEq]
  · simp [Frame.setLocal, locals]
  · simp only [Frame.setLocal]
    rw [index, List.set_append_right _ _ (by omega), prefixLength, Nat.add_sub_cancel_left]

/-- Tee expands to the same value and the relocated pending store. Unlike a
load/store step, the expansion itself does not inspect the local index. -/
theorem reverse_callee_localTee {d : Nat} {L : List (Option Val)}
    {s t : Store H} {F : Frame} {x : LocalIdx} {args : List Val} {next : Config H}
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext) (stores : SR p s t)
    (selected : Det.Head P t ⟨L ++ F.locals, p.mi⟩ args
      (.plain (.localTee (InlineTy.xIdx p.base x))) next) :
    ∃ originalNext : Config H,
      Det.Head P s F args (.plain (.localTee x)) originalNext ∧
      MR p (.i d L) originalNext next ∧ SR p originalNext.store next.store := by
  obtain ⟨v, rfl, rfl⟩ := SimplifyLocalsLite.head_localTee selected
  exact ⟨⟨s, F, [v.toAdmin, v.toAdmin, .plain (.localSet x)]⟩, .variable .localTee,
    ⟨moduleEq, prefixLength, locals, rfl,
      .cons (AI.of_val d v) (.cons (AI.of_val d v) (.cons (.plain trivial) .nil))⟩, stores⟩

/-- Non-call computational heads retain the actual selected numerical, memory,
table, reference or aggregate result in the callee relation. -/
theorem reverse_callee_noncall_head {d : Nat} {L : List (Option Val)}
    {s t : Store H} {F : Frame} {args : List Val} {head : Admin} {next : Config H}
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext) (stores : SR p s t)
    (simple : SimpleE head) (nonstruct : ¬ StructE head) (nontail : ¬ TailE head)
    (noncall : ¬ head.IsCallRef)
    (selected : Det.Head P t ⟨L ++ F.locals, p.mi⟩ args head next) :
    ∃ originalNext : Config H,
      Det.Head P s F args head originalNext ∧
      MR p (.i d L) originalNext next ∧ SR p originalNext.store next.store := by
  have notCall : ¬ CallData t ⟨L ++ F.locals, p.mi⟩ args head next := by
    rintro ⟨_, _, _, _, _, _, _, isCall, _⟩
    exact noncall isCall
  rcases head_simple_reverse stores moduleEq.symm simple selected with call |
      ⟨originalNext, actual, originalFrame, transformedFrame, code, related⟩
  · exact (notCall call).elim
  · rcases head_out selected simple nonstruct with call | out | ⟨tail, _⟩
    · exact (notCall call).elim
    · refine ⟨originalNext, actual, ⟨?_, prefixLength, ?_, ?_, ?_⟩, related⟩
      · rw [originalFrame]; exact moduleEq
      · rw [originalFrame]; exact locals
      · rw [transformedFrame, originalFrame]
      · rw [code]; exact LI.of_out out
    · exact (nontail tail).elim

/-! ## Structured entries

These rules inspect the selected transformed structural step, rather than
deriving a successor from uniqueness. They therefore retain the exact resolved
block type and selected conditional branch under every profile.
-/

section structural

variable {d : Nat} {L : List (Option Val)} {s t : Store H} {F : Frame}
  {args : List Val} {next : Config H}

theorem reverse_callee_block {bt : BlockType} {body : List Instr}
    (good : InlineTy.retGoodL (d + 1) body)
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext) (stores : SR p s t)
    (selected : Det.Head P t ⟨L ++ F.locals, p.mi⟩ args
      (.plain (InlineTy.xform p.base d (.block bt body))) next) :
    ∃ originalNext : Config H,
      Det.Head P s F args (.plain (.block bt body)) originalNext ∧
      MR p (.i d L) originalNext next ∧ SR p originalNext.store next.store := by
  obtain ⟨ps, rs, type, count, rfl⟩ := head_block selected
  exact ⟨⟨s, F, [.label rs.length [] (vals args ++ expression body)]⟩,
    .block (by rw [moduleEq]; exact type) count,
    ⟨moduleEq, prefixLength, locals, rfl,
      .cons (.label trivial (LI.append (LI.of_vals (d + 1) args) (LI.of_xformL good))) .nil⟩,
    stores⟩

theorem reverse_callee_loop {bt : BlockType} {body : List Instr}
    (good : InlineTy.retGoodL (d + 1) body)
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext) (stores : SR p s t)
    (selected : Det.Head P t ⟨L ++ F.locals, p.mi⟩ args
      (.plain (InlineTy.xform p.base d (.loop bt body))) next) :
    ∃ originalNext : Config H,
      Det.Head P s F args (.plain (.loop bt body)) originalNext ∧
      MR p (.i d L) originalNext next ∧ SR p originalNext.store next.store := by
  simp only [InlineTy.xform] at selected
  cases selected with
  | loop type count =>
    exact ⟨_, .loop (by rw [moduleEq]; exact type) count,
      ⟨moduleEq, prefixLength, locals, rfl,
        .cons (.label ⟨good, trivial⟩
          (LI.append (LI.of_vals (d + 1) args) (LI.of_xformL good))) .nil⟩, stores⟩
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])

theorem reverse_callee_if {bt : BlockType} {yes no : List Instr}
    (yesGood : InlineTy.retGoodL (d + 1) yes)
    (noGood : InlineTy.retGoodL (d + 1) no)
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext) (stores : SR p s t)
    (selected : Det.Head P t ⟨L ++ F.locals, p.mi⟩ args
      (.plain (InlineTy.xform p.base d (.if_ bt yes no))) next) :
    ∃ originalNext : Config H,
      Det.Head P s F args (.plain (.if_ bt yes no)) originalNext ∧
      MR p (.i d L) originalNext next ∧ SR p originalNext.store next.store := by
  simp only [InlineTy.xform] at selected
  cases selected with
  | ifTrue condition =>
    exact ⟨_, .ifTrue condition,
      ⟨moduleEq, prefixLength, locals, rfl, .cons (.plain yesGood) .nil⟩, stores⟩
  | ifFalse condition =>
    exact ⟨_, .ifFalse condition,
      ⟨moduleEq, prefixLength, locals, rfl, .cons (.plain noGood) .nil⟩, stores⟩
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])

theorem reverse_callee_tryTable {bt : BlockType} {catches : List Catch} {body : List Instr}
    (good : InlineTy.retGoodL (d + 1) body)
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext) (stores : SR p s t)
    (selected : Det.Head P t ⟨L ++ F.locals, p.mi⟩ args
      (.plain (InlineTy.xform p.base d (.tryTable bt catches body))) next) :
    ∃ originalNext : Config H,
      Det.Head P s F args (.plain (.tryTable bt catches body)) originalNext ∧
      MR p (.i d L) originalNext next ∧ SR p originalNext.store next.store := by
  simp only [InlineTy.xform] at selected
  cases selected with
  | tryTable type count =>
    exact ⟨_, .tryTable (by rw [moduleEq]; exact type) count,
      ⟨moduleEq, prefixLength, locals, rfl,
        .cons (.handler (.cons (.label trivial
          (LI.append (LI.of_vals (d + 1) args) (LI.of_xformL good))) .nil)) .nil⟩, stores⟩
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])

end structural

end Silmaril.Wasm.Binaryen.InlR
