module

public import Silmaril.Compiler.Native.Optimize.LocalSSA.Defs
@[expose] public section

namespace Silmaril.Compiler.Native.Optimize

open Silmaril.Machine

theorem find_version_filter (versions : List (Nat × Nat)) (original reg : Nat)
    (hne : reg ≠ original) :
    ((versions.filter (·.1 != original)).find? (·.1 == reg)) =
      versions.find? (·.1 == reg) := by
  induction versions with
  | nil => rfl
  | cons entry rest ih =>
    by_cases ho : entry.1 = original
    · simp [ho, Ne.symm hne, ih]
    · simp [ho, ih, List.find?_cons]

/-- Defining an original register updates exactly its current SSA name. -/
theorem read_define (s : Rename) (original reg : Nat) :
    ((define original).run s).2.read reg =
      if reg = original then s.next else s.read reg := by
  change (Rename.read
    { versions := (original, s.next) :: s.versions.filter (·.1 != original),
      next := s.next + 1 } reg) = _
  by_cases h : reg = original
  · subst reg
    simp [Rename.read]
  · simp [Rename.read, h, Ne.symm h, find_version_filter s.versions original reg h]

/-- The initial renaming environment satisfies the freshness invariant. -/
theorem bounded_initial (base : Nat) : Rename.Bounded base { next := base } := by
  exact ⟨le_rfl, fun _ h => h⟩

/-- Allocating a fresh name preserves the bounded-name invariant. -/
theorem bounded_define {base : Nat} {s : Rename} (bounded : s.Bounded base)
    (original : Nat) : ((define original).run s).2.Bounded base := by
  refine ⟨bounded.1.trans (Nat.le_succ _), fun reg hr => ?_⟩
  rw [read_define]
  by_cases h : reg = original
  · simp only [h, ↓reduceIte]
    exact Nat.lt_succ_self _
  · simp only [h, ↓reduceIte]
    exact (bounded.2 reg hr).trans (Nat.lt_succ_self _)

/-- Writing a source register and its allocated SSA version preserves the frame
relation. Freshness ensures the new destination cannot overwrite another input
or previously allocated version. This is the semantic invariant for all writes. -/
theorem agrees_define {base : Nat} {s : Rename} {source target : Lir.Frame Nat}
    (bounded : s.Bounded base) (agree : s.Agrees base source target)
    (original : Nat) (value : Lir.Word) :
    ((define original).run s).2.Agrees base
      (source.set original value) (target.set s.next value) := by
  refine ⟨agree.1, fun reg hr => ?_⟩
  rw [read_define]
  by_cases h : reg = original
  · simp [h]
  · have fresh : s.read reg ≠ s.next := Nat.ne_of_lt (bounded.2 reg hr)
    simp [h, fresh, agree.2 reg hr]

/-- Updating a frame slot identically preserves register and slot agreement. -/
theorem agrees_slotSet {base : Nat} {s : Rename} {source target : Lir.Frame Nat}
    (agree : s.Agrees base source target) (slot : Nat) (value : Lir.Word) :
    s.Agrees base (source.setSlot slot value) (target.setSlot slot value) := by
  refine ⟨?_, fun reg hr => agree.2 reg hr⟩
  funext n
  simp [agree.1]

/-- Register renaming simulates every straight-line Lir operation, including
partial arithmetic, memory access and frame slots. Operand bounds are explicit;
the same returned memory and the updated frame relation are produced. This is
the instruction-level semantic premise for the local SSA round trip. -/
theorem renameOp_exec {base : Nat} {s : Rename} {source target : Lir.Frame Nat}
    {memory memory' : Lir.Memory} {o : Lir.Op Nat} {source' : Lir.Frame Nat}
    (bounded : s.Bounded base) (agree : s.Agrees base source target)
    (uses : ∀ reg ∈ Silmaril.Compile.Mir.DeadCode.opUses o, reg < base)
    (exec : o.exec source memory = some (source', memory')) :
    ∃ target', ((renameOp o).run s).1.exec target memory = some (target', memory') ∧
      ((renameOp o).run s).2.Bounded base ∧
      ((renameOp o).run s).2.Agrees base source' target' := by
  cases o with
  | const dest value =>
    show ∃ target', ((renameOp (.const dest value)).run s).1.exec target memory = some (target', memory') ∧
      ((renameOp (.const dest value)).run s).2.Bounded base ∧
      ((renameOp (.const dest value)).run s).2.Agrees base source' target'
    have result : source.set dest value = source' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.some.injEq, Prod.mk.injEq] using exec
    obtain ⟨hframe, hmem⟩ := result
    rw [← hframe, ← hmem]
    refine ⟨target.set s.next value, ?_, bounded_define bounded dest, agrees_define bounded agree dest value⟩
    rfl
  | move dest src =>
    show ∃ target', ((renameOp (.move dest src)).run s).1.exec target memory = some (target', memory') ∧
      ((renameOp (.move dest src)).run s).2.Bounded base ∧
      ((renameOp (.move dest src)).run s).2.Agrees base source' target'
    have result : ∃ value, source.get src = some value ∧ source.set dest value = source' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using exec
    obtain ⟨value, hv, hframe, hmem⟩ := result
    rw [← hframe, ← hmem]
    refine ⟨target.set s.next value, ?_, bounded_define bounded dest, agrees_define bounded agree dest value⟩
    change (target.get (s.read src)).map (fun v => (target.set s.next v, memory)) = _
    rw [agree.2 src (uses src (by simp [Silmaril.Compile.Mir.DeadCode.opUses])), hv]
    rfl
  | unary op dest src =>
    show ∃ target', ((renameOp (.unary op dest src)).run s).1.exec target memory = some (target', memory') ∧
      ((renameOp (.unary op dest src)).run s).2.Bounded base ∧
      ((renameOp (.unary op dest src)).run s).2.Agrees base source' target'
    have result : ∃ value, source.get src = some value ∧
        source.set dest (op.eval value) = source' ∧
        memory = memory' := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using exec
    obtain ⟨value, hv, hframe, hmem⟩ := result
    rw [← hframe, ← hmem]
    refine ⟨target.set s.next (op.eval value), ?_,
      bounded_define bounded dest, agrees_define bounded agree dest (op.eval value)⟩
    change (target.get (s.read src)).map
      (fun v => (target.set s.next (op.eval v), memory)) = _
    rw [agree.2 src (uses src (by simp [Silmaril.Compile.Mir.DeadCode.opUses])), hv]
    rfl
  | binary op dest a b =>
    show ∃ target', ((renameOp (.binary op dest a b)).run s).1.exec target memory = some (target', memory') ∧
      ((renameOp (.binary op dest a b)).run s).2.Bounded base ∧
      ((renameOp (.binary op dest a b)).run s).2.Agrees base source' target'
    have result : ∃ x, source.get a = some x ∧
        ∃ y, source.get b = some y ∧
        ∃ value, op.eval x y = some value ∧
        source.set dest value = source' ∧
        memory = memory' := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using exec
    obtain ⟨x, hx, y, hy, value, hv, hframe, hmem⟩ := result
    rw [← hframe, ← hmem]
    refine ⟨target.set s.next value, ?_, bounded_define bounded dest, agrees_define bounded agree dest value⟩
    change (target.get (s.read a)).bind (fun x =>
      (target.get (s.read b)).bind fun y =>
        (op.eval x y).map fun v => (target.set s.next v, memory)) = _
    rw [agree.2 a (uses a (by simp [Silmaril.Compile.Mir.DeadCode.opUses])), hx]
    simp only [Option.bind_some]
    rw [agree.2 b (uses b (by simp [Silmaril.Compile.Mir.DeadCode.opUses])), hy]
    simp only [Option.bind_some, hv, Option.map_some]
  | load width ext dest baseReg offset =>
    show ∃ target', ((renameOp (.load width ext dest baseReg offset)).run s).1.exec target memory = some (target', memory') ∧
      ((renameOp (.load width ext dest baseReg offset)).run s).2.Bounded base ∧
      ((renameOp (.load width ext dest baseReg offset)).run s).2.Agrees base source' target'
    have result : ∃ address, source.get baseReg = some address ∧
        ∃ value, memory.load width ext (address.toNat + offset) = some value ∧
        source.set dest value = source' ∧
        memory = memory' := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using exec
    obtain ⟨address, ha, value, hv, hframe, hmem⟩ := result
    rw [← hframe, ← hmem]
    refine ⟨target.set s.next value, ?_, bounded_define bounded dest, agrees_define bounded agree dest value⟩
    change (target.get (s.read baseReg)).bind (fun a =>
      (memory.load width ext (a.toNat + offset)).map fun v =>
        (target.set s.next v, memory)) = _
    rw [agree.2 baseReg (uses baseReg (by simp [Silmaril.Compile.Mir.DeadCode.opUses])), ha]
    simp only [Option.bind_some, hv, Option.map_some]
  | store width baseReg offset src =>
    show ∃ target', ((renameOp (.store width baseReg offset src)).run s).1.exec target memory = some (target', memory') ∧
      ((renameOp (.store width baseReg offset src)).run s).2.Bounded base ∧
      ((renameOp (.store width baseReg offset src)).run s).2.Agrees base source' target'
    have result : ∃ address, source.get baseReg = some address ∧
        ∃ value, source.get src = some value ∧
        ∃ mem, memory.store width (address.toNat + offset) value = some mem ∧
        source = source' ∧
        mem = memory' := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using exec
    obtain ⟨address, ha, value, hv, mem, hm, hframe, hmem⟩ := result
    rw [← hframe, ← hmem]
    refine ⟨target, ?_, bounded, agree⟩
    change (target.get (s.read baseReg)).bind (fun a =>
      (target.get (s.read src)).bind fun v =>
        (memory.store width (a.toNat + offset) v).map fun m => (target, m)) = _
    rw [agree.2 baseReg (uses baseReg (by simp [Silmaril.Compile.Mir.DeadCode.opUses])), ha]
    simp only [Option.bind_some]
    rw [agree.2 src (uses src (by simp [Silmaril.Compile.Mir.DeadCode.opUses])), hv]
    simp only [Option.bind_some, hm, Option.map_some]
  | slotGet dest index =>
    show ∃ target', ((renameOp (.slotGet dest index)).run s).1.exec target memory = some (target', memory') ∧
      ((renameOp (.slotGet dest index)).run s).2.Bounded base ∧
      ((renameOp (.slotGet dest index)).run s).2.Agrees base source' target'
    have result : ∃ value, source.slots index = some value ∧ source.set dest value = source' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using exec
    obtain ⟨value, hv, hframe, hmem⟩ := result
    rw [← hframe, ← hmem]
    refine ⟨target.set s.next value, ?_, bounded_define bounded dest, agrees_define bounded agree dest value⟩
    change (target.slots index).map (fun v => (target.set s.next v, memory)) = _
    rw [← agree.1, hv]
    rfl
  | slotSet index src =>
    show ∃ target', ((renameOp (.slotSet index src)).run s).1.exec target memory = some (target', memory') ∧
      ((renameOp (.slotSet index src)).run s).2.Bounded base ∧
      ((renameOp (.slotSet index src)).run s).2.Agrees base source' target'
    have result : ∃ value, source.get src = some value ∧ source.setSlot index value = source' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using exec
    obtain ⟨value, hv, hframe, hmem⟩ := result
    rw [← hframe, ← hmem]
    refine ⟨target.setSlot index value, ?_, bounded, agrees_slotSet agree index value⟩
    change (target.get (s.read src)).map (fun v => (target.setSlot index v, memory)) = _
    rw [agree.2 src (uses src (by simp [Silmaril.Compile.Mir.DeadCode.opUses])), hv]
    rfl

/-- Call operands have the same values under the current SSA frame relation. -/
theorem readAll_renamed {base : Nat} {s : Rename} {source target : Lir.Frame Nat}
    (agree : s.Agrees base source target) (regs : List Nat)
    (bounds : ∀ reg ∈ regs, reg < base) :
    target.readAll (regs.map (fun r => .reg (s.read r))) =
      source.readAll (regs.map .reg) := by
  induction regs with
  | nil => rfl
  | cons reg rest ih =>
    simp only [Lir.Frame.readAll, List.map_cons, List.mapM_cons, Lir.Frame.read]
    have hread : target.regs (s.read reg) = source.regs reg :=
      agree.2 reg (bounds reg (by simp))
    have htail := ih (fun r hr => bounds r (by simp [hr]))
    simp only [Lir.Frame.readAll] at htail
    rw [hread, htail]

theorem defineResults_cons (reg : Nat) (regs : List Nat) (s : Rename) :
    ((reg :: regs).mapM define).run s =
      (let tail := (regs.mapM define).run ((define reg).run s).2
       (s.next :: tail.1, tail.2)) := by
  simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure]
  rfl

/-- Freshening a call's result list commutes with its actual left-to-right
frame writes, including repeated source destinations. -/
theorem defineResults_writeAll {base : Nat} {s : Rename}
    {source target source' : Lir.Frame Nat} (bounded : s.Bounded base)
    (agree : s.Agrees base source target) (regs : List Nat) (values : List Lir.Word)
    (written : source.writeAll (regs.map .reg) values = some source') :
    ∃ target', target.writeAll (((regs.mapM define).run s).1.map .reg) values = some target' ∧
      ((regs.mapM define).run s).2.Bounded base ∧
      ((regs.mapM define).run s).2.Agrees base source' target' := by
  induction regs generalizing s source target values with
  | nil =>
    cases values with
    | nil =>
      cases written
      exact ⟨target, rfl, bounded, agree⟩
    | cons value rest => cases written
  | cons reg regs ih =>
    cases values with
    | nil => cases written
    | cons value values =>
      have restWrite : (source.set reg value).writeAll (regs.map .reg) values = some source' :=
        written
      obtain ⟨target', hw, hb, ha⟩ := ih (bounded_define bounded reg)
        (agrees_define bounded agree reg value) values restWrite
      rw [defineResults_cons]
      exact ⟨target', hw, hb, ha⟩


theorem renameInstr_call_run (symbol : String) (args results : List Nat) (s : Rename) :
    (renameInstr (.call symbol args results)).run s =
      (let p := (results.mapM define).run s
       (.call symbol (args.map s.read) p.1, p.2)) := by
  simp only [renameInstr, StateT.run_bind, StateT.run_pure]
  rfl

theorem renameInstr_indirect_run (reg : Nat) (args results : List Nat) (s : Rename) :
    (renameInstr (.callIndirect reg args results)).run s =
      (let p := (results.mapM define).run s
       (.callIndirect (s.read reg) (args.map s.read) p.1, p.2)) := by
  simp only [renameInstr, StateT.run_bind, StateT.run_pure]
  rfl

theorem renameInstr_exec {base : Nat} {s : Rename} {source target source' : Lir.Frame Nat}
    {calls : OpenCalls} {memory memory' : Lir.Memory} {i : Silmaril.Compile.Mir.Instr}
    (bounded : s.Bounded base) (agree : s.Agrees base source target)
    (huses : ∀ reg ∈ uses i, reg < base)
    (exec : InstructionExec calls i source memory source' memory') :
    ∃ target', InstructionExec calls ((renameInstr i).run s).1 target memory target' memory' ∧
      ((renameInstr i).run s).2.Bounded base ∧
      ((renameInstr i).run s).2.Agrees base source' target' := by
  cases exec with
  | op he =>
    obtain ⟨target', he', hb, ha⟩ := renameOp_exec bounded agree huses he
    exact ⟨target', .op he', hb, ha⟩
  | @fop op dest a b source memory source' he =>
    show ∃ target', InstructionExec calls ((renameInstr (.fop op dest a b)).run s).1
        target memory target' memory ∧
      ((renameInstr (.fop op dest a b)).run s).2.Bounded base ∧
      ((renameInstr (.fop op dest a b)).run s).2.Agrees base source' target'
    have result : ∃ x, source.get a = some x ∧ ∃ y, source.get b = some y ∧
        source.set dest (op.eval x y) = source' := by
      simpa only [Lir.FOp.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] using he
    obtain ⟨x, hx, y, hy, hframe⟩ := result
    rw [← hframe]
    refine ⟨target.set s.next (op.eval x y), .fop ?_, bounded_define bounded dest,
      agrees_define bounded agree dest (op.eval x y)⟩
    change (target.get (s.read a)).bind
      (fun x => (target.get (s.read b)).map fun y => target.set s.next (op.eval x y)) = _
    rw [agree.2 a (huses a (by simp [uses])), hx]
    simp only [Option.bind_some]
    rw [agree.2 b (huses b (by simp [uses])), hy]
    rfl
  | addr he =>
    exact ⟨_, .addr he, bounded_define bounded _, agrees_define bounded agree _ _⟩
  | @call symbol args results source memory values returned source' memory' hargs hcall hw =>
    obtain ⟨target', hwrite, hb, ha⟩ := defineResults_writeAll bounded agree results returned hw
    rw [renameInstr_call_run]
    refine ⟨target', .call ?_ hcall hwrite, hb, ha⟩
    simpa only [List.map_map, Function.comp_def] using (readAll_renamed agree args huses).trans hargs
  | @indirect reg args results source memory pointer values returned source' memory'
      htarget hargs hcall hw =>
    obtain ⟨target', hwrite, hb, ha⟩ := defineResults_writeAll bounded agree results returned hw
    rw [renameInstr_indirect_run]
    refine ⟨target', .indirect ?_ ?_ hcall hwrite, hb, ha⟩
    · rw [agree.2 reg (huses reg (by simp [uses]))]
      exact htarget
    · simpa only [List.map_map, Function.comp_def] using
        (readAll_renamed agree args (fun r hr => huses r (by simp [uses, hr]))).trans hargs

theorem renameInstrs_cons (i : Silmaril.Compile.Mir.Instr)
    (rest : List Silmaril.Compile.Mir.Instr) (s : Rename) :
    ((i :: rest).mapM renameInstr).run s =
      (let p := (renameInstr i).run s
       let q := (rest.mapM renameInstr).run p.2
       (p.1 :: q.1, q.2)) := by
  simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure]
  rfl

theorem renameInstrs_exec {base : Nat} {s : Rename} {source target source' : Lir.Frame Nat}
    {calls : OpenCalls} {memory memory' : Lir.Memory} {instrs : List Silmaril.Compile.Mir.Instr}
    (bounded : s.Bounded base) (agree : s.Agrees base source target)
    (huses : ∀ i ∈ instrs, ∀ reg ∈ uses i, reg < base)
    (exec : InstructionsExec calls instrs source memory source' memory') :
    ∃ target', InstructionsExec calls ((instrs.mapM renameInstr).run s).1
        target memory target' memory' ∧
      ((instrs.mapM renameInstr).run s).2.Bounded base ∧
      ((instrs.mapM renameInstr).run s).2.Agrees base source' target' := by
  induction exec generalizing s target with
  | nil => exact ⟨target, .nil, bounded, agree⟩
  | @cons i rest source memory middle middleMem source' memory' hi hrest ih =>
    obtain ⟨target₁, hi', hb, ha⟩ := renameInstr_exec bounded agree
      (huses i (by simp)) hi
    obtain ⟨target₂, hrest', hb', ha'⟩ := ih hb ha (fun i hi => huses i (by simp [hi]))
    rw [renameInstrs_cons]
    exact ⟨target₂, .cons hi' hrest', hb', ha'⟩


theorem renameArray_run (instrs : Array Silmaril.Compile.Mir.Instr) (s : Rename) :
    (instrs.mapM renameInstr).run s =
      (let p := (instrs.toList.mapM renameInstr).run s
       (p.1.toArray, p.2)) := by
  rw [Array.mapM_eq_mapM_toList]
  rfl

theorem enter_body_exec {base : Nat} {source source' : Lir.Frame Nat}
    {calls : OpenCalls} {memory memory' : Lir.Memory} {b : Silmaril.Compile.Mir.Block}
    (huses : ∀ i ∈ b.instrs.toList, ∀ reg ∈ uses i, reg < base)
    (exec : InstructionsExec calls b.instrs.toList source memory source' memory') :
    ∃ target', InstructionsExec calls (enter base b).body.instrs.toList
        source memory target' memory' ∧
      ((b.instrs.toList.mapM renameInstr).run {next := base}).2.Agrees base source' target' := by
  have agree : Rename.Agrees base {next := base} source source := ⟨rfl, fun _ _ => rfl⟩
  obtain ⟨target', hrun, _, ha⟩ := renameInstrs_exec (bounded_initial base) agree huses exec
  refine ⟨target', ?_, ha⟩
  simpa only [enter, renameArray_run, List.toList_toArray] using hrun


theorem commitInstrs_exec {base : Nat} {source target : Lir.Frame Nat}
    {calls : OpenCalls} {memory : Lir.Memory} (versions : List (Nat × Nat))
    (bounds : ∀ p ∈ versions, p.1 < base ∧ base ≤ p.2)
    (values : ∀ p ∈ versions, ∃ w, target.get p.2 = some w ∧ source.get p.1 = some w) :
    ∃ target', InstructionsExec calls (commitInstrs versions) target memory target' memory ∧
      target'.slots = target.slots ∧
      (∀ reg ∈ versions.map (·.1), target'.get reg = source.get reg) ∧
      (∀ reg, reg ∉ versions.map (·.1) → target'.get reg = target.get reg) := by
  induction versions generalizing target with
  | nil => exact ⟨target, .nil, rfl, by simp, by simp⟩
  | cons p rest ih =>
    show ∃ target', InstructionsExec calls (commitInstrs (p :: rest)) target memory target' memory ∧
      target'.slots = target.slots ∧
      (∀ reg ∈ (p :: rest).map (·.1), target'.get reg = source.get reg) ∧
      (∀ reg, reg ∉ (p :: rest).map (·.1) → target'.get reg = target.get reg)
    obtain ⟨w, ht, hs⟩ := values p (by simp)
    have htailValues : ∀ q ∈ rest, ∃ v,
        (target.set p.1 w).get q.2 = some v ∧ source.get q.1 = some v := by
      intro q hq
      obtain ⟨v, hv, hv'⟩ := values q (by simp [hq])
      have hne : q.2 ≠ p.1 := by
        have hp : p.1 < base := (bounds p (by simp)).1
        have hq' : base ≤ q.2 := (bounds q (by simp [hq])).2
        omega
      exact ⟨v, by simpa [hne] using hv, hv'⟩
    obtain ⟨target', hrun, hslots, hwritten, huntouched⟩ :=
      ih (target := target.set p.1 w) (fun q hq => bounds q (by simp [hq])) htailValues
    refine ⟨target', .cons (.op ?_) hrun, hslots, ?_, ?_⟩
    · simp [Lir.Op.exec, ht]
    · show ∀ reg ∈ (p :: rest).map (·.1), target'.get reg = source.get reg
      intro reg hr
      have member : reg = p.1 ∨ reg ∈ rest.map (·.1) := by
        simpa only [List.map_cons, List.mem_cons] using hr
      rcases member with heq | hrest
      · rw [heq]
        by_cases hp : p.1 ∈ rest.map (·.1)
        · exact hwritten _ hp
        · rw [huntouched _ hp]
          simp [hs]
      · exact hwritten reg hrest
    · intro reg hr
      have hne : reg ≠ p.1 := by
        intro heq
        apply hr
        simp [heq]
      have hnot : reg ∉ rest.map (·.1) := fun h => hr (by simp [h])
      rw [huntouched reg hnot]
      simp [hne]


theorem valid_initial (base : Nat) : Rename.Valid base { next := base } :=
  ⟨bounded_initial base, by simp⟩

theorem defined_initial (base : Nat) (source : Lir.Frame Nat) :
    Rename.Defined { next := base } source := by simp [Rename.Defined]

theorem valid_define {base : Nat} {s : Rename} (valid : s.Valid base)
    (original : Nat) (bound : original < base) :
    ((define original).run s).2.Valid base := by
  refine ⟨bounded_define valid.1 original, fun p hp => ?_⟩
  change p ∈ (original, s.next) :: s.versions.filter (·.1 != original) at hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨bound, valid.1.1, by rw [read_define]; simp⟩
  · simp only [List.mem_filter, bne_iff_ne] at hp
    obtain ⟨hb, hv, hr⟩ := valid.2 p hp.1
    refine ⟨hb, hv, ?_⟩
    rw [read_define]
    simp [hp.2, hr]

theorem defined_define {s : Rename} {source : Lir.Frame Nat}
    (defined : s.Defined source) (original : Nat) (value : Lir.Word) :
    ((define original).run s).2.Defined (source.set original value) := by
  intro p hp
  change p ∈ (original, s.next) :: s.versions.filter (·.1 != original) at hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨value, by simp⟩
  · simp only [List.mem_filter, bne_iff_ne] at hp
    obtain ⟨w, hw⟩ := defined p hp.1
    exact ⟨w, by simpa [hp.2] using hw⟩

theorem valid_defineResults {base : Nat} {s : Rename} (valid : s.Valid base)
    (regs : List Nat) (bounds : ∀ reg ∈ regs, reg < base) :
    ((regs.mapM define).run s).2.Valid base := by
  induction regs generalizing s with
  | nil => exact valid
  | cons reg regs ih =>
    rw [defineResults_cons]
    exact ih (valid_define valid reg (bounds reg (by simp)))
      (fun r hr => bounds r (by simp [hr]))

theorem valid_renameOp {base : Nat} {s : Rename} (valid : s.Valid base)
    (o : Lir.Op Nat) (bounds : ∀ reg ∈ defs (.op o), reg < base) :
    ((renameOp o).run s).2.Valid base := by
  cases o <;> first
    | exact valid
    | exact valid_define valid _ (bounds _ (by simp [defs, Silmaril.Compile.Mir.DeadCode.opDef]))

theorem valid_renameInstr {base : Nat} {s : Rename} (valid : s.Valid base)
    (i : Silmaril.Compile.Mir.Instr) (bounds : ∀ reg ∈ defs i, reg < base) :
    ((renameInstr i).run s).2.Valid base := by
  cases i with
  | op o => exact valid_renameOp valid o bounds
  | fop op dest a b => exact valid_define valid dest (bounds dest (by simp [defs]))
  | addr dest symbol offset => exact valid_define valid dest (bounds dest (by simp [defs]))
  | call symbol args results =>
    rw [renameInstr_call_run]
    exact valid_defineResults valid results bounds
  | callIndirect reg args results =>
    rw [renameInstr_indirect_run]
    exact valid_defineResults valid results bounds

theorem defined_renameOp {s : Rename} {source source' : Lir.Frame Nat}
    {memory memory' : Lir.Memory} {o : Lir.Op Nat} (defined : s.Defined source)
    (exec : o.exec source memory = some (source', memory')) :
    ((renameOp o).run s).2.Defined source' := by
  cases o with
  | const dest value =>
    show ((renameOp (.const dest value)).run s).2.Defined source'
    have result : source.set dest value = source' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.some.injEq, Prod.mk.injEq] using exec
    obtain ⟨hframe, hmem⟩ := result
    rw [← hframe]
    exact defined_define defined dest value
  | move dest src =>
    show ((renameOp (.move dest src)).run s).2.Defined source'
    have result : ∃ value, source.get src = some value ∧ source.set dest value = source' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using exec
    obtain ⟨value, _, hframe, hmem⟩ := result
    rw [← hframe]
    exact defined_define defined dest value
  | unary op dest src =>
    show ((renameOp (.unary op dest src)).run s).2.Defined source'
    have result : ∃ value, source.get src = some value ∧
        source.set dest (op.eval value) = source' ∧
        memory = memory' := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using exec
    obtain ⟨value, _, hframe, hmem⟩ := result
    rw [← hframe]
    exact defined_define defined dest (op.eval value)
  | binary op dest a b =>
    show ((renameOp (.binary op dest a b)).run s).2.Defined source'
    have result : ∃ x, source.get a = some x ∧
        ∃ y, source.get b = some y ∧
        ∃ value, op.eval x y = some value ∧
        source.set dest value = source' ∧
        memory = memory' := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using exec
    obtain ⟨x, _, y, _, value, _, hframe, hmem⟩ := result
    rw [← hframe]
    exact defined_define defined dest value
  | load width ext dest baseReg offset =>
    show ((renameOp (.load width ext dest baseReg offset)).run s).2.Defined source'
    have result : ∃ address, source.get baseReg = some address ∧
        ∃ value, memory.load width ext (address.toNat + offset) = some value ∧
        source.set dest value = source' ∧
        memory = memory' := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using exec
    obtain ⟨address, _, value, _, hframe, hmem⟩ := result
    rw [← hframe]
    exact defined_define defined dest value
  | store width baseReg offset src =>
    show ((renameOp (.store width baseReg offset src)).run s).2.Defined source'
    have result : ∃ address, source.get baseReg = some address ∧
        ∃ value, source.get src = some value ∧
        ∃ mem, memory.store width (address.toNat + offset) value = some mem ∧
        source = source' ∧
        mem = memory' := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using exec
    obtain ⟨address, _, value, _, mem, _, hframe, hmem⟩ := result
    rw [← hframe]
    exact defined
  | slotGet dest index =>
    show ((renameOp (.slotGet dest index)).run s).2.Defined source'
    have result : ∃ value, source.slots index = some value ∧ source.set dest value = source' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using exec
    obtain ⟨value, _, hframe, hmem⟩ := result
    rw [← hframe]
    exact defined_define defined dest value
  | slotSet index src =>
    show ((renameOp (.slotSet index src)).run s).2.Defined source'
    have result : ∃ value, source.get src = some value ∧ source.setSlot index value = source' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using exec
    obtain ⟨value, _, hframe, hmem⟩ := result
    rw [← hframe]
    exact defined

theorem definedResults_writeAll {s : Rename} {source source' : Lir.Frame Nat}
    (defined : s.Defined source) (regs : List Nat) (values : List Lir.Word)
    (written : source.writeAll (regs.map .reg) values = some source') :
    ((regs.mapM define).run s).2.Defined source' := by
  induction regs generalizing s source values with
  | nil =>
    cases values with
    | nil => cases written; exact defined
    | cons value rest => cases written
  | cons reg regs ih =>
    cases values with
    | nil => cases written
    | cons value values =>
      rw [defineResults_cons]
      exact ih (defined_define defined reg value) values written

theorem defined_renameInstr {s : Rename} {source source' : Lir.Frame Nat}
    {memory memory' : Lir.Memory} {calls : OpenCalls} {i : Silmaril.Compile.Mir.Instr}
    (defined : s.Defined source) (exec : InstructionExec calls i source memory source' memory') :
    ((renameInstr i).run s).2.Defined source' := by
  cases exec with
  | op he => exact defined_renameOp defined he
  | fop he =>
    simp only [Lir.FOp.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
    obtain ⟨_, _, _, _, rfl⟩ := he
    exact defined_define defined _ _
  | addr _ => exact defined_define defined _ _
  | call _ _ hw =>
    rw [renameInstr_call_run]
    exact definedResults_writeAll defined _ _ hw
  | indirect _ _ _ hw =>
    rw [renameInstr_indirect_run]
    exact definedResults_writeAll defined _ _ hw

theorem renameInstrs_valid_defined {base : Nat} {s : Rename} {source source' : Lir.Frame Nat}
    {calls : OpenCalls} {memory memory' : Lir.Memory} {instrs : List Silmaril.Compile.Mir.Instr}
    (valid : s.Valid base) (defined : s.Defined source)
    (bounds : ∀ i ∈ instrs, ∀ reg ∈ defs i, reg < base)
    (exec : InstructionsExec calls instrs source memory source' memory') :
    ((instrs.mapM renameInstr).run s).2.Valid base ∧
      ((instrs.mapM renameInstr).run s).2.Defined source' := by
  induction exec generalizing s with
  | nil => exact ⟨valid, defined⟩
  | @cons i rest source memory middle middleMem source' memory' hi hrest ih =>
    have hv := valid_renameInstr valid i (bounds i (by simp))
    have hd := defined_renameInstr defined hi
    rw [renameInstrs_cons]
    exact ih hv hd (fun i hi => bounds i (by simp [hi]))


theorem read_eq_self_of_notmem (s : Rename) (reg : Nat)
    (h : reg ∉ s.versions.map (·.1)) : s.read reg = reg := by
  unfold Rename.read
  cases hf : s.versions.find? (·.1 == reg) with
  | none => rfl
  | some p =>
    have hm := List.mem_of_find?_eq_some hf
    have hfound := List.find?_some hf
    have he : p.1 = reg := by simpa only [beq_iff_eq] using hfound
    exact False.elim (h (List.mem_map.mpr ⟨p, hm, he⟩))

theorem current_not_origin {base : Nat} {s : Rename} (valid : s.Valid base)
    (reg : Nat) : s.read reg ∉ s.versions.map (·.1) := by
  by_cases hr : reg ∈ s.versions.map (·.1)
  · obtain ⟨p, hp, hpr⟩ := List.mem_map.mp hr
    have hv := valid.2 p hp
    intro hmem
    obtain ⟨q, hq, hqr⟩ := List.mem_map.mp hmem
    have hqbound := (valid.2 q hq).1
    rw [← hpr, hv.2.2] at hqr
    omega
  · rw [read_eq_self_of_notmem s reg hr]
    exact hr

theorem commit_exit {base : Nat} {s : Rename} {source target : Lir.Frame Nat}
    {calls : OpenCalls} {memory : Lir.Memory}
    (valid : s.Valid base) (defined : s.Defined source) (agree : s.Agrees base source target) :
    ∃ target', InstructionsExec calls (commitInstrs s.versions) target memory target' memory ∧
      s.Agrees base source target' ∧ source.slots = target'.slots ∧
      (∀ reg, reg < base → target'.get reg = source.get reg) := by
  have hvalues : ∀ p ∈ s.versions, ∃ w,
      target.get p.2 = some w ∧ source.get p.1 = some w := by
    intro p hp
    obtain ⟨w, hw⟩ := defined p hp
    have hv : p.1 < base ∧ base ≤ p.2 ∧ s.read p.1 = p.2 := valid.2 p hp
    have hread : target.get p.2 = source.get p.1 := by
      simpa only [hv.2.2] using agree.2 p.1 hv.1
    exact ⟨w, hread.trans hw, hw⟩
  obtain ⟨target', hrun, hslots, hwritten, huntouched⟩ := commitInstrs_exec s.versions
    (fun p hp => ⟨(valid.2 p hp).1, (valid.2 p hp).2.1⟩) hvalues
  have hslots' : source.slots = target'.slots := agree.1.trans hslots.symm
  refine ⟨target', hrun, ⟨hslots', ?_⟩, hslots', ?_⟩
  · intro reg hr
    rw [huntouched _ (current_not_origin valid reg)]
    exact agree.2 reg hr
  · intro reg hr
    by_cases hmem : reg ∈ s.versions.map (·.1)
    · exact hwritten reg hmem
    · rw [huntouched reg hmem]
      simpa only [read_eq_self_of_notmem s reg hmem] using agree.2 reg hr

theorem readAll_renameLoc {base : Nat} {s : Rename} {source target : Lir.Frame Nat}
    (agree : s.Agrees base source target) (locs : List (Lir.Loc Nat))
    (bounds : ∀ reg, .reg reg ∈ locs → reg < base) :
    target.readAll (locs.map (renameLoc s)) = source.readAll locs := by
  induction locs with
  | nil => rfl
  | cons loc rest ih =>
    have hhead : target.read (renameLoc s loc) = source.read loc := by
      cases loc with
      | reg reg => exact agree.2 reg (bounds reg (by simp))
      | slot index => exact congrFun agree.1.symm index
    have htail := ih (fun r hr => bounds r (by simp [hr]))
    simp only [Lir.Frame.readAll, List.map_cons, List.mapM_cons] at *
    rw [hhead, htail]

theorem renameTerm_exec {base : Nat} {s : Rename} {source target : Lir.Frame Nat}
    {term : Lir.Term Nat} {exit : BlockExit} (agree : s.Agrees base source target)
    (bounds : ∀ reg ∈ Silmaril.Compile.Mir.DeadCode.termUses term, reg < base)
    (exec : TermExec term source exit) : TermExec (renameTerm s term) target exit := by
  cases exec with
  | jump => exact .jump
  | zero hz =>
    apply TermExec.zero
    rw [agree.2 _ (bounds _ (by simp [Silmaril.Compile.Mir.DeadCode.termUses]))]
    exact hz
  | nonzero hv hn =>
    refine .nonzero ?_ hn
    rw [agree.2 _ (bounds _ (by simp [Silmaril.Compile.Mir.DeadCode.termUses]))]
    exact hv
  | @ret locs source values hr =>
    apply TermExec.ret
    rw [readAll_renameLoc agree locs]
    · exact hr
    · intro reg hreg
      apply bounds reg
      simp only [Silmaril.Compile.Mir.DeadCode.termUses]
      exact List.mem_filterMap.mpr ⟨.reg reg, hreg, rfl⟩
  | trap => exact .trap

theorem InstructionsExec.append {calls : OpenCalls}
    {first second : List Silmaril.Compile.Mir.Instr}
    {source middle target : Lir.Frame Nat} {memory middleMem memory' : Lir.Memory}
    (hfirst : InstructionsExec calls first source memory middle middleMem)
    (hsecond : InstructionsExec calls second middle middleMem target memory') :
    InstructionsExec calls (first ++ second) source memory target memory' := by
  induction hfirst with
  | nil => exact hsecond
  | cons hi _ ih => exact .cons hi (ih hsecond)

/-- The complete local SSA entry/exit round trip preserves every finite
successful open-block execution, its memory, control-flow exit, slots and all
original registers below the supplied fresh-name bound. Calls may have arbitrary
relational summaries. This is a forward simulation; it does not yet establish
backward refinement, divergence preservation or whole-program MirSem validity. -/
theorem leave_enter_exec {base : Nat} {source source' : Lir.Frame Nat}
    {calls : OpenCalls} {memory memory' : Lir.Memory} {b : Silmaril.Compile.Mir.Block}
    {exit : BlockExit}
    (huses : ∀ i ∈ b.instrs.toList, ∀ reg ∈ uses i, reg < base)
    (hdefs : ∀ i ∈ b.instrs.toList, ∀ reg ∈ defs i, reg < base)
    (hterm : ∀ reg ∈ Silmaril.Compile.Mir.DeadCode.termUses b.term, reg < base)
    (exec : BlockExec calls b source memory exit source' memory') :
    ∃ target', BlockExec calls (leave (enter base b)) source memory exit target' memory' ∧
      source'.slots = target'.slots ∧
      (∀ reg, reg < base → target'.get reg = source'.get reg) := by
  have agree : Rename.Agrees base {next := base} source source := ⟨rfl, fun _ _ => rfl⟩
  obtain ⟨bodyTarget, hbody, _, hbodyAgree⟩ :=
    renameInstrs_exec (bounded_initial base) agree huses exec.1
  obtain ⟨hvalid, hdefined⟩ := renameInstrs_valid_defined
    (valid_initial base) (defined_initial base source) hdefs exec.1
  obtain ⟨target', hcommits, hfinalAgree, hslots, hregs⟩ :=
    commit_exit hvalid hdefined hbodyAgree
  refine ⟨target', ⟨?_, ?_⟩, hslots, hregs⟩
  · have combined := hbody.append hcommits
    simpa only [leave, enter, renameArray_run, Array.toList_append, Array.toList_map,
      List.toList_toArray, commitInstrs] using combined
  · have term := renameTerm_exec hfinalAgree hterm exec.2
    simpa only [leave, enter, renameArray_run] using term


theorem renameOp_exec_back {base : Nat} {s : Rename} {source target target' : Lir.Frame Nat}
    {memory memory' : Lir.Memory} {o : Lir.Op Nat}
    (bounded : s.Bounded base) (agree : s.Agrees base source target)
    (huses : ∀ reg ∈ Silmaril.Compile.Mir.DeadCode.opUses o, reg < base)
    (exec : ((renameOp o).run s).1.exec target memory = some (target', memory')) :
    ∃ source', o.exec source memory = some (source', memory') ∧
      ((renameOp o).run s).2.Bounded base ∧
      ((renameOp o).run s).2.Agrees base source' target' := by
  cases o with
  | const dest value =>
    show ∃ source', (.const dest value : Lir.Op Nat).exec source memory = some (source', memory') ∧
      ((renameOp (.const dest value)).run s).2.Bounded base ∧
      ((renameOp (.const dest value)).run s).2.Agrees base source' target'
    have execution : some (target.set s.next value, memory) = some (target', memory') := exec
    have result : target.set s.next value = target' ∧ memory = memory' := by
      simpa only [Option.some.injEq, Prod.mk.injEq] using execution
    obtain ⟨hframe, hmem⟩ := result
    rw [← hframe, ← hmem]
    exact ⟨_, rfl, bounded_define bounded dest, agrees_define bounded agree dest value⟩
  | move dest src =>
    show ∃ source', (.move dest src : Lir.Op Nat).exec source memory = some (source', memory') ∧
      ((renameOp (.move dest src)).run s).2.Bounded base ∧
      ((renameOp (.move dest src)).run s).2.Agrees base source' target'
    have execution : (target.get (s.read src)).map (fun v => (target.set s.next v, memory)) = some (target', memory') := exec
    have result : ∃ value, target.get (s.read src) = some value ∧
        target.set s.next value = target' ∧
        memory = memory' := by
      simpa only [Option.map_eq_some_iff, Prod.mk.injEq] using execution
    obtain ⟨value, hv, hframe, hmem⟩ := result
    rw [← hframe, ← hmem]
    have hs : source.get src = some value :=
      (agree.2 src (huses src (by simp [Silmaril.Compile.Mir.DeadCode.opUses]))).symm.trans hv
    exact ⟨_, by simp [Lir.Op.exec, hs], bounded_define bounded dest, agrees_define bounded agree dest value⟩
  | unary op dest src =>
    show ∃ source', (.unary op dest src : Lir.Op Nat).exec source memory = some (source', memory') ∧
      ((renameOp (.unary op dest src)).run s).2.Bounded base ∧
      ((renameOp (.unary op dest src)).run s).2.Agrees base source' target'
    have execution : (target.get (s.read src)).map (fun v => (target.set s.next (op.eval v), memory)) = some (target', memory') := exec
    have result : ∃ value, target.get (s.read src) = some value ∧
        target.set s.next (op.eval value) = target' ∧
        memory = memory' := by
      simpa only [Option.map_eq_some_iff, Prod.mk.injEq] using execution
    obtain ⟨value, hv, hframe, hmem⟩ := result
    rw [← hframe, ← hmem]
    have hs : source.get src = some value :=
      (agree.2 src (huses src (by simp [Silmaril.Compile.Mir.DeadCode.opUses]))).symm.trans hv
    exact ⟨_, by simp [Lir.Op.exec, hs], bounded_define bounded dest, agrees_define bounded agree dest (op.eval value)⟩
  | binary op dest a b =>
    show ∃ source', (.binary op dest a b : Lir.Op Nat).exec source memory = some (source', memory') ∧
      ((renameOp (.binary op dest a b)).run s).2.Bounded base ∧
      ((renameOp (.binary op dest a b)).run s).2.Agrees base source' target'
    have execution : (target.get (s.read a)).bind (fun x => (target.get (s.read b)).bind fun y => (op.eval x y).map fun v => (target.set s.next v, memory)) = some (target', memory') := exec
    have result : ∃ x, target.get (s.read a) = some x ∧
        ∃ y, target.get (s.read b) = some y ∧
        ∃ value, op.eval x y = some value ∧
        target.set s.next value = target' ∧
        memory = memory' := by
      simpa only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using execution
    obtain ⟨x, hx, y, hy, value, hv, hframe, hmem⟩ := result
    rw [← hframe, ← hmem]
    have ha : source.get a = some x :=
      (agree.2 a (huses a (by simp [Silmaril.Compile.Mir.DeadCode.opUses]))).symm.trans hx
    have hb : source.get b = some y :=
      (agree.2 b (huses b (by simp [Silmaril.Compile.Mir.DeadCode.opUses]))).symm.trans hy
    exact ⟨_, by simp [Lir.Op.exec, ha, hb, hv], bounded_define bounded dest, agrees_define bounded agree dest value⟩
  | load width ext dest baseReg offset =>
    show ∃ source', (.load width ext dest baseReg offset : Lir.Op Nat).exec source memory = some (source', memory') ∧
      ((renameOp (.load width ext dest baseReg offset)).run s).2.Bounded base ∧
      ((renameOp (.load width ext dest baseReg offset)).run s).2.Agrees base source' target'
    have execution : (target.get (s.read baseReg)).bind (fun a => (memory.load width ext (a.toNat + offset)).map fun v => (target.set s.next v, memory)) = some (target', memory') := exec
    have result : ∃ address, target.get (s.read baseReg) = some address ∧
        ∃ value, memory.load width ext (address.toNat + offset) = some value ∧
        target.set s.next value = target' ∧
        memory = memory' := by
      simpa only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using execution
    obtain ⟨address, ha, value, hv, hframe, hmem⟩ := result
    rw [← hframe, ← hmem]
    have hs : source.get baseReg = some address :=
      (agree.2 baseReg (huses baseReg (by simp [Silmaril.Compile.Mir.DeadCode.opUses]))).symm.trans ha
    exact ⟨_, by simp [Lir.Op.exec, hs, hv], bounded_define bounded dest, agrees_define bounded agree dest value⟩
  | store width baseReg offset src =>
    show ∃ source', (.store width baseReg offset src : Lir.Op Nat).exec source memory = some (source', memory') ∧
      ((renameOp (.store width baseReg offset src)).run s).2.Bounded base ∧
      ((renameOp (.store width baseReg offset src)).run s).2.Agrees base source' target'
    have execution : (target.get (s.read baseReg)).bind (fun a => (target.get (s.read src)).bind fun v => (memory.store width (a.toNat + offset) v).map fun m => (target, m)) = some (target', memory') := exec
    have result : ∃ address, target.get (s.read baseReg) = some address ∧
        ∃ value, target.get (s.read src) = some value ∧
        ∃ mem, memory.store width (address.toNat + offset) value = some mem ∧
        target = target' ∧
        mem = memory' := by
      simpa only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using execution
    obtain ⟨address, ha, value, hv, mem, hm, hframe, hmem⟩ := result
    rw [← hframe, ← hmem]
    have hs : source.get baseReg = some address :=
      (agree.2 baseReg (huses baseReg (by simp [Silmaril.Compile.Mir.DeadCode.opUses]))).symm.trans ha
    have hs' : source.get src = some value :=
      (agree.2 src (huses src (by simp [Silmaril.Compile.Mir.DeadCode.opUses]))).symm.trans hv
    exact ⟨_, by simp [Lir.Op.exec, hs, hs', hm], bounded, agree⟩
  | slotGet dest index =>
    show ∃ source', (.slotGet dest index : Lir.Op Nat).exec source memory = some (source', memory') ∧
      ((renameOp (.slotGet dest index)).run s).2.Bounded base ∧
      ((renameOp (.slotGet dest index)).run s).2.Agrees base source' target'
    have execution : (target.slots index).map (fun v => (target.set s.next v, memory)) = some (target', memory') := exec
    have result : ∃ value, target.slots index = some value ∧ target.set s.next value = target' ∧ memory = memory' := by
      simpa only [Option.map_eq_some_iff, Prod.mk.injEq] using execution
    obtain ⟨value, hv, hframe, hmem⟩ := result
    rw [← hframe, ← hmem]
    have hs : source.slots index = some value := (congrFun agree.1 index).trans hv
    exact ⟨_, by simp [Lir.Op.exec, hs], bounded_define bounded dest, agrees_define bounded agree dest value⟩
  | slotSet index src =>
    show ∃ source', (.slotSet index src : Lir.Op Nat).exec source memory = some (source', memory') ∧
      ((renameOp (.slotSet index src)).run s).2.Bounded base ∧
      ((renameOp (.slotSet index src)).run s).2.Agrees base source' target'
    have execution : (target.get (s.read src)).map (fun v => (target.setSlot index v, memory)) = some (target', memory') := exec
    have result : ∃ value, target.get (s.read src) = some value ∧
        target.setSlot index value = target' ∧
        memory = memory' := by
      simpa only [Option.map_eq_some_iff, Prod.mk.injEq] using execution
    obtain ⟨value, hv, hframe, hmem⟩ := result
    rw [← hframe, ← hmem]
    have hs : source.get src = some value :=
      (agree.2 src (huses src (by simp [Silmaril.Compile.Mir.DeadCode.opUses]))).symm.trans hv
    exact ⟨_, by simp [Lir.Op.exec, hs], bounded, agrees_slotSet agree index value⟩

theorem defineResults_writeAll_back {base : Nat} {s : Rename}
    {source target target' : Lir.Frame Nat} (bounded : s.Bounded base)
    (agree : s.Agrees base source target) (regs : List Nat) (values : List Lir.Word)
    (written : target.writeAll (((regs.mapM define).run s).1.map .reg) values = some target') :
    ∃ source', source.writeAll (regs.map .reg) values = some source' ∧
      ((regs.mapM define).run s).2.Bounded base ∧
      ((regs.mapM define).run s).2.Agrees base source' target' := by
  induction regs generalizing s source target values with
  | nil =>
    cases values with
    | nil => cases written; exact ⟨source, rfl, bounded, agree⟩
    | cons value rest => cases written
  | cons reg regs ih =>
    rw [defineResults_cons] at written ⊢
    cases values with
    | nil => cases written
    | cons value values =>
      obtain ⟨source', hw, hb, ha⟩ := ih (bounded_define bounded reg)
        (agrees_define bounded agree reg value) values written
      exact ⟨source', hw, hb, ha⟩

theorem renameInstr_exec_back {base : Nat} {s : Rename} {source target target' : Lir.Frame Nat}
    {calls : OpenCalls} {memory memory' : Lir.Memory} {i : Silmaril.Compile.Mir.Instr}
    (bounded : s.Bounded base) (agree : s.Agrees base source target)
    (huses : ∀ reg ∈ uses i, reg < base)
    (exec : InstructionExec calls ((renameInstr i).run s).1 target memory target' memory') :
    ∃ source', InstructionExec calls i source memory source' memory' ∧
      ((renameInstr i).run s).2.Bounded base ∧
      ((renameInstr i).run s).2.Agrees base source' target' := by
  cases i with
  | op o =>
    cases exec with
    | op he =>
      obtain ⟨source', he', hb, ha⟩ := renameOp_exec_back bounded agree huses he
      exact ⟨source', .op he', hb, ha⟩
  | fop op dest a b =>
    show ∃ source', InstructionExec calls (.fop op dest a b) source memory source' memory' ∧
        ((renameInstr (.fop op dest a b)).run s).2.Bounded base ∧
        ((renameInstr (.fop op dest a b)).run s).2.Agrees base source' target'
    cases exec with
    | fop he =>
      show ∃ source', InstructionExec calls (.fop op dest a b) source memory source' memory ∧
        ((renameInstr (.fop op dest a b)).run s).2.Bounded base ∧
        ((renameInstr (.fop op dest a b)).run s).2.Agrees base source' target'
      have execution : (target.get (s.read a)).bind
          (fun x => (target.get (s.read b)).map fun y => target.set s.next (op.eval x y)) =
          some target' := he
      have result : ∃ x, target.get (s.read a) = some x ∧ ∃ y,
          target.get (s.read b) = some y ∧ target.set s.next (op.eval x y) = target' := by
        simpa only [Option.bind_eq_some_iff, Option.map_eq_some_iff] using execution
      obtain ⟨x, hx, y, hy, hframe⟩ := result
      rw [← hframe]
      have ha : source.get a = some x := (agree.2 a (huses a (by simp [uses]))).symm.trans hx
      have hb : source.get b = some y := (agree.2 b (huses b (by simp [uses]))).symm.trans hy
      exact ⟨_, .fop (by simp [Lir.FOp.exec, ha, hb]), bounded_define bounded dest,
        agrees_define bounded agree dest (op.eval x y)⟩
  | addr dest symbol offset =>
    cases exec with
    | addr he => exact ⟨_, .addr he, bounded_define bounded dest, agrees_define bounded agree dest _⟩
  | call symbol args results =>
    show ∃ source', InstructionExec calls (.call symbol args results) source memory source' memory' ∧
        ((renameInstr (.call symbol args results)).run s).2.Bounded base ∧
        ((renameInstr (.call symbol args results)).run s).2.Agrees base source' target'
    have execution : InstructionExec calls
        (.call symbol (args.map s.read) ((results.mapM define).run s).1)
        target memory target' memory' := by
      simpa only [renameInstr_call_run] using exec
    rw [renameInstr_call_run]
    cases execution with
    | call hargs hcall hw =>
      obtain ⟨source', hwrite, hb, ha⟩ := defineResults_writeAll_back bounded agree results _ hw
      refine ⟨source', .call ?_ hcall hwrite, hb, ha⟩
      have hr : target.readAll (args.map (fun r => .reg (s.read r))) =
          source.readAll (args.map .reg) := readAll_renamed agree args huses
      exact hr.symm.trans (by simpa only [List.map_map, Function.comp_def] using hargs)
  | callIndirect reg args results =>
    show ∃ source', InstructionExec calls (.callIndirect reg args results) source memory source' memory' ∧
        ((renameInstr (.callIndirect reg args results)).run s).2.Bounded base ∧
        ((renameInstr (.callIndirect reg args results)).run s).2.Agrees base source' target'
    have execution : InstructionExec calls
        (.callIndirect (s.read reg) (args.map s.read) ((results.mapM define).run s).1)
        target memory target' memory' := by
      simpa only [renameInstr_indirect_run] using exec
    rw [renameInstr_indirect_run]
    cases execution with
    | indirect htarget hargs hcall hw =>
      show ∃ source', InstructionExec calls (.callIndirect reg args results) source memory source' memory' ∧
        ((renameInstr (.callIndirect reg args results)).run s).2.Bounded base ∧
        ((renameInstr (.callIndirect reg args results)).run s).2.Agrees base source' target'
      obtain ⟨source', hwrite, hb, ha⟩ := defineResults_writeAll_back bounded agree results _ hw
      refine ⟨source', .indirect ?_ ?_ hcall hwrite, hb, ha⟩
      · exact (agree.2 reg (huses reg (by simp [uses]))).symm.trans htarget
      · have hr : target.readAll (args.map (fun r => .reg (s.read r))) =
            source.readAll (args.map .reg) :=
          readAll_renamed agree args (fun r hr => huses r (by simp [uses, hr]))
        exact hr.symm.trans (by simpa only [List.map_map, Function.comp_def] using hargs)

theorem renameInstrs_exec_back {base : Nat} {s : Rename} {source target target' : Lir.Frame Nat}
    {calls : OpenCalls} {memory memory' : Lir.Memory} (instrs : List Silmaril.Compile.Mir.Instr)
    (bounded : s.Bounded base) (agree : s.Agrees base source target)
    (huses : ∀ i ∈ instrs, ∀ reg ∈ uses i, reg < base)
    (exec : InstructionsExec calls ((instrs.mapM renameInstr).run s).1
      target memory target' memory') :
    ∃ source', InstructionsExec calls instrs source memory source' memory' ∧
      ((instrs.mapM renameInstr).run s).2.Bounded base ∧
      ((instrs.mapM renameInstr).run s).2.Agrees base source' target' := by
  induction instrs generalizing s source target memory with
  | nil => cases exec; exact ⟨source, .nil, bounded, agree⟩
  | cons i rest ih =>
    rw [renameInstrs_cons] at exec ⊢
    cases exec with
    | cons hi hrest =>
      obtain ⟨source₁, hi', hb, ha⟩ := renameInstr_exec_back bounded agree (huses i (by simp)) hi
      obtain ⟨source₂, hrest', hb', ha'⟩ := ih hb ha
        (fun i hi => huses i (by simp [hi])) hrest
      exact ⟨source₂, .cons hi' hrest', hb', ha'⟩


theorem renameTerm_exec_back {base : Nat} {s : Rename} {source target : Lir.Frame Nat}
    {term : Lir.Term Nat} {exit : BlockExit} (agree : s.Agrees base source target)
    (bounds : ∀ reg ∈ Silmaril.Compile.Mir.DeadCode.termUses term, reg < base)
    (exec : TermExec (renameTerm s term) target exit) : TermExec term source exit := by
  cases term with
  | jump label => cases exec; exact .jump
  | trap => cases exec; exact .trap
  | branch reg yes no =>
    cases exec with
    | zero hz =>
      exact .zero ((agree.2 reg (bounds reg
        (by simp [Silmaril.Compile.Mir.DeadCode.termUses]))).symm.trans hz)
    | nonzero hv hn =>
      exact .nonzero ((agree.2 reg (bounds reg
        (by simp [Silmaril.Compile.Mir.DeadCode.termUses]))).symm.trans hv) hn
  | ret locs =>
    cases exec with
    | ret hr =>
      apply TermExec.ret
      have hread := readAll_renameLoc agree locs (fun reg hreg => bounds reg
        (List.mem_filterMap.mpr ⟨.reg reg, hreg, rfl⟩))
      exact hread.symm.trans hr

theorem InstructionsExec.append_inv {calls : OpenCalls}
    (first second : List Silmaril.Compile.Mir.Instr)
    {source target : Lir.Frame Nat} {memory memory' : Lir.Memory}
    (exec : InstructionsExec calls (first ++ second) source memory target memory') :
    ∃ middle middleMem, InstructionsExec calls first source memory middle middleMem ∧
      InstructionsExec calls second middle middleMem target memory' := by
  induction first generalizing source memory with
  | nil => exact ⟨source, memory, .nil, exec⟩
  | cons i rest ih =>
    cases exec with
    | cons hi hrest =>
      obtain ⟨middle, middleMem, hfirst, hsecond⟩ := ih hrest
      exact ⟨middle, middleMem, .cons hi hfirst, hsecond⟩

theorem commitInstrs_unique {calls : OpenCalls} (versions : List (Nat × Nat))
    {source first second : Lir.Frame Nat} {memory firstMem secondMem : Lir.Memory}
    (hfirst : InstructionsExec calls (commitInstrs versions) source memory first firstMem)
    (hsecond : InstructionsExec calls (commitInstrs versions) source memory second secondMem) :
    first = second ∧ firstMem = secondMem := by
  induction versions generalizing source memory with
  | nil => cases hfirst; cases hsecond; exact ⟨rfl, rfl⟩
  | cons p rest ih =>
    cases hfirst with
    | cons hi hrest =>
      cases hsecond with
      | cons hi' hrest' =>
        cases hi with
        | op he =>
          cases hi' with
          | op he' =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (he.symm.trans he'))
            exact ih hrest hrest'

/-- Backward simulation of the actual local SSA round trip, including the
boundary copies. Every successful transformed block execution has a source
execution with identical exit, memory, slots and original registers. -/
theorem leave_enter_exec_back {base : Nat} {source target' : Lir.Frame Nat}
    {calls : OpenCalls} {memory memory' : Lir.Memory} {b : Silmaril.Compile.Mir.Block}
    {exit : BlockExit}
    (huses : ∀ i ∈ b.instrs.toList, ∀ reg ∈ uses i, reg < base)
    (hdefs : ∀ i ∈ b.instrs.toList, ∀ reg ∈ defs i, reg < base)
    (hterm : ∀ reg ∈ Silmaril.Compile.Mir.DeadCode.termUses b.term, reg < base)
    (exec : BlockExec calls (leave (enter base b)) source memory exit target' memory') :
    ∃ source', BlockExec calls b source memory exit source' memory' ∧
      source'.slots = target'.slots ∧
      (∀ reg, reg < base → target'.get reg = source'.get reg) := by
  have ht : InstructionsExec calls
      (((b.instrs.toList.mapM renameInstr).run {next := base}).1 ++
        commitInstrs ((b.instrs.toList.mapM renameInstr).run {next := base}).2.versions)
      source memory target' memory' := by
    simpa only [leave, enter, renameArray_run, Array.toList_append, Array.toList_map,
      List.toList_toArray, commitInstrs] using exec.1
  obtain ⟨bodyTarget, bodyMem, hbody, hcommits⟩ := InstructionsExec.append_inv _ _ ht
  have agree : Rename.Agrees base {next := base} source source := ⟨rfl, fun _ _ => rfl⟩
  obtain ⟨source', hsource, _, hbodyAgree⟩ :=
    renameInstrs_exec_back b.instrs.toList (bounded_initial base) agree huses hbody
  obtain ⟨hvalid, hdefined⟩ := renameInstrs_valid_defined
    (valid_initial base) (defined_initial base source) hdefs hsource
  obtain ⟨predicted, hpredict, hfinalAgree, hslots, hregs⟩ :=
    commit_exit hvalid hdefined hbodyAgree
  obtain ⟨rfl, rfl⟩ := commitInstrs_unique _ hcommits hpredict
  refine ⟨source', ⟨hsource, ?_⟩, hslots, hregs⟩
  apply renameTerm_exec_back hfinalAgree hterm
  simpa only [leave, enter, renameArray_run] using exec.2

/-- Finite open-block observations and final memory coincide exactly before
and after the SSA entry/exit round trip, under arbitrary symbolic call summaries.
This theorem covers the renaming round trip; it does not include the lambda-SSA
arithmetic optimizer, whole-program linking, divergence or native code emission. -/
theorem leave_enter_observations_iff {base : Nat} {source : Lir.Frame Nat}
    {calls : OpenCalls} {memory memory' : Lir.Memory} {b : Silmaril.Compile.Mir.Block}
    {exit : BlockExit}
    (huses : ∀ i ∈ b.instrs.toList, ∀ reg ∈ uses i, reg < base)
    (hdefs : ∀ i ∈ b.instrs.toList, ∀ reg ∈ defs i, reg < base)
    (hterm : ∀ reg ∈ Silmaril.Compile.Mir.DeadCode.termUses b.term, reg < base) :
    (∃ final, BlockExec calls (leave (enter base b)) source memory exit final memory') ↔
      (∃ final, BlockExec calls b source memory exit final memory') := by
  constructor
  · rintro ⟨final, hrun⟩
    obtain ⟨source', hsource, _, _⟩ := leave_enter_exec_back huses hdefs hterm hrun
    exact ⟨source', hsource⟩
  · rintro ⟨final, hrun⟩
    obtain ⟨target', htarget, _, _⟩ := leave_enter_exec huses hdefs hterm hrun
    exact ⟨target', htarget⟩

end Silmaril.Compiler.Native.Optimize
