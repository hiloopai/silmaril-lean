module

public import Silmaril.Compiler.Target.RegAlloc.Defs
public import Silmaril.Machine.CBackend.Lir.Behaviour.Defs
/-! # Correctness of register renaming under a liveness certificate

`RegAlloc.renumber` renames the virtual registers of each function by a map `σ` chosen
from live intervals. This file proves the key semantic lemma behind it: a per-function
renaming that never merges two registers that are live at the same point (nor a register
being written with one live after the write) preserves every non-stuck behaviour.

The liveness information is a *certificate*, `live : Point → Set Nat` (the registers live
before each point; the terminator of a block is at index `instrs.length`), checked by the
standard backward-dataflow inequalities rather than computed as a fixpoint
(`LiveCert`):

* an instruction's uses are live before it, and every register live after it that it does
  not define is live before it;
* a terminator's uses are live before it, and the registers live at the head of every
  successor are live before it;
* interference-freedom: a register live after an instruction (or defined by it) that is
  renamed to the same number as a register the instruction defines is that register;
* the register parameters of every function are renamed injectively.

No injectivity of `σ` on whole live sets is required: it follows for the registers that
hold values. The simulation relation (`FrameRel`) only transports the *defined* live
registers (`some w → some w`), because reading an unwritten register is stuck in Lir.

`renameProg σ p` renames every function `f` by `σ f` without deleting the self-moves that
renaming can create. `rename_behaves` is the analogue of `Lir.Alloc.spill_behaves` and
`rename_refines` the analogue of `Lir.Alloc.spill_refines`.

`dropProg D q` then deletes instructions that are self-moves (`DropsSelfMoves D`);
`drop_behaves` shows that this preserves non-stuck behaviours. `renumber_eq` identifies
`RegAlloc.renumber k p` with renaming by `renumberσ k p` followed by such a deletion, so
`renumber_behaves` and `renumber_refines` prove `renumber` correct for every program and
`k` for which some liveness certificate makes `renumberσ k p` interference-free. Producing
that certificate from `liveness` and `assign` (by proof or by a checker) is not done here.
-/

@[expose] public section

namespace Silmaril.Compile.Target.RegAlloc

open Silmaril.Machine Silmaril.Machine.Lir Relation

/-! ## Renaming without dropping moves -/

def renameInstrND (σ : Nat → Nat) : Instr Nat → Instr Nat
  | .op o => .op (renameOp σ o)
  | .call f args res => .call f (args.map (renameLoc σ)) (res.map (renameLoc σ))
  | .fop op d x y => .fop op (σ d) (σ x) (σ y)

def renameBlockND (σ : Nat → Nat) (b : Block Nat) : Block Nat :=
  ⟨b.instrs.map (renameInstrND σ), renameTerm σ b.term⟩

def renameFuncND (σ : Nat → Nat) (fn : Func Nat) : Func Nat where
  params := fn.params.map (renameLoc σ)
  entry := fn.entry
  blocks := fn.blocks.map (renameBlockND σ)

/-- Rename function `f` of `p` by `σ f`, keeping every instruction. -/
def renameProg (σ : FuncId → Nat → Nat) (p : Prog Nat) : Prog Nat :=
  ⟨p.funcs.mapIdx fun f fn => renameFuncND (σ f) fn⟩

def renameCode (σ : Nat → Nat) : Code Nat → Code Nat
  | .instr i => .instr (renameInstrND σ i)
  | .term t => .term (renameTerm σ t)

theorem renameProg_func? (σ : FuncId → Nat → Nat) (p : Prog Nat) (f : FuncId) :
    (renameProg σ p).func? f = (p.func? f).map (renameFuncND (σ f)) := by
  simp [renameProg, Prog.func?]

theorem renameProg_fetch (σ : FuncId → Nat → Nat) (p : Prog Nat) (pt : Point) :
    (renameProg σ p).fetch pt = (p.fetch pt).map (renameCode (σ pt.func)) := by
  unfold Prog.fetch Prog.block?
  rw [renameProg_func?]
  cases p.func? pt.func with
  | none => rfl
  | some fn =>
    simp only [Option.map_some, Option.bind_some, renameFuncND, List.getElem?_map]
    cases fn.blocks[pt.label]? with
    | none => rfl
    | some b =>
      simp only [Option.map_some, Option.bind_some, renameBlockND, List.getElem?_map,
        List.length_map]
      cases b.instrs[pt.index]? with
      | some i => simp [renameCode]
      | none => simp only [Option.map_none]; split <;> simp [renameCode]

theorem mem_locRegs {v : Nat} {ls : List (Loc Nat)} : v ∈ locRegs ls ↔ Loc.reg v ∈ ls := by
  unfold locRegs
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨l, hl, e⟩
    cases l <;> simp_all
  · intro h
    exact ⟨_, h, rfl⟩

/-! ## The frame relation -/

/-- Every defined register of `L` is found at its new name, and the slots agree. -/
def FrameRel (σ : Nat → Nat) (L : Set Nat) (fs ft : Frame Nat) : Prop :=
  (∀ v ∈ L, ∀ w, fs.regs v = some w → ft.regs (σ v) = some w) ∧ ft.slots = fs.slots

variable {σ : Nat → Nat}

theorem FrameRel.mono {L L' : Set Nat} {fs ft : Frame Nat} (h : FrameRel σ L fs ft)
    (hs : L' ⊆ L) : FrameRel σ L' fs ft :=
  ⟨fun v hv => h.1 v (hs hv), h.2⟩

theorem FrameRel.get {L : Set Nat} {fs ft : Frame Nat} (h : FrameRel σ L fs ft) {u : Nat}
    (hu : u ∈ L) {x : Word} (hx : fs.get u = some x) : ft.get (σ u) = some x :=
  h.1 u hu x hx

/-- Writing a register `d` that does not share its new name with another register of `A`. -/
theorem FrameRel.set {A : Set Nat} {fs ft : Frame Nat} (h : FrameRel σ A fs ft) (d : Nat)
    (z : Word) (hd : ∀ v ∈ A, σ v = σ d → v = d) :
    FrameRel σ (insert d A) (fs.set d z) (ft.set (σ d) z) := by
  refine ⟨fun v hv w hw => ?_, by simp [h.2]⟩
  by_cases e : v = d
  · subst e; simpa using hw
  · have hv' : v ∈ A := (Set.mem_insert_iff.mp hv).resolve_left e
    have ne : σ v ≠ σ d := fun h' => e (hd v hv' h')
    simp only [Frame.regs_set, e, ne, ite_false] at hw ⊢
    exact h.1 v hv' w hw

/-- The form used for an operation defining `d`: live-after registers other than `d` were
live before, and none of them shares `d`'s new name. -/
theorem FrameRel.dest {L L' : Set Nat} {fs ft : Frame Nat} (h : FrameRel σ L fs ft) {d : Nat}
    (hlive : ∀ v ∈ L', v ≠ d → v ∈ L) (hint : ∀ v ∈ L', σ v = σ d → v = d) (z : Word) :
    FrameRel σ L' (fs.set d z) (ft.set (σ d) z) := by
  have h₁ : FrameRel σ {v | v ∈ L' ∧ v ≠ d} fs ft := h.mono fun v hv => hlive v hv.1 hv.2
  refine (h₁.set d z fun v hv => hint v hv.1).mono fun v hv => ?_
  by_cases e : v = d
  · exact Set.mem_insert_iff.mpr (.inl e)
  · exact Set.mem_insert_iff.mpr (.inr ⟨hv, e⟩)

theorem FrameRel.setSlot {L L' : Set Nat} {fs ft : Frame Nat} (h : FrameRel σ L fs ft)
    (hs : L' ⊆ L) (n : Nat) (x : Word) : FrameRel σ L' (fs.setSlot n x) (ft.setSlot n x) := by
  refine ⟨fun v hv w hw => h.1 v (hs hv) w hw, ?_⟩
  funext n'
  simp [h.2]

theorem FrameRel.readAll {L : Set Nat} {fs ft : Frame Nat} (h : FrameRel σ L fs ft) :
    ∀ {locs : List (Loc Nat)} {vals : List Word}, (∀ v, Loc.reg v ∈ locs → v ∈ L) →
      fs.readAll locs = some vals → ft.readAll (locs.map (renameLoc σ)) = some vals
  | [], vals, _, hr => by simpa [Frame.readAll] using hr
  | l :: ls, vals, hu, hr => by
    simp only [Frame.readAll, List.mapM_cons] at hr ⊢
    cases hl : fs.read l with
    | none => simp [hl] at hr
    | some x =>
      cases hls : ls.mapM fs.read with
      | none => simp [hl, hls] at hr
      | some xs =>
        have := FrameRel.readAll h (locs := ls) (fun v hv => hu v (List.mem_cons_of_mem _ hv)) hls
        simp only [Frame.readAll] at this
        simp [hl, hls] at hr
        subst hr
        have hx : ft.read (renameLoc σ l) = some x := by
          cases l with
          | reg r => exact h.1 r (hu r List.mem_cons_self) x hl
          | slot n => simp only [renameLoc, Frame.read, h.2]; exact hl
        simp [hx, this]

theorem writeAll_regs_other {v : Nat} :
    ∀ {locs : List (Loc Nat)} {vals : List Word} {fs fs' : Frame Nat},
      fs.writeAll locs vals = some fs' → Loc.reg v ∉ locs → fs'.regs v = fs.regs v
  | [], [], _, _, h, _ => by cases h; rfl
  | [], _ :: _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, h, _ => by cases h
  | l :: ls, x :: xs, fs, fs', h, hv => by
    simp only [Frame.writeAll] at h
    rw [writeAll_regs_other h (fun h' => hv (List.mem_cons_of_mem _ h'))]
    cases l with
    | reg r =>
      have : v ≠ r := by rintro rfl; exact hv List.mem_cons_self
      simp [Frame.write, this]
    | slot n => rfl

/-- Writing a list of locations whose registers, together with `A`, do not clash under `σ`
with a written register. -/
theorem FrameRel.writeAll :
    ∀ {locs : List (Loc Nat)} {vals : List Word} {A : Set Nat} {fs fs' ft : Frame Nat},
      FrameRel σ A fs ft →
      (∀ v, (v ∈ A ∨ Loc.reg v ∈ locs) → ∀ r, Loc.reg r ∈ locs → σ v = σ r → v = r) →
      fs.writeAll locs vals = some fs' →
      ∃ ft', ft.writeAll (locs.map (renameLoc σ)) vals = some ft' ∧
        FrameRel σ {v | v ∈ A ∨ Loc.reg v ∈ locs} fs' ft'
  | [], [], A, _, _, ft, hr, _, h => by
    cases h; exact ⟨ft, rfl, hr.mono fun v hv => by simpa using hv⟩
  | [], _ :: _, _, _, _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, _, _, _, h => by cases h
  | l :: ls, x :: xs, A, fs, fs', ft, hr, hint, h => by
    simp only [Frame.writeAll] at h
    cases l with
    | reg r =>
      have h₁ := hr.set r x fun v hv => hint v (.inl hv) r List.mem_cons_self
      obtain ⟨ft', hw, hr'⟩ := FrameRel.writeAll (A := insert r A) h₁ (fun v hv r' hr' => by
        refine hint v ?_ r' (List.mem_cons_of_mem _ hr')
        rcases hv with hv | hv
        · rcases Set.mem_insert_iff.mp hv with rfl | hv
          · exact .inr List.mem_cons_self
          · exact .inl hv
        · exact .inr (List.mem_cons_of_mem _ hv)) h
      refine ⟨ft', by simpa [Frame.writeAll, renameLoc, Frame.write] using hw, hr'.mono ?_⟩
      intro v hv
      rcases hv with hv | hv
      · exact .inl (Set.mem_insert_of_mem _ hv)
      · rcases List.mem_cons.mp hv with e | hv
        · cases e; exact .inl (Set.mem_insert _ _)
        · exact .inr hv
    | slot n =>
      have h₁ := hr.setSlot (L' := A) (fun _ h => h) n x
      obtain ⟨ft', hw, hr'⟩ := FrameRel.writeAll (A := A) h₁ (fun v hv r' hr' => by
        refine hint v ?_ r' (List.mem_cons_of_mem _ hr')
        rcases hv with hv | hv
        · exact .inl hv
        · exact .inr (List.mem_cons_of_mem _ hv)) h
      refine ⟨ft', by simpa [Frame.writeAll, renameLoc, Frame.write] using hw, hr'.mono ?_⟩
      intro v hv
      rcases hv with hv | hv
      · exact .inl hv
      · rcases List.mem_cons.mp hv with e | hv
        · cases e
        · exact .inr hv

/-! ## Operations -/

theorem renameOp_exec {L L' : Set Nat} {fs fs' ft : Frame Nat} {o : Op Nat} {m m' : Memory}
    (hr : FrameRel σ L fs ft) (huse : ∀ u ∈ opUses o, u ∈ L)
    (hlive : ∀ v ∈ L', v ∉ opDefs o → v ∈ L)
    (hint : ∀ v ∈ L', ∀ d ∈ opDefs o, σ v = σ d → v = d)
    (hx : o.exec fs m = some (fs', m')) :
    ∃ ft', (renameOp σ o).exec ft m = some (ft', m') ∧ FrameRel σ L' fs' ft' := by
  cases o with
  | const d v =>
    simp only [opDefs, List.mem_singleton, forall_eq] at hlive hint
    simp only [Op.exec, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨_, rfl, hr.dest hlive hint v⟩
  | move d s =>
    simp only [opDefs, opUses, List.mem_singleton, forall_eq] at hlive hint huse
    simp only [Op.exec] at hx
    cases hs : fs.get s with
    | none => simp [hs] at hx
    | some x =>
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨_, by simp [renameOp, Op.exec, hr.get huse hs], hr.dest hlive hint x⟩
  | unary op d s =>
    simp only [opDefs, opUses, List.mem_singleton, forall_eq] at hlive hint huse
    simp only [Op.exec] at hx
    cases hs : fs.get s with
    | none => simp [hs] at hx
    | some x =>
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨_, by simp [renameOp, Op.exec, hr.get huse hs], hr.dest hlive hint _⟩
  | binary op d x y =>
    simp only [opDefs, opUses, forall_eq, List.mem_cons, forall_eq_or_imp,
      List.not_mem_nil, or_false] at hlive hint huse
    simp only [Op.exec] at hx
    cases hx' : fs.get x with
    | none => simp [hx'] at hx
    | some vx =>
      cases hy' : fs.get y with
      | none => simp [hx', hy'] at hx
      | some vy =>
        cases hz : op.eval vx vy with
        | none => simp [hx', hy', hz] at hx
        | some z =>
          simp only [hx', hy', hz, Option.bind_some, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact ⟨_, by simp [renameOp, Op.exec, hr.get huse.1 hx', hr.get huse.2 hy', hz],
            hr.dest hlive hint z⟩
  | load w e d b off =>
    simp only [opDefs, opUses, List.mem_singleton, forall_eq] at hlive hint huse
    simp only [Op.exec] at hx
    cases hb : fs.get b with
    | none => simp [hb] at hx
    | some vb =>
      cases hl : m.load w e (vb.toNat + off) with
      | none => simp [hb, hl] at hx
      | some z =>
        simp only [hb, hl, Option.bind_some, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        exact ⟨_, by simp [renameOp, Op.exec, hr.get huse hb, hl], hr.dest hlive hint z⟩
  | store w b off src =>
    simp only [opDefs, opUses, List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
      false_imp_iff, imp_true_iff, and_true, not_false_eq_true, forall_const] at hlive huse
    simp only [Op.exec] at hx
    cases hb : fs.get b with
    | none => simp [hb] at hx
    | some vb =>
      cases hs : fs.get src with
      | none => simp [hb, hs] at hx
      | some vs =>
        cases hm : m.store w (vb.toNat + off) vs with
        | none => simp [hb, hs, hm] at hx
        | some mm =>
          simp only [hb, hs, hm, Option.bind_some, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact ⟨ft, by simp [renameOp, Op.exec, hr.get huse.1 hb, hr.get huse.2 hs, hm],
            hr.mono hlive⟩
  | slotGet d n =>
    simp only [opDefs, List.mem_singleton, forall_eq] at hlive hint
    simp only [Op.exec] at hx
    cases hs : fs.slots n with
    | none => simp [hs] at hx
    | some x =>
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨_, by simp [renameOp, Op.exec, hr.2, hs], hr.dest hlive hint x⟩
  | slotSet n s =>
    simp only [opDefs, opUses, List.mem_singleton, forall_eq, List.not_mem_nil,
      not_false_eq_true, forall_const] at hlive huse
    simp only [Op.exec] at hx
    cases hs : fs.get s with
    | none => simp [hs] at hx
    | some x =>
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨_, by simp [renameOp, Op.exec, hr.get huse hs], hr.setSlot hlive n x⟩

/-- A floating-point instruction, renamed: its operands are live, the registers live after it
other than `d` were live before, and none of them shares `d`'s new name. -/
theorem renameFop_exec {L L' : Set Nat} {fs fs' ft : Frame Nat} {op : FOp} {d a b : Nat}
    (hr : FrameRel σ L fs ft) (ha : a ∈ L) (hb : b ∈ L)
    (hlive : ∀ v ∈ L', v ≠ d → v ∈ L) (hint : ∀ v ∈ L', σ v = σ d → v = d)
    (hx : op.exec d a b fs = some fs') :
    ∃ ft', op.exec (σ d) (σ a) (σ b) ft = some ft' ∧ FrameRel σ L' fs' ft' := by
  simp only [FOp.exec] at hx
  cases hga : fs.get a with
  | none => simp [hga] at hx
  | some x =>
    cases hgb : fs.get b with
    | none => simp [hga, hgb] at hx
    | some y =>
      simp only [hga, hgb, Option.bind_some, Option.map_some, Option.some.injEq] at hx
      subst hx
      exact ⟨_, by simp [FOp.exec, hr.get ha hga, hr.get hb hgb], hr.dest hlive hint _⟩

/-! ## The liveness certificate -/

/-- Backward-dataflow inequalities for `live` (registers live before each point) and the
interference-freedom of the per-function renaming `σ`. -/
structure LiveCert (p : Prog Nat) (σ : FuncId → Nat → Nat) (live : Point → Set Nat) : Prop where
  uses : ∀ pt ins, p.fetch pt = some (.instr ins) → ∀ u ∈ instrUses ins, u ∈ live pt
  flow : ∀ pt ins, p.fetch pt = some (.instr ins) →
    ∀ v ∈ live pt.next, v ∉ instrDefs ins → v ∈ live pt
  interf : ∀ pt ins, p.fetch pt = some (.instr ins) →
    ∀ v, (v ∈ live pt.next ∨ v ∈ instrDefs ins) → ∀ d ∈ instrDefs ins,
      σ pt.func v = σ pt.func d → v = d
  termUses : ∀ pt t, p.fetch pt = some (.term t) → ∀ u ∈ termUses t, u ∈ live pt
  succ : ∀ pt t, p.fetch pt = some (.term t) →
    ∀ l ∈ termSuccs t, ∀ v ∈ live ⟨pt.func, l, 0⟩, v ∈ live pt
  params : ∀ f fn, p.func? f = some fn → ∀ v ∈ locRegs fn.params, ∀ w ∈ locRegs fn.params,
    σ f v = σ f w → v = w

/-- The certificate is satisfiable: the identity renaming with everything live. -/
theorem LiveCert.id (p : Prog Nat) : LiveCert p (fun _ => id) (fun _ => Set.univ) where
  uses _ _ _ _ _ := trivial
  flow _ _ _ _ _ _ := trivial
  interf _ _ _ _ _ _ _ e := e
  termUses _ _ _ _ _ := trivial
  succ _ _ _ _ _ _ _ := trivial
  params _ _ _ _ _ _ _ e := e

/-! ## The simulation -/

variable {σ : FuncId → Nat → Nat} {live : Point → Set Nat} {p : Prog Nat}

theorem rename_enter (hc : LiveCert p σ live) {f : FuncId} {vals : List Word} {pt : Point}
    {fr : Frame Nat} (h : p.enter f vals = some (pt, fr)) :
    ∃ ft, (renameProg σ p).enter f vals = some (pt, ft) ∧ pt.func = f ∧
      FrameRel (σ f) (live pt) fr ft := by
  unfold Prog.enter at h ⊢
  rw [renameProg_func?]
  cases hf : p.func? f with
  | none => simp [hf] at h
  | some fn =>
    simp only [hf, Option.bind_some] at h
    cases hw : Frame.empty.writeAll fn.params vals with
    | none => simp [hw] at h
    | some fr' =>
      simp only [hw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h₀ : FrameRel (σ f) ∅ (Frame.empty : Frame Nat) Frame.empty :=
        ⟨fun _ hv => hv.elim, rfl⟩
      obtain ⟨ft, hwt, hr⟩ := h₀.writeAll (fun v hv r hr e => by
        rcases hv with hv | hv
        · exact hv.elim
        · exact hc.params f fn hf v (mem_locRegs.mpr hv) r (mem_locRegs.mpr hr) e) hw
      refine ⟨ft, by simp [renameFuncND, hwt], rfl, fun v _ w hv => ?_, hr.2⟩
      by_cases hp : Loc.reg v ∈ fn.params
      · exact hr.1 v (.inr hp) w hv
      · rw [writeAll_regs_other hw hp] at hv
        cases hv

/-- Suspended activations: same point, frames related at the point of their call. -/
def StackRel (σ : FuncId → Nat → Nat) (live : Point → Set Nat) :
    List (Activation Nat) → List (Activation Nat) → Prop :=
  List.Forall₂ fun a b => b.point = a.point ∧ FrameRel (σ a.point.func) (live a.point) a.frame b.frame

structure Rel (σ : FuncId → Nat → Nat) (live : Point → Set Nat) (s t : State Nat) : Prop where
  point : t.point = s.point
  frame : FrameRel (σ s.point.func) (live s.point) s.frame t.frame
  stack : StackRel σ live s.stack t.stack
  mem : t.mem = s.mem

theorem fetch_rename {pt : Point} {c : Code Nat} (h : p.fetch pt = some c) :
    (renameProg σ p).fetch pt = some (renameCode (σ pt.func) c) := by
  rw [renameProg_fetch, h]; rfl

theorem fetch_rename_at {pt pt' : Point} {c : Code Nat} (e : pt' = pt) (h : p.fetch pt = some c) :
    (renameProg σ p).fetch pt' = some (renameCode (σ pt.func) c) := by
  subst e; exact fetch_rename h

/-- The renaming as a lock-step simulation into the renamed program. -/
def simulation (hc : LiveCert p σ live) : CaseSimulation p (LirTarget (renameProg σ p)) where
  Match := Rel σ live
  measure := fun _ => 0
  Returned := fun vs m t => step (renameProg σ p) t = .returned vs m
  Trapped := fun m t => step (renameProg σ p) t = .trapped m
  op := by
    intro s t o fr m hm hf he
    have hft := fetch_rename_at (σ := σ) hm.point hf
    obtain ⟨ft', hx, hr⟩ := renameOp_exec (L' := live s.point.next) hm.frame
      (hc.uses _ _ hf) (hc.flow _ _ hf) (fun v hv d hd => hc.interf _ _ hf v (.inl hv) d hd) he
    rw [← hm.mem] at hx
    have st := (Transition.op (s := t) hft hx).step_eq
    refine ⟨{ t with point := t.point.next, frame := ft', mem := m }, ⟨?_, ?_, hm.stack, rfl⟩,
      .inl (.single st)⟩
    · simp [hm.point]
    · exact hr
  call := by
    intro s t f args results vals pt fr hm hf ha he
    have hft := fetch_rename_at (σ := σ) hm.point hf
    obtain ⟨ft, hen, hpf, hfr⟩ := rename_enter hc he
    have hra := hm.frame.readAll (fun v hv => hc.uses _ _ hf v (mem_locRegs.mpr hv)) ha
    have st := (Transition.call (s := t) hft hra hen).step_eq
    refine ⟨⟨pt, ft, ⟨t.point, t.frame⟩ :: t.stack, t.mem⟩, ⟨rfl, by rw [hpf]; exact hfr, ?_,
      hm.mem⟩, .inl (.single st)⟩
    exact List.Forall₂.cons ⟨hm.point, hm.frame⟩ hm.stack
  fop := by
    intro s t op d a b fr hm hf he
    have hft := fetch_rename_at (σ := σ) hm.point hf
    obtain ⟨ft', hx, hr⟩ := renameFop_exec (L' := live s.point.next) hm.frame
      (hc.uses _ _ hf a (by simp [instrUses])) (hc.uses _ _ hf b (by simp [instrUses]))
      (fun v hv hne => hc.flow _ _ hf v hv (by simpa [instrDefs] using hne))
      (fun v hv e => hc.interf _ _ hf v (.inl hv) d (by simp [instrDefs]) e) he
    have st := (Transition.fop (s := t) hft hx).step_eq
    refine ⟨{ t with point := t.point.next, frame := ft' }, ⟨?_, ?_, hm.stack, hm.mem⟩,
      .inl (.single st)⟩
    · simp [hm.point]
    · exact hr
  jump := by
    intro s t l hm hf
    have hft := fetch_rename_at (σ := σ) hm.point hf
    have st := (Transition.jump (s := t) hft).step_eq
    refine ⟨{ t with point := ⟨t.point.func, l, 0⟩ }, ⟨by simp [hm.point], ?_, hm.stack, hm.mem⟩,
      .inl (.single st)⟩
    exact hm.frame.mono fun v hv => hc.succ _ _ hf l (by simp [termSuccs]) v hv
  branch := by
    intro s t c l₁ l₂ x hm hf hx
    have hft := fetch_rename_at (σ := σ) hm.point hf
    have hx' := hm.frame.get (hc.termUses _ _ hf c (by simp [RegAlloc.termUses])) hx
    have st := (Transition.branch (s := t) hft hx').step_eq
    refine ⟨{ t with point := ⟨t.point.func, if x = 0 then l₂ else l₁, 0⟩ },
      ⟨by simp [hm.point], ?_, hm.stack, hm.mem⟩, .inl (.single st)⟩
    refine hm.frame.mono fun v hv => hc.succ _ _ hf _ ?_ v hv
    split <;> simp [termSuccs]
  ret := by
    intro s t locs vals act rest f args results fr hm hf hv hs ha hw
    have hft := fetch_rename_at (σ := σ) hm.point hf
    have hra := hm.frame.readAll
      (fun v hv => hc.termUses _ _ hf v (by simpa [RegAlloc.termUses, mem_locRegs] using hv)) hv
    have hst := hm.stack
    rw [hs] at hst
    cases htst : t.stack with
    | nil => rw [htst] at hst; cases hst
    | cons act' rest' =>
      rw [htst] at hst
      obtain ⟨⟨hap, haf⟩, hrest⟩ := List.forall₂_cons.mp hst
      have hfa := fetch_rename_at (σ := σ) hap ha
      obtain ⟨ft, hwt, hr⟩ := (haf.mono (L' := {v | v ∈ live act.point.next ∧
          Loc.reg v ∉ results}) fun v hv =>
            hc.flow _ _ ha v hv.1 (by simpa [instrDefs, mem_locRegs] using hv.2)).writeAll
        (fun v hv r hr e => by
          refine hc.interf _ _ ha v ?_ r (by simpa [instrDefs, mem_locRegs] using hr) e
          rcases hv with hv | hv
          · exact .inl hv.1
          · exact .inr (by simpa [instrDefs, mem_locRegs] using hv)) hw
      have st := (Transition.ret (s := t) hft hra htst hfa hwt).step_eq
      refine ⟨⟨act'.point.next, ft, rest', t.mem⟩, ⟨by simp [hap], ?_, hrest, hm.mem⟩,
        .inl (.single st)⟩
      refine hr.mono fun v hv => ?_
      by_cases e : Loc.reg v ∈ results
      · exact .inr e
      · exact .inl ⟨hv, e⟩
  halt := by
    intro s t locs vals hm hf hv hs
    have hft := fetch_rename_at (σ := σ) hm.point hf
    have hra := hm.frame.readAll
      (fun v hv => hc.termUses _ _ hf v (by simpa [RegAlloc.termUses, mem_locRegs] using hv)) hv
    have hst := hm.stack
    rw [hs] at hst
    have htst : t.stack = [] := List.forall₂_nil_left_iff.mp hst
    refine ⟨t, .refl, ?_⟩
    rw [← hm.mem]
    exact (Transition.halt (s := t) hft hra htst).step_eq
  trap := by
    intro s t hm hf
    have hft := fetch_rename_at (σ := σ) hm.point hf
    refine ⟨t, .refl, ?_⟩
    rw [← hm.mem]
    exact (Transition.trap (s := t) hft).step_eq

theorem rename_start (hc : LiveCert p σ live) {f : FuncId} {args : List Word} {mem : Memory}
    {s : State Nat} (h : p.start f args mem = some s) :
    ∃ t, (renameProg σ p).start f args mem = some t ∧ Rel σ live s t := by
  unfold Prog.start at h ⊢
  cases he : p.enter f args with
  | none => simp [he] at h
  | some r =>
    obtain ⟨pt, fr⟩ := r
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨ft, hen, hpf, hr⟩ := rename_enter hc he
    exact ⟨⟨pt, ft, [], mem⟩, by rw [hen]; rfl, ⟨rfl, by rw [hpf]; exact hr, .nil, rfl⟩⟩

/-- **Semantic preservation of renaming.** Under a liveness certificate for which the
per-function renaming `σ` is interference-free, every non-stuck behaviour of a
whole-program run is a behaviour of the renamed program started with the same function,
arguments and memory. -/
theorem rename_behaves (hc : LiveCert p σ live) {f : FuncId} {args : List Word}
    {mem : Memory} {s : State Nat} (h : p.start f args mem = some s) {b : Behavior}
    (hb : Behaves p s b) (hns : b ≠ .stuck) :
    ∃ t, (renameProg σ p).start f args mem = some t ∧ Behaves (renameProg σ p) t b := by
  obtain ⟨t, ht, hr⟩ := rename_start hc h
  exact ⟨t, ht, (simulation hc).toForward.behaves ⟨fun _ _ _ h => h, fun _ _ h => h⟩ hr hb hns⟩

open Silmaril.Machine.Behaviour (Refines Mode Obs) in
/-- Renaming refines the original program from the start states of the same call, in the
strict mode with the identity observation (the analogue of `Lir.Alloc.spill_refines`). -/
theorem rename_refines (hc : LiveCert p σ live) :
    Refines Mode.strict (sem (renameProg σ p)) (sem p)
      (fun t s => ∃ f args mem, p.start f args mem = some s ∧
        (renameProg σ p).start f args mem = some t)
      (fun _ _ => Obs.id) := by
  refine Refines.of_forward (sem_deterministic _) (fun _ s _ _ => beh_exists s) ?_
  rintro t s ⟨f, args, mem, hs, ht⟩ hsafe o ho
  obtain ⟨b, rfl, hb, hns⟩ := beh_of_safe hsafe ho
  obtain ⟨t', ht', hb'⟩ := rename_behaves hc hs hb hns
  rw [ht] at ht'
  cases ht'
  exact ⟨b.toOutcome, beh_iff_behaves.mpr hb', Behaviour.Outcome.Rel.refl Obs.isRefl_id _ _⟩

/-! ## Dropping self-moves

`renameInstr` deletes the moves `move d s` with `σ d = σ s`, which renaming turns into
self-moves `move r r`. A self-move that runs leaves the frame unchanged, so deleting
instructions that are self-moves preserves every non-stuck behaviour. `dropProg D q`
deletes, in function `f`, the instructions `i` with `D f i`; `DropsSelfMoves D` says that
these are self-moves. The simulation maps instruction `i` of a block to the number of kept
instructions before it (`dropPoint`); a deleted self-move is matched by no target step,
and the number of deleted instructions left in the block decreases (`dropMeasure`). -/

def isSelfMove : Instr Nat → Bool
  | .op (.move d s) => d == s
  | _ => false

def dropBlock (g : Instr Nat → Bool) (b : Block Nat) : Block Nat :=
  ⟨b.instrs.filter (fun i => !g i), b.term⟩

def dropFunc (g : Instr Nat → Bool) (fn : Func Nat) : Func Nat :=
  { fn with blocks := fn.blocks.map (dropBlock g) }

def dropProg (D : FuncId → Instr Nat → Bool) (q : Prog Nat) : Prog Nat :=
  ⟨q.funcs.mapIdx fun f fn => dropFunc (D f) fn⟩

def DropsSelfMoves (D : FuncId → Instr Nat → Bool) : Prop :=
  ∀ f i, D f i = true → ∃ r, i = .op (.move r r)

theorem dropsSelfMoves_isSelfMove : DropsSelfMoves fun _ => isSelfMove := by
  intro _ i h
  match i, h with
  | .op (.move d s), h =>
    simp only [isSelfMove, beq_iff_eq] at h
    exact ⟨d, by rw [h]⟩

section Drop

variable {D : FuncId → Instr Nat → Bool} {q : Prog Nat}

theorem dropProg_func? (f : FuncId) : (dropProg D q).func? f = (q.func? f).map (dropFunc (D f)) := by
  simp [dropProg, Prog.func?]

theorem dropProg_block? (f : FuncId) (l : Label) :
    (dropProg D q).block? f l = (q.block? f l).map (dropBlock (D f)) := by
  unfold Prog.block?
  rw [dropProg_func?]
  cases q.func? f <;> simp [dropFunc]

theorem dropProg_enter {f : FuncId} {vals : List Word} :
    (dropProg D q).enter f vals = q.enter f vals := by
  unfold Prog.enter
  rw [dropProg_func?]
  cases q.func? f <;> rfl

theorem enter_index {f : FuncId} {vals : List Word} {pt : Point} {fr : Frame Nat}
    (h : q.enter f vals = some (pt, fr)) : pt.index = 0 := by
  unfold Prog.enter at h
  cases hf : q.func? f with
  | none => simp [hf] at h
  | some fn =>
    simp only [hf, Option.bind_some, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl, _⟩ := h
    rfl

/-- Kept instructions before index `i`. -/
def keptBefore (g : Instr Nat → Bool) (b : Block Nat) (i : Nat) : Nat :=
  ((b.instrs.take i).filter (fun x => !g x)).length

def dropPoint (D : FuncId → Instr Nat → Bool) (q : Prog Nat) (pt : Point) : Point :=
  match q.block? pt.func pt.label with
  | some b => ⟨pt.func, pt.label, keptBefore (D pt.func) b pt.index⟩
  | none => pt

/-- Deleted instructions from the current point to the end of the block. -/
def dropMeasure (D : FuncId → Instr Nat → Bool) (q : Prog Nat) (s : State Nat) : Nat :=
  match q.block? s.point.func s.point.label with
  | some b => ((b.instrs.drop s.point.index).filter (D s.point.func)).length
  | none => 0

theorem dropPoint_func (pt : Point) : (dropPoint D q pt).func = pt.func := by
  unfold dropPoint; split <;> rfl

theorem dropPoint_zero (f : FuncId) (l : Label) : dropPoint D q ⟨f, l, 0⟩ = ⟨f, l, 0⟩ := by
  unfold dropPoint; split <;> simp [keptBefore]

theorem dropPoint_index_zero {pt : Point} (h : pt.index = 0) : dropPoint D q pt = pt := by
  obtain ⟨f, l, i⟩ := pt
  simp only at h
  subst h
  exact dropPoint_zero f l

theorem filter_getElem?_kept {α : Type} (g : α → Bool) {L : List α} {i : Nat} {x : α}
    (h : L[i]? = some x) (hx : g x = true) :
    (L.filter g)[((L.take i).filter g).length]? = some x := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
  have e : L.filter g = (L.take i).filter g ++ L[i] :: (L.drop (i + 1)).filter g := by
    conv_lhs => rw [← List.take_append_drop i L]
    rw [List.filter_append, List.drop_eq_getElem_cons hlt, List.filter_cons_of_pos hx]
  rw [e, List.getElem?_append_right (le_refl _)]
  simp

theorem filter_take_succ {α : Type} (g : α → Bool) {L : List α} {i : Nat} {x : α}
    (h : L[i]? = some x) :
    ((L.take (i + 1)).filter g).length = ((L.take i).filter g).length + if g x then 1 else 0 := by
  rw [List.take_add_one, h]
  cases hgx : g x <;> simp [hgx]

theorem filter_drop_succ {α : Type} (g : α → Bool) {L : List α} {i : Nat} {x : α}
    (h : L[i]? = some x) (hx : g x = true) :
    ((L.drop i).filter g).length = ((L.drop (i + 1)).filter g).length + 1 := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons hlt, List.filter_cons_of_pos hx]
  rfl

theorem drop_fetch_kept {pt : Point} {ins : Instr Nat} (h : q.fetch pt = some (.instr ins))
    (hk : D pt.func ins = false) :
    (dropProg D q).fetch (dropPoint D q pt) = some (.instr ins) ∧
      dropPoint D q pt.next = (dropPoint D q pt).next := by
  obtain ⟨b, hb, hc⟩ := Prog.fetch_eq_some h
  rcases hc with ⟨i', hi, e⟩ | ⟨_, e⟩
  · cases e
    have hp : dropPoint D q pt = ⟨pt.func, pt.label, keptBefore (D pt.func) b pt.index⟩ := by
      simp [dropPoint, hb]
    refine ⟨?_, ?_⟩
    · rw [hp]
      refine Prog.fetch_eq_instr (pt := ⟨pt.func, pt.label, _⟩)
        (by rw [dropProg_block?, hb]; rfl) ?_
      exact filter_getElem?_kept _ hi (by simp [hk])
    · simp [dropPoint, hb, Point.next, keptBefore, filter_take_succ _ hi, hk]
  · cases e

theorem drop_fetch_dropped {pt : Point} {ins : Instr Nat} (h : q.fetch pt = some (.instr ins))
    (hk : D pt.func ins = true) : dropPoint D q pt.next = dropPoint D q pt := by
  obtain ⟨b, hb, hc⟩ := Prog.fetch_eq_some h
  rcases hc with ⟨i', hi, e⟩ | ⟨_, e⟩
  · cases e
    simp [dropPoint, hb, Point.next, keptBefore, filter_take_succ _ hi, hk]
  · cases e

theorem drop_fetch_term {pt : Point} {t : Term Nat} (h : q.fetch pt = some (.term t)) :
    (dropProg D q).fetch (dropPoint D q pt) = some (.term t) := by
  obtain ⟨b, hb, hc⟩ := Prog.fetch_eq_some h
  rcases hc with ⟨i', _, e⟩ | ⟨hi, e⟩
  · cases e
  · cases e
    have hp : dropPoint D q pt = ⟨pt.func, pt.label, keptBefore (D pt.func) b pt.index⟩ := by
      simp [dropPoint, hb]
    rw [hp]
    exact Prog.fetch_eq_term (pt := ⟨pt.func, pt.label, _⟩) (b := dropBlock (D pt.func) b)
      (by rw [dropProg_block?, hb]; rfl) (by simp [keptBefore, hi, dropBlock])

theorem drop_kept_of_call (hD : DropsSelfMoves D) {f g : FuncId} {args res : List (Loc Nat)} :
    D f (.call g args res) = false := by
  cases h : D f (.call g args res)
  · rfl
  · obtain ⟨r, e⟩ := hD _ _ h; cases e

theorem drop_kept_of_fop (hD : DropsSelfMoves D) {f : FuncId} {op : FOp} {d a b : Nat} :
    D f (.fop op d a b) = false := by
  cases h : D f (.fop op d a b)
  · rfl
  · obtain ⟨r, e⟩ := hD _ _ h; cases e

structure DropRel (D : FuncId → Instr Nat → Bool) (q : Prog Nat) (s t : State Nat) : Prop where
  point : t.point = dropPoint D q s.point
  frame : t.frame = s.frame
  stack : t.stack = s.stack.map fun a => ⟨dropPoint D q a.point, a.frame⟩
  mem : t.mem = s.mem

theorem frame_set_self {fr : Frame Nat} {r : Nat} {x : Word} (h : fr.get r = some x) :
    fr.set r x = fr := by
  obtain ⟨regs, slots⟩ := fr
  simp only [Frame.set, Frame.mk.injEq, and_true]
  funext r'
  split
  · subst r'; exact h.symm
  · rfl

/-- Deleting self-moves as a simulation into the reduced program. -/
def dropSimulation (hD : DropsSelfMoves D) (q : Prog Nat) :
    CaseSimulation q (LirTarget (dropProg D q)) where
  Match := DropRel D q
  measure := dropMeasure D q
  Returned := fun vs m t => step (dropProg D q) t = .returned vs m
  Trapped := fun m t => step (dropProg D q) t = .trapped m
  op := by
    intro s t o fr m hm hf he
    cases hk : D s.point.func (.op o)
    · obtain ⟨hft, hnext⟩ := drop_fetch_kept hf hk
      rw [← hm.point] at hft
      rw [← hm.frame, ← hm.mem] at he
      have st := (Transition.op (s := t) hft he).step_eq
      refine ⟨{ t with point := t.point.next, frame := fr, mem := m },
        ⟨by simp [hm.point, hnext], rfl, hm.stack, rfl⟩, .inl (.single st)⟩
    · obtain ⟨r, e⟩ := hD _ _ hk
      cases e
      simp only [Op.exec] at he
      cases hr : s.frame.get r with
      | none => simp [hr] at he
      | some x =>
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨t, ⟨by rw [drop_fetch_dropped hf hk, hm.point], by rw [frame_set_self hr, hm.frame],
          hm.stack, hm.mem⟩, .inr ⟨rfl, ?_⟩⟩
        obtain ⟨b, hb, hc⟩ := Prog.fetch_eq_some hf
        rcases hc with ⟨i', hi, e⟩ | ⟨_, e⟩
        · cases e
          simp only [dropMeasure, Point.next_func, Point.next_label, Point.next_index, hb]
          rw [filter_drop_succ _ hi hk]
          omega
        · cases e
  call := by
    intro s t f args results vals pt fr hm hf ha he
    obtain ⟨hft, _⟩ := drop_fetch_kept hf (drop_kept_of_call hD)
    rw [← hm.point] at hft
    rw [← hm.frame] at ha
    rw [← dropProg_enter (D := D)] at he
    have st := (Transition.call (s := t) hft ha he).step_eq
    refine ⟨⟨pt, fr, ⟨t.point, t.frame⟩ :: t.stack, t.mem⟩, ⟨?_, rfl, ?_, hm.mem⟩, .inl (.single st)⟩
    · rw [dropProg_enter] at he
      exact (dropPoint_index_zero (enter_index he)).symm
    · simp [hm.point, hm.frame, hm.stack]
  fop := by
    intro s t op d a b fr hm hf he
    obtain ⟨hft, hnext⟩ := drop_fetch_kept hf (drop_kept_of_fop hD)
    rw [← hm.point] at hft
    rw [← hm.frame] at he
    have st := (Transition.fop (s := t) hft he).step_eq
    refine ⟨{ t with point := t.point.next, frame := fr },
      ⟨by simp [hm.point, hnext], rfl, hm.stack, hm.mem⟩, .inl (.single st)⟩
  jump := by
    intro s t l hm hf
    have hft := drop_fetch_term (D := D) hf
    rw [← hm.point] at hft
    have st := (Transition.jump (s := t) hft).step_eq
    refine ⟨{ t with point := ⟨t.point.func, l, 0⟩ }, ⟨?_, hm.frame, hm.stack, hm.mem⟩,
      .inl (.single st)⟩
    simp [hm.point, dropPoint_func, dropPoint_zero]
  branch := by
    intro s t c l₁ l₂ x hm hf hx
    have hft := drop_fetch_term (D := D) hf
    rw [← hm.point] at hft
    rw [← hm.frame] at hx
    have st := (Transition.branch (s := t) hft hx).step_eq
    refine ⟨{ t with point := ⟨t.point.func, if x = 0 then l₂ else l₁, 0⟩ },
      ⟨?_, hm.frame, hm.stack, hm.mem⟩, .inl (.single st)⟩
    simp [hm.point, dropPoint_func, dropPoint_zero]
  ret := by
    intro s t locs vals act rest f args results fr hm hf hv hs ha hw
    have hft := drop_fetch_term (D := D) hf
    rw [← hm.point] at hft
    rw [← hm.frame] at hv
    obtain ⟨hfa, hnext⟩ := drop_fetch_kept ha (drop_kept_of_call hD)
    have htst : t.stack = ⟨dropPoint D q act.point, act.frame⟩ ::
        rest.map fun a => ⟨dropPoint D q a.point, a.frame⟩ := by
      rw [hm.stack, hs]; rfl
    have st := (Transition.ret (s := t) (a := ⟨dropPoint D q act.point, act.frame⟩) hft hv htst
      hfa hw).step_eq
    refine ⟨⟨(dropPoint D q act.point).next, fr,
      rest.map fun (a : Activation Nat) => (⟨dropPoint D q a.point, a.frame⟩ : Activation Nat),
      t.mem⟩, ⟨hnext.symm, rfl, rfl, hm.mem⟩, .inl (.single st)⟩
  halt := by
    intro s t locs vals hm hf hv hs
    have hft := drop_fetch_term (D := D) hf
    rw [← hm.point] at hft
    rw [← hm.frame] at hv
    have htst : t.stack = [] := by rw [hm.stack, hs]; rfl
    refine ⟨t, .refl, ?_⟩
    rw [← hm.mem]
    exact (Transition.halt (s := t) hft hv htst).step_eq
  trap := by
    intro s t hm hf
    have hft := drop_fetch_term (D := D) hf
    rw [← hm.point] at hft
    refine ⟨t, .refl, ?_⟩
    rw [← hm.mem]
    exact (Transition.trap (s := t) hft).step_eq

theorem drop_start {f : FuncId} {args : List Word} {mem : Memory} {s : State Nat}
    (h : q.start f args mem = some s) :
    ∃ t, (dropProg D q).start f args mem = some t ∧ DropRel D q s t := by
  refine ⟨s, by simpa [Prog.start, dropProg_enter] using h, ⟨?_, rfl, ?_, rfl⟩⟩
  · unfold Prog.start at h
    cases he : q.enter f args with
    | none => simp [he] at h
    | some r =>
      simp only [he, Option.map_some, Option.some.injEq] at h
      subst h
      exact (dropPoint_index_zero (enter_index he)).symm
  · unfold Prog.start at h
    cases he : q.enter f args with
    | none => simp [he] at h
    | some r => simp only [he, Option.map_some, Option.some.injEq] at h; subst h; rfl

/-- **Deleting self-moves preserves non-stuck behaviours.** -/
theorem drop_behaves (hD : DropsSelfMoves D) {f : FuncId} {args : List Word} {mem : Memory}
    {s : State Nat} (h : q.start f args mem = some s) {b : Behavior} (hb : Behaves q s b)
    (hns : b ≠ .stuck) :
    ∃ t, (dropProg D q).start f args mem = some t ∧ Behaves (dropProg D q) t b := by
  obtain ⟨t, ht, hr⟩ := drop_start h
  exact ⟨t, ht,
    (dropSimulation hD q).toForward.behaves ⟨fun _ _ _ h => h, fun _ _ h => h⟩ hr hb hns⟩

end Drop

/-- Renaming followed by deleting self-moves: the shape of `renumber`. -/
theorem renameDrop_behaves {D : FuncId → Instr Nat → Bool} (hD : DropsSelfMoves D)
    (hc : LiveCert p σ live) {f : FuncId} {args : List Word} {mem : Memory} {s : State Nat}
    (h : p.start f args mem = some s) {b : Behavior} (hb : Behaves p s b) (hns : b ≠ .stuck) :
    ∃ t, (dropProg D (renameProg σ p)).start f args mem = some t ∧
      Behaves (dropProg D (renameProg σ p)) t b := by
  obtain ⟨t, ht, hb'⟩ := rename_behaves hc h hb hns
  exact drop_behaves hD ht hb' hns

/-! ## `renumber` as renaming followed by deleting self-moves

`renumber k p` is `dropProg (renumberDrop p) (renameProg (renumberσ k p) p)`: a function
whose liveness converges is renamed by the `assign`ed numbering and loses its self-moves; a
function whose liveness does not converge is unchanged (identity renaming, nothing
deleted). Its correctness is therefore reduced to a `LiveCert` for `renumberσ k p`. -/

/-- The numbering `renumberFunc` applies to a function. -/
def funcσ (k : Nat) (fn : Func Nat) : Nat → Nat :=
  match liveness fn.blocks.toArray (fn.blocks.toArray.size + 2) with
  | none => id
  | some (liveIn, liveOut) =>
    let σ := assign k (infos fn fn.blocks.toArray liveIn liveOut)
    fun v => σ.getD v v

/-- Whether `renumberFunc` renames (and deletes the self-moves of) a function. -/
def funcRenamed (fn : Func Nat) : Bool :=
  (liveness fn.blocks.toArray (fn.blocks.toArray.size + 2)).isSome

def renumberσ (k : Nat) (p : Prog Nat) (f : FuncId) : Nat → Nat :=
  (p.funcs[f]?.map (funcσ k)).getD id

def renumberDrop (p : Prog Nat) (f : FuncId) (i : Instr Nat) : Bool :=
  (p.funcs[f]?.map funcRenamed).getD false && isSelfMove i

theorem renumberDrop_dropsSelfMoves (p : Prog Nat) : DropsSelfMoves (renumberDrop p) :=
  fun f i h => dropsSelfMoves_isSelfMove f i (Bool.and_eq_true_iff.mp h).2

theorem renameOp_id (o : Op Nat) : renameOp id o = o := by cases o <;> rfl

theorem renameLoc_id : renameLoc id = id := by funext l; cases l <;> rfl

theorem renameTerm_id (t : Term Nat) : renameTerm id t = t := by
  cases t <;> simp [renameTerm, renameLoc_id]

theorem renameFuncND_id (fn : Func Nat) : renameFuncND id fn = fn := by
  obtain ⟨params, entry, blocks⟩ := fn
  have hi : renameInstrND id = id := by
    funext i; cases i <;> simp [renameInstrND, renameOp_id, renameLoc_id]
  have hb : renameBlockND id = id := by
    funext b; simp [renameBlockND, hi, renameTerm_id]
  simp [renameFuncND, renameLoc_id, hb]

theorem renameInstr_eq (σ : Nat → Nat) (i : Instr Nat) :
    renameInstr σ i = if isSelfMove (renameInstrND σ i) then [] else [renameInstrND σ i] := by
  cases i with
  | op o => cases o <;> simp [renameInstr, renameOp, renameInstrND, isSelfMove]
  | call => simp [renameInstr, renameInstrND, isSelfMove]
  | fop => simp [renameInstr, renameInstrND, isSelfMove]

theorem flatMap_renameInstr (σ : Nat → Nat) (l : List (Instr Nat)) :
    l.flatMap (renameInstr σ) = (l.map (renameInstrND σ)).filter fun i => !(true && isSelfMove i) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.flatMap_cons, ih, renameInstr_eq, List.map_cons, List.filter_cons]
    cases isSelfMove (renameInstrND σ i) <;> simp

theorem renumberFunc_eq (k : Nat) (fn : Func Nat) :
    renumberFunc k fn =
      dropFunc (fun i => funcRenamed fn && isSelfMove i) (renameFuncND (funcσ k fn) fn) := by
  unfold renumberFunc funcσ funcRenamed
  split
  · next h =>
    simp only [h, Option.isSome_none, Bool.false_and]
    rw [renameFuncND_id]
    have hd : dropBlock (fun _ => false) = id := by funext b; simp [dropBlock]
    simp [dropFunc, hd]
  · next liveIn liveOut h =>
    simp only [h, Option.isSome_some]
    simp [renameFunc, dropFunc, renameFuncND, renameBlockND, dropBlock, flatMap_renameInstr]

theorem renumber_eq (k : Nat) (p : Prog Nat) :
    renumber k p = dropProg (renumberDrop p) (renameProg (renumberσ k p) p) := by
  simp only [renumber, dropProg, renameProg, Prog.mk.injEq]
  apply List.ext_getElem?
  intro f
  simp only [List.getElem?_map, List.getElem?_mapIdx]
  cases h : p.funcs[f]? with
  | none => rfl
  | some fn =>
    simp only [Option.map_some, renumberσ, h, Option.getD_some, renumberFunc_eq]
    congr 2
    funext i
    simp [renumberDrop, h]

/-- **Correctness of `renumber`, relative to a liveness certificate.** If some liveness
certificate makes the numbering `renumberσ k p` interference-free, every non-stuck
behaviour of a whole-program run of `p` is a behaviour of `renumber k p`. -/
theorem renumber_behaves (k : Nat) (hc : LiveCert p (renumberσ k p) live) {f : FuncId}
    {args : List Word} {mem : Memory} {s : State Nat} (h : p.start f args mem = some s)
    {b : Behavior} (hb : Behaves p s b) (hns : b ≠ .stuck) :
    ∃ t, (renumber k p).start f args mem = some t ∧ Behaves (renumber k p) t b := by
  rw [renumber_eq]
  exact renameDrop_behaves (renumberDrop_dropsSelfMoves p) hc h hb hns

open Silmaril.Machine.Behaviour (Refines Mode Obs) in
theorem renumber_refines (k : Nat) (hc : LiveCert p (renumberσ k p) live) :
    Refines Mode.strict (sem (renumber k p)) (sem p)
      (fun t s => ∃ f args mem, p.start f args mem = some s ∧
        (renumber k p).start f args mem = some t)
      (fun _ _ => Obs.id) := by
  refine Refines.of_forward (sem_deterministic _) (fun _ s _ _ => beh_exists s) ?_
  rintro t s ⟨f, args, mem, hs, ht⟩ hsafe o ho
  obtain ⟨b, rfl, hb, hns⟩ := beh_of_safe hsafe ho
  obtain ⟨t', ht', hb'⟩ := renumber_behaves k hc hs hb hns
  rw [ht] at ht'
  cases ht'
  exact ⟨b.toOutcome, beh_iff_behaves.mpr hb', Behaviour.Outcome.Rel.refl Obs.isRefl_id _ _⟩

end Silmaril.Compile.Target.RegAlloc
