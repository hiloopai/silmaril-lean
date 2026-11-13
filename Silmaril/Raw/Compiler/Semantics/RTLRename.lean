module

public import Silmaril.Machine.CBackend.RTL.Semantics.Defs
public import Silmaril.Foundations.ForwardSim

@[expose] public section

/-!
# Renaming the registers of an RTL program

`Prog.rename g` applies a register map `g : R → S` to every instruction and parameter list of
an RTL program. For an **injective** `g` the renamed program is the same program: one step of
the renamed machine from a renamed state is the renamed step (`step_rename`, an equation, not
a simulation), so the two programs have exactly the same behaviours, stuck included
(`behaves_rename_iff`), from corresponding start states (`start_rename`).

The zoo (`Silmaril.Compile.Semantics.RTL`) needs this because every pass on the RTL family
changes the register type (`Name R` after the maximal SSA construction, `R ⊕ Nat` after
sequentialization), while `Lir` programs of the zoo are over `Nat`: an injective encoding
into `Nat` followed by `Prog.rename` closes the loop.
-/

namespace Silmaril.Machine.RTL

open Silmaril.Machine.Lir (Word Memory)

variable {R S : Type} (g : R → S)

/-! ## Syntax -/

/-- An instruction with its registers renamed. -/
def Instr.rename : Instr R → Instr S
  | .nop n => .nop n
  | .const d v n => .const (g d) v n
  | .move d s n => .move (g d) (g s) n
  | .unary op d s n => .unary op (g d) (g s) n
  | .binary op d a b n => .binary op (g d) (g a) (g b) n
  | .load w e d b o n => .load w e (g d) (g b) o n
  | .store w b o s n => .store w (g b) o (g s) n
  | .call f as rs n => .call f (as.map g) (rs.map g) n
  | .cond c a b => .cond (g c) a b
  | .jump t => .jump t
  | .ret vs => .ret (vs.map g)
  | .trap => .trap

/-- A function with its registers renamed. -/
def Func.rename (fn : Func R) : Func S :=
  ⟨fn.sig, fn.params.map g, fn.entry, fn.code.map (Instr.rename g)⟩

/-- A program with its registers renamed. -/
def Prog.rename (p : Prog R) : Prog S := ⟨p.funcs.map (Func.rename g)⟩

@[simp] theorem Prog.func?_rename (p : Prog R) (f : FuncId) :
    (p.rename g).func? f = (p.func? f).map (Func.rename g) := by
  simp [Prog.func?, Prog.rename]

theorem Prog.fetch_rename (p : Prog R) (pt : Point) :
    (p.rename g).fetch pt = (p.fetch pt).map (Instr.rename g) := by
  simp only [Prog.fetch, Prog.instr?, Prog.func?_rename]
  cases p.func? pt.func <;> simp [Func.instr?, Func.rename]

/-! ## States -/

section

open Classical in
/-- A frame with its registers renamed: a register outside the image of `g` is unwritten. -/
noncomputable def Frame.rename (fr : Frame R) : Frame S :=
  ⟨fun x => if h : ∃ r, g r = x then fr.regs h.choose else none⟩

/-- A suspended caller with its registers renamed. -/
noncomputable def Activation.rename (a : Activation R) : Activation S :=
  ⟨a.point, a.frame.rename g⟩

/-- A state with its registers renamed. -/
noncomputable def State.rename (s : State R) : State S :=
  ⟨s.point, s.frame.rename g, s.stack.map (Activation.rename g), s.mem⟩

/-- A result with its registers renamed. -/
noncomputable def Result.rename : Result R → Result S
  | .running s => .running (s.rename g)
  | .returned vs m => .returned vs m
  | .trapped m => .trapped m
  | .stuck => .stuck

theorem Frame.rename_empty : (Frame.empty : Frame R).rename g = Frame.empty := by
  show Frame.mk _ = Frame.mk _
  congr 1
  funext x
  simp [Frame.empty]

variable {g} (hg : Function.Injective g)
include hg

theorem Frame.rename_get (fr : Frame R) (r : R) : (fr.rename g).get (g r) = fr.get r := by
  have h : ∃ r', g r' = g r := ⟨r, rfl⟩
  simp only [Frame.rename, Frame.get, dite_eq_left h]
  rw [hg h.choose_spec]

variable [DecidableEq R] [DecidableEq S]

theorem Frame.rename_set (fr : Frame R) (r : R) (w : Word) :
    (fr.set r w).rename g = (fr.rename g).set (g r) w := by
  show Frame.mk _ = Frame.mk _
  congr 1
  funext x
  by_cases hx : ∃ r', g r' = x
  · obtain ⟨r', rfl⟩ := hx
    change ((fr.set r w).rename g).get (g r') = ((fr.rename g).set (g r) w).get (g r')
    rw [Frame.rename_get hg, Frame.get_set, Frame.get_set, Frame.rename_get hg]
    simp only [hg.eq_iff]
  · have hne : x ≠ g r := fun h => hx ⟨r, h.symm⟩
    simp [Frame.rename, hx, hne]

omit [DecidableEq R] [DecidableEq S] in
theorem Frame.readAll_rename (fr : Frame R) (rs : List R) :
    (fr.rename g).readAll (rs.map g) = fr.readAll rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [Frame.readAll, List.map_cons, List.mapM_cons] at ih ⊢
    rw [show (fr.rename g).get (g r) = fr.get r from Frame.rename_get hg fr r, ih]

theorem Frame.writeAll_rename (rs : List R) :
    ∀ (fr : Frame R) (vs : List Word),
      (fr.rename g).writeAll (rs.map g) vs = (fr.writeAll rs vs).map (Frame.rename g) := by
  induction rs with
  | nil => intro fr vs; cases vs <;> rfl
  | cons r rs ih =>
    intro fr vs
    cases vs with
    | nil => rfl
    | cons v vs =>
      simp only [List.map_cons, Frame.writeAll]
      rw [← Frame.rename_set hg, ih]

theorem Prog.enter_rename (p : Prog R) (f : FuncId) (vals : List Word) :
    (p.rename g).enter f vals = (p.enter f vals).map fun x => (x.1, x.2.rename g) := by
  simp only [Prog.enter, Prog.func?_rename]
  cases p.func? f with
  | none => rfl
  | some fn =>
    simp only [Option.map_some, Option.bind_some, Func.rename]
    rw [← Frame.rename_empty (g := g), Frame.writeAll_rename hg]
    cases Frame.empty.writeAll fn.params vals <;> rfl

theorem Prog.start_rename (p : Prog R) (f : FuncId) (args : List Word) (mem : Memory) :
    (p.rename g).start f args mem = (p.start f args mem).map (State.rename g) := by
  simp only [Prog.start, Prog.enter_rename hg]
  cases p.enter f args <;> rfl

/-- **One step of the renamed program is the renamed step.** -/
theorem step_rename (p : Prog R) (s : State R) :
    step (p.rename g) (s.rename g) = (step p s).rename g := by
  have hf := Prog.fetch_rename g p s.point
  have hget := Frame.rename_get hg s.frame
  unfold step
  simp only [State.rename] at hf ⊢
  rw [hf]
  cases hi : p.fetch s.point with
  | none => rfl
  | some i =>
    cases i with
    | nop n => rfl
    | const d v n =>
      simp only [Option.map_some, Instr.rename, Result.rename, State.rename, Frame.rename_set hg]
    | move d src n =>
      simp only [Option.map_some, Instr.rename, hget]
      cases s.frame.get src <;>
        simp [Result.rename, State.rename, Frame.rename_set hg, Point.at]
    | unary op d src n =>
      simp only [Option.map_some, Instr.rename, hget]
      cases s.frame.get src <;>
        simp [Result.rename, State.rename, Frame.rename_set hg, Point.at]
    | binary op d a b n =>
      simp only [Option.map_some, Instr.rename, hget]
      cases s.frame.get a <;> cases s.frame.get b <;> simp only [Result.rename]
      rename_i x y
      cases op.eval x y <;>
        simp [State.rename, Frame.rename_set hg, Point.at]
    | load w e d base off n =>
      simp only [Option.map_some, Instr.rename, hget]
      cases s.frame.get base <;> simp only [Result.rename]
      rename_i a
      cases s.mem.load w e (a.toNat + off) <;>
        simp [State.rename, Frame.rename_set hg, Point.at]
    | store w base off src n =>
      simp only [Option.map_some, Instr.rename, hget]
      cases s.frame.get base <;> cases s.frame.get src <;> simp only [Result.rename]
      rename_i a x
      cases s.mem.store w (a.toNat + off) x <;> simp [State.rename, Point.at]
    | call f args results n =>
      simp only [Option.map_some, Instr.rename, Frame.readAll_rename hg]
      cases s.frame.readAll args with
      | none => rfl
      | some vals =>
        simp only [Prog.enter_rename hg]
        cases p.enter f vals with
        | none => rfl
        | some x => simp [Result.rename, State.rename, Activation.rename]
    | cond c n₁ n₂ =>
      simp only [Option.map_some, Instr.rename, hget]
      cases s.frame.get c <;> simp [Result.rename, State.rename, Point.at]
    | jump t => simp [Instr.rename, Result.rename, State.rename, Point.at]
    | ret regs =>
      simp only [Option.map_some, Instr.rename, Frame.readAll_rename hg]
      cases s.frame.readAll regs with
      | none => rfl
      | some vals =>
        simp only
        cases s.stack with
        | nil => rfl
        | cons a rest =>
          simp only [List.map_cons, Activation.rename, Prog.fetch_rename]
          cases p.fetch a.point with
          | none => rfl
          | some j =>
            cases j <;> try rfl
            rename_i f args results n
            simp only [Option.map_some, Instr.rename, Frame.writeAll_rename hg]
            cases a.frame.writeAll results vals <;>
              simp [Result.rename, State.rename]
    | trap => rfl

theorem Step.rename {p : Prog R} {s t : State R} (h : Step p s t) :
    Step (p.rename g) (s.rename g) (t.rename g) := by
  unfold Step at h ⊢
  rw [step_rename hg, h]
  rfl

theorem Steps.rename {p : Prog R} {s t : State R} (h : Steps p s t) :
    Steps (p.rename g) (s.rename g) (t.rename g) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (hst.rename hg)

theorem behaves_rename {p : Prog R} {s : State R} {b : Behavior} (h : Behaves p s b) :
    Behaves (p.rename g) (s.rename g) b := by
  cases b with
  | returned vs m =>
    obtain ⟨t, ht, hf⟩ := h
    exact ⟨t.rename g, ht.rename hg, by rw [step_rename hg, hf]; rfl⟩
  | trapped m =>
    obtain ⟨t, ht, hf⟩ := h
    exact ⟨t.rename g, ht.rename hg, by rw [step_rename hg, hf]; rfl⟩
  | stuck =>
    obtain ⟨t, ht, hf⟩ := h
    exact ⟨t.rename g, ht.rename hg, by rw [step_rename hg, hf]; rfl⟩
  | diverges => exact InfiniteTrace.map (State.rename g) (fun _ _ h => h.rename hg) h

/-- **Renaming by an injective map preserves and reflects every behaviour.** -/
theorem behaves_rename_iff {p : Prog R} {s : State R} {b : Behavior} :
    Behaves (p.rename g) (s.rename g) b ↔ Behaves p s b := by
  refine ⟨fun h => ?_, behaves_rename hg⟩
  obtain ⟨b₀, hb₀⟩ := Behaves.exists p s
  rw [Behaves.unique h (behaves_rename hg hb₀)]
  exact hb₀

end

end Silmaril.Machine.RTL
