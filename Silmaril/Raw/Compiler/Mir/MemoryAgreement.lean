module

public import Silmaril.Compiler.Mir.Semantics.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false
@[expose] public section

/-! # Inaccessible bytes do not affect Lir stuckness -/

namespace Silmaril.Machine.Lir

def Memory.Agrees (m m' : Memory) : Prop :=
  m.size = m'.size ∧ ∀ a < m.size, m.bytes a = m'.bytes a

private theorem readLE_agrees (m m' : Memory) (h : m.Agrees m') (a n : Nat)
    (hn : a+n ≤ m.size) : readLE m.bytes a n = readLE m'.bytes a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => rw [readLE, readLE, h.2 a (by omega), ih (a+1) (by omega)]

theorem Memory.load_agrees (m m' : Memory) (h : m.Agrees m') (w : Width) (e : Ext) (a : Nat) :
    m.load w e a = m'.load w e a := by
  by_cases hb : a+w.bytes ≤ m.size
  · have hb' : a+w.bytes ≤ m'.size := by simpa [← h.1] using hb
    simp only [Memory.load, Memory.InBounds, hb, hb', ite_true]
    rw [readLE_agrees m m' h a w.bytes hb]
  · have hb' : ¬ a+w.bytes ≤ m'.size := by simpa [← h.1] using hb
    simp [Memory.load, Memory.InBounds, hb, hb']

private def StoreAgrees : Option Memory → Option Memory → Prop
  | none, none => True
  | some m, some m' => m.Agrees m'
  | _, _ => False

private theorem store_agrees (m m' : Memory) (h : m.Agrees m') (w : Width) (a : Nat) (v : Word) :
    StoreAgrees (m.store w a v) (m'.store w a v) := by
  by_cases hb : a+w.bytes ≤ m.size
  · have hb' : a+w.bytes ≤ m'.size := by simpa [← h.1] using hb
    simp only [Memory.store, Memory.InBounds, hb, hb', ite_true, StoreAgrees, Memory.Agrees]
    refine ⟨h.1, ?_⟩
    intro b hb
    unfold writeLE
    split
    · rfl
    · exact h.2 b hb
  · have hb' : ¬ a+w.bytes ≤ m'.size := by simpa [← h.1] using hb
    simp [Memory.store, Memory.InBounds, hb, hb', StoreAgrees]

private def ExecAgrees : Option (Frame Nat × Memory) → Option (Frame Nat × Memory) → Prop
  | none, none => True
  | some (fr,m), some (fr',m') => fr = fr' ∧ m.Agrees m'
  | _, _ => False

private theorem exec_agrees (o : Op Nat) (fr : Frame Nat) (m m' : Memory) (hm : m.Agrees m') :
    ExecAgrees (o.exec fr m) (o.exec fr m') := by
  cases o with
  | const d v => exact ⟨rfl,hm⟩
  | move d s => cases h : fr.get s <;> simp [Op.exec, h, ExecAgrees, hm]
  | unary op d s => cases h : fr.get s <;> simp [Op.exec, h, ExecAgrees, hm]
  | binary op d a b =>
    cases ha : fr.get a <;> cases hb : fr.get b <;> simp [Op.exec, ha, hb, ExecAgrees]
    rename_i x y
    cases he : op.eval x y <;> simp [hm]
  | load w e d base off =>
    cases ha : fr.get base <;> simp [Op.exec, ha, ExecAgrees]
    rename_i x
    rw [Memory.load_agrees m m' hm]
    cases he : m'.load w e (x.toNat+off) <;> simp [hm]
  | store w base off src =>
    cases ha : fr.get base <;> cases hx : fr.get src <;> simp [Op.exec, ha, hx, ExecAgrees]
    rename_i a v
    have hs := store_agrees m m' hm w (a.toNat+off) v
    cases h₁ : m.store w (a.toNat+off) v <;> cases h₂ : m'.store w (a.toNat+off) v <;>
      simp_all only [StoreAgrees, Option.map_none, Option.map_some, true_and]
  | slotGet d n => cases h : fr.slots n <;> simp [Op.exec, h, ExecAgrees, hm]
  | slotSet n s => cases h : fr.get s <;> simp [Op.exec, h, ExecAgrees, hm]

def State.Agrees (s s' : State Nat) : Prop :=
  s.point = s'.point ∧ s.frame = s'.frame ∧ s.stack = s'.stack ∧ s.mem.Agrees s'.mem

private def ResultAgrees : Result Nat → Result Nat → Prop
  | .running s, .running s' => s.Agrees s'
  | .returned vs m, .returned vs' m' => vs = vs' ∧ m.Agrees m'
  | .trapped m, .trapped m' => m.Agrees m'
  | .stuck, .stuck => True
  | _, _ => False

private theorem step_agrees (p : Prog Nat) (s s' : State Nat) (h : s.Agrees s') :
    ResultAgrees (step p s) (step p s') := by
  rcases s with ⟨pt,fr,stack,mem⟩
  rcases s' with ⟨pt',fr',stack',mem'⟩
  obtain ⟨rfl,rfl,rfl,hm⟩ := h
  dsimp only at hm
  simp only [step]
  cases hf : p.fetch pt with
  | none => trivial
  | some c =>
    cases c with
    | instr i =>
      cases i with
      | op o =>
        have he := exec_agrees o fr mem mem' hm
        cases h₁ : o.exec fr mem <;> cases h₂ : o.exec fr mem' <;>
          simp_all only [ExecAgrees, ResultAgrees, State.Agrees]
        rename_i x y
        rcases x with ⟨fr₁,m₁⟩
        rcases y with ⟨fr₂,m₂⟩
        simp only [true_and]
      | call f args results =>
        cases hv : fr.readAll args <;> simp [hv, ResultAgrees]
        rename_i vs
        cases he : p.enter f vs <;> simp [State.Agrees, hm]
      | fop op d a b =>
        cases he : op.exec d a b fr <;> simp [he, ResultAgrees, State.Agrees, hm]
    | term t =>
      cases t with
      | jump l => exact ⟨rfl,rfl,rfl,hm⟩
      | branch c l₁ l₂ =>
        cases hc : fr.get c <;> simp [hc, ResultAgrees, State.Agrees, hm]
      | trap => exact hm
      | ret locs =>
        cases hv : fr.readAll locs <;> simp [hv, ResultAgrees]
        cases stack with
        | nil => simp [hm]
        | cons a rest =>
          try dsimp only
          cases hc : p.fetch a.point with
          | none => simp
          | some c =>
            cases c with
            | term t => simp
            | instr i =>
              cases i with
              | op o => simp
              | fop op d a b => simp
              | call f args results =>
                rename_i vs
                cases hw : a.frame.writeAll results vs <;>
                  simp [hw, State.Agrees, hm]

/-- Changing inaccessible bytes cannot change a stuck finite run. -/
theorem run_stuck_of_agrees (p : Prog Nat) (n : Nat) :
    ∀ (s s' : State Nat), s.Agrees s' → run p n s = .stuck → run p n s' = .stuck := by
  induction n with
  | zero => intro s s' _ h; cases h
  | succ n ih =>
    intro s s' h hr
    have he := step_agrees p s s' h
    cases h₁ : step p s <;> cases h₂ : step p s' <;>
      simp_all only [run, ResultAgrees]
    exact ih _ _ he hr

end Silmaril.Machine.Lir
