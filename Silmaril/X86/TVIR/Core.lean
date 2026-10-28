module

public import Silmaril.Process.LPS.Problems.Sha256Cli.Leads

/-! # TVIR: a tiny structured IR for translation validation of machine code

Status: **VERIFIED** (no `sorry`, standard axioms only).

Translation validation into a higher-level IR splits a machine-code proof in two:

1. **Source level.** A small structured program `s : Stmt V L` (variables of type `V` holding
   64-bit words, byte loads from a read-only memory, an output primitive `putc`, sequencing,
   conditionals and do-while loops) is proved correct by a weakest-precondition calculus
   (`wp`, sound for total correctness by `wp_sound`). Loops carry their invariant and variant
   as annotations, so `wp` *is* the verification-condition generator.
2. **Translation validation.** `Sim step Ok ro F R R' s` says that the machine (any step
   relation with a safety invariant, in the continuation form of `Sha256Cli.Leads`) follows
   every terminating IR execution of `s`: from a state coupled to `σ` by `R`, every
   execution keeps `Ok` and reaches a state coupled to the IR result `σ'` by `R'`. The
   coupling relations name the registers that hold the IR variables; flags never appear in
   them (`TVIR.Flags` turns a fused `cmp`/`jcc` into an IR condition). `Sim` is proved per
   machine block (leaves) and assembled by the structural rules `Sim.seq`, `Sim.ite`,
   `Sim.loop`, following the IR syntax.

`Sim.leads` composes the two: a correct IR program and its simulation give a `Leads`
segment of the machine.

**Output.** `putc` acts on an abstract output layer (`IOLayer`: a state, a `putc` and the
stream emitted so far). Machine-level output obligations (a buffered `putc` may flush, and
a flush must only write a prefix of the expected output) are discharged from the IR side:
`Sim` is relative to a final output bound `F`, and every IR execution it simulates ends with
its output a prefix of `F` (`Exec.out_prefix`: output only grows). So the machine proof of a
`putc` site may assume that the byte it appends keeps the output a prefix of `F`.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.X86.TVIR

open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)

/-- An output layer: a state, the `putc` primitive, and the byte stream emitted so far. -/
structure IOLayer where
  S : Type
  putc : S → UInt8 → S
  out : S → List UInt8
  out_putc : ∀ s b, out (putc s b) = out s ++ [b]

/-- Machine words. -/
abbrev Word := BitVec 64

/-- Expressions over variables `V`. `ld8 a` is the zero-extended byte at address `a` of the
read-only memory. -/
inductive Exp (V : Type) where
  | var (x : V)
  | lit (n : Word)
  | add (a b : Exp V)
  | sub (a b : Exp V)
  | band (a b : Exp V)
  | shr (a : Exp V) (k : Nat)
  | ld8 (a : Exp V)

/-- Conditions (expressions, not flags). -/
inductive BExp (V : Type) where
  | eq (a b : Exp V)
  | ne (a b : Exp V)
  | ult (a b : Exp V)

/-- An IR state: the variables and the output layer. -/
structure St (V : Type) (L : IOLayer) where
  env : V → Word
  io : L.S

variable {V : Type} {L : IOLayer}

/-- The byte of a word (its low 8 bits). -/
def byteOf (w : Word) : UInt8 := UInt8.ofBitVec (w.setWidth 8)

/-- A byte, zero-extended. -/
def zext (b : UInt8) : Word := b.toBitVec.setWidth 64

def Exp.eval (ro : Nat → UInt8) (env : V → Word) : Exp V → Word
  | .var x => env x
  | .lit n => n
  | .add a b => a.eval ro env + b.eval ro env
  | .sub a b => a.eval ro env - b.eval ro env
  | .band a b => a.eval ro env &&& b.eval ro env
  | .shr a k => a.eval ro env >>> k
  | .ld8 a => zext (ro (a.eval ro env).toNat)

def BExp.eval (ro : Nat → UInt8) (env : V → Word) : BExp V → Bool
  | .eq a b => a.eval ro env == b.eval ro env
  | .ne a b => a.eval ro env != b.eval ro env
  | .ult a b => decide ((a.eval ro env).toNat < (b.eval ro env).toNat)

/-- Statements. `loop inv variant body c` is `do body while c`, annotated with the invariant
`inv` (holding after every execution of `body`) and the variant `variant` (decreasing along
every repetition). The annotations are used by `wp` only. -/
inductive Stmt (V : Type) (L : IOLayer) where
  | skip
  | set (x : V) (e : Exp V)
  | putc (e : Exp V)
  | seq (s t : Stmt V L)
  | ite (c : BExp V) (s t : Stmt V L)
  | loop (inv : St V L → Prop) (variant : St V L → Nat) (body : Stmt V L) (c : BExp V)

variable [DecidableEq V]

/-- Assignment. -/
def St.set (σ : St V L) (x : V) (v : Word) : St V L :=
  { σ with env := Function.update σ.env x v }

/-- Output of one byte. -/
def St.putc (σ : St V L) (b : UInt8) : St V L := { σ with io := L.putc σ.io b }

/-- **Big-step semantics** over the read-only memory `ro`. -/
inductive Exec (ro : Nat → UInt8) : Stmt V L → St V L → St V L → Prop
  | skip (σ : St V L) : Exec ro .skip σ σ
  | set (σ : St V L) (x : V) (e : Exp V) : Exec ro (.set x e) σ (σ.set x (e.eval ro σ.env))
  | putc (σ : St V L) (e : Exp V) : Exec ro (.putc e) σ (σ.putc (byteOf (e.eval ro σ.env)))
  | seq {s t : Stmt V L} {σ σ₁ σ₂ : St V L} : Exec ro s σ σ₁ → Exec ro t σ₁ σ₂ →
      Exec ro (.seq s t) σ σ₂
  | iteT {c : BExp V} {s t : Stmt V L} {σ σ' : St V L} : c.eval ro σ.env = true →
      Exec ro s σ σ' → Exec ro (.ite c s t) σ σ'
  | iteF {c : BExp V} {s t : Stmt V L} {σ σ' : St V L} : c.eval ro σ.env = false →
      Exec ro t σ σ' → Exec ro (.ite c s t) σ σ'
  | loopDone {I : St V L → Prop} {var : St V L → Nat} {body : Stmt V L} {c : BExp V}
      {σ σ₁ : St V L} : Exec ro body σ σ₁ → c.eval ro σ₁.env = false →
      Exec ro (.loop I var body c) σ σ₁
  | loopMore {I : St V L → Prop} {var : St V L → Nat} {body : Stmt V L} {c : BExp V}
      {σ σ₁ σ₂ : St V L} : Exec ro body σ σ₁ → c.eval ro σ₁.env = true →
      Exec ro (.loop I var body c) σ₁ σ₂ → Exec ro (.loop I var body c) σ σ₂

/-- Output only grows. -/
theorem Exec.out_prefix {ro : Nat → UInt8} {s : Stmt V L} {σ σ' : St V L}
    (h : Exec ro s σ σ') : L.out σ.io <+: L.out σ'.io := by
  induction h with
  | skip => exact List.prefix_refl _
  | set => exact List.prefix_refl _
  | putc σ e => simp only [St.putc, L.out_putc]; exact List.prefix_append _ _
  | seq _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | iteT _ _ ih => exact ih
  | iteF _ _ ih => exact ih
  | loopDone _ _ ih => exact ih
  | loopMore _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## Weakest preconditions (the VC generator) -/

/-- **Weakest precondition** for total correctness. For a loop it is the three loop VCs:
the first body execution establishes the invariant; from the invariant with the condition
true, the body re-establishes it with a smaller variant; with the condition false the
invariant implies the postcondition. -/
def wp (ro : Nat → UInt8) : Stmt V L → (St V L → Prop) → St V L → Prop
  | .skip, Q => Q
  | .set x e, Q => fun σ => Q (σ.set x (e.eval ro σ.env))
  | .putc e, Q => fun σ => Q (σ.putc (byteOf (e.eval ro σ.env)))
  | .seq s t, Q => wp ro s (wp ro t Q)
  | .ite c s t, Q => fun σ => if c.eval ro σ.env then wp ro s Q σ else wp ro t Q σ
  | .loop I var body c, Q => fun σ =>
      wp ro body I σ ∧
      (∀ τ, I τ → c.eval ro τ.env = true → wp ro body (fun τ' => I τ' ∧ var τ' < var τ) τ) ∧
      (∀ τ, I τ → c.eval ro τ.env = false → Q τ)

/-- **Soundness of `wp`** (total correctness): the program terminates in a state satisfying
the postcondition. -/
theorem wp_sound (ro : Nat → UInt8) :
    ∀ (s : Stmt V L) (Q : St V L → Prop) (σ : St V L), wp ro s Q σ →
      ∃ σ', Exec ro s σ σ' ∧ Q σ'
  | .skip, _, σ, h => ⟨σ, .skip σ, h⟩
  | .set x e, _, σ, h => ⟨_, .set σ x e, h⟩
  | .putc e, _, σ, h => ⟨_, .putc σ e, h⟩
  | .seq s t, Q, σ, h => by
    obtain ⟨σ₁, e₁, h₁⟩ := wp_sound ro s _ σ h
    obtain ⟨σ₂, e₂, h₂⟩ := wp_sound ro t Q σ₁ h₁
    exact ⟨σ₂, .seq e₁ e₂, h₂⟩
  | .ite c s t, Q, σ, h => by
    simp only [wp] at h
    cases hc : c.eval ro σ.env
    · rw [hc] at h
      obtain ⟨σ', e, hq⟩ := wp_sound ro t Q σ (by simpa using h)
      exact ⟨σ', .iteF hc e, hq⟩
    · rw [hc] at h
      obtain ⟨σ', e, hq⟩ := wp_sound ro s Q σ (by simpa using h)
      exact ⟨σ', .iteT hc e, hq⟩
  | .loop I var body c, Q, σ, ⟨h₀, hstep, hexit⟩ => by
    -- from every invariant state, the remaining loop terminates in `Q`
    have rest : ∀ n τ, var τ = n → I τ →
        (c.eval ro τ.env = false → ∃ σ', Exec ro (.loop I var body c) τ σ' ∧ Q σ' ∨ True) ∧
        (c.eval ro τ.env = true → ∃ σ', Exec ro (.loop I var body c) τ σ' ∧ Q σ') := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro τ hn hi
        refine ⟨fun _ => ⟨τ, Or.inr trivial⟩, fun hc => ?_⟩
        obtain ⟨τ₁, e₁, hi₁, hlt⟩ := wp_sound ro body _ τ (hstep τ hi hc)
        cases hc₁ : c.eval ro τ₁.env
        · exact ⟨τ₁, .loopDone e₁ hc₁, hexit τ₁ hi₁ hc₁⟩
        · obtain ⟨σ', e', hq⟩ := (ih (var τ₁) (hn ▸ hlt) τ₁ rfl hi₁).2 hc₁
          exact ⟨σ', .loopMore e₁ hc₁ e', hq⟩
    obtain ⟨σ₁, e₁, hi₁⟩ := wp_sound ro body I σ h₀
    cases hc₁ : c.eval ro σ₁.env
    · exact ⟨σ₁, .loopDone e₁ hc₁, hexit σ₁ hi₁ hc₁⟩
    · obtain ⟨σ', e', hq⟩ := (rest _ σ₁ rfl hi₁).2 hc₁
      exact ⟨σ', .loopMore e₁ hc₁ e', hq⟩

/-- `wp` is monotone in the postcondition. -/
theorem wp_mono (ro : Nat → UInt8) :
    ∀ (s : Stmt V L) {Q Q' : St V L → Prop}, (∀ σ, Q σ → Q' σ) → ∀ σ, wp ro s Q σ →
      wp ro s Q' σ
  | .skip, _, _, h, σ, hq => h σ hq
  | .set _ _, _, _, h, _, hq => h _ hq
  | .putc _, _, _, h, _, hq => h _ hq
  | .seq s t, _, _, h, σ, hq => wp_mono ro s (wp_mono ro t h) σ hq
  | .ite c s t, _, _, h, σ, hq => by
    simp only [wp] at hq ⊢
    split <;> rename_i hc <;> simp only [hc] at hq
    · exact wp_mono ro s h σ hq
    · exact wp_mono ro t h σ hq
  | .loop _ _ _ _, _, _, h, _, ⟨h₀, hs, he⟩ => ⟨h₀, hs, fun τ hi hc => h τ (he τ hi hc)⟩

/-! ## Simulation of IR statements by a machine -/

section Sim

variable {X E : Type} (step : X → List E → X → Prop) (Ok : X → List E → Prop)

/-- **The machine simulates `s`** from coupling `R` to coupling `R'`, for runs whose output
stays a prefix of `F`: for every terminating IR execution `σ → σ'` with output a prefix of
`F`, every machine execution from a state coupled to `σ` keeps `Ok` and reaches a state
coupled to `σ'` (continuation form: any goal `K` that holds there holds from the start). -/
def Sim (ro : Nat → UInt8) (F : List UInt8) (R R' : St V L → X → List E → Prop)
    (s : Stmt V L) : Prop :=
  ∀ σ σ', Exec ro s σ σ' → L.out σ'.io <+: F → ∀ (K : X → List E → Prop) (x : X) (h : List E),
    R σ x h → (∀ x' h', R' σ' x' h' → Leads step Ok K x' h') → Leads step Ok K x h

/-- **A machine branch** on an IR condition: from a state coupled by `R`, every execution
keeps `Ok` and reaches a state coupled by `Rt` if the condition holds, by `Rf` if not; the
IR state is unchanged. A fused `cmp`/`jcc` pair is the typical instance. -/
def Branch (ro : Nat → UInt8) (R : St V L → X → List E → Prop) (c : BExp V)
    (Rt Rf : St V L → X → List E → Prop) : Prop :=
  ∀ σ (K : X → List E → Prop) (x : X) (h : List E), R σ x h →
    (c.eval ro σ.env = true → ∀ x' h', Rt σ x' h' → Leads step Ok K x' h') →
    (c.eval ro σ.env = false → ∀ x' h', Rf σ x' h' → Leads step Ok K x' h') →
    Leads step Ok K x h

variable {step Ok} {ro : Nat → UInt8} {F : List UInt8}

/-- Sequencing. -/
theorem Sim.seq {R R₁ R₂ : St V L → X → List E → Prop} {s t : Stmt V L}
    (h₁ : Sim step Ok ro F R R₁ s) (h₂ : Sim step Ok ro F R₁ R₂ t) :
    Sim step Ok ro F R R₂ (.seq s t) := by
  intro σ σ' e hF K x h hr k
  cases e with
  | seq e₁ e₂ =>
    exact h₁ _ _ e₁ ((Exec.out_prefix e₂).trans hF) K x h hr fun x' h' hr' =>
      h₂ _ _ e₂ hF K x' h' hr' k

/-- `skip` is simulated by doing nothing. -/
theorem Sim.skip (R : St V L → X → List E → Prop) : Sim step Ok ro F R R .skip := by
  intro σ σ' e _ K x h hr k
  cases e; exact k x h hr

/-- Consequence: a stronger precondition coupling, a weaker postcondition coupling. -/
theorem Sim.conseq {R R' P P' : St V L → X → List E → Prop} {s : Stmt V L}
    (hs : Sim step Ok ro F R R' s) (hp : ∀ σ x h, P σ x h → R σ x h)
    (hq : ∀ σ x h, R' σ x h → P' σ x h) : Sim step Ok ro F P P' s :=
  fun σ σ' e hF K x h hr k => hs σ σ' e hF K x h (hp σ x h hr) fun x' h' r => k x' h' (hq _ _ _ r)

/-- Conditionals: a machine branch, then the two arms. -/
theorem Sim.ite {R Rt Rf R' : St V L → X → List E → Prop} {c : BExp V} {s t : Stmt V L}
    (hb : Branch step Ok ro R c Rt Rf) (hs : Sim step Ok ro F Rt R' s)
    (ht : Sim step Ok ro F Rf R' t) : Sim step Ok ro F R R' (.ite c s t) := by
  intro σ σ' e hF K x h hr k
  cases e with
  | iteT hc e =>
    exact hb σ K x h hr (fun _ x' h' r => hs σ σ' e hF K x' h' r k)
      (fun hc' => absurd (hc.symm.trans hc') (by simp))
  | iteF hc e =>
    exact hb σ K x h hr (fun hc' => absurd (hc.symm.trans hc') (by simp))
      (fun _ x' h' r => ht σ σ' e hF K x' h' r k)

/-- **Do-while loops**: the body from the loop head `Rh` to the test point `Rt`, and a machine
branch at the test point back to the head (condition true) or out (`Rx`). -/
theorem Sim.loop {Rh Rt Rx : St V L → X → List E → Prop} {I : St V L → Prop}
    {var : St V L → Nat} {body : Stmt V L} {c : BExp V}
    (hb : Sim step Ok ro F Rh Rt body) (ht : Branch step Ok ro Rt c Rh Rx) :
    Sim step Ok ro F Rh Rx (.loop I var body c) := by
  intro σ σ' e
  generalize hl : (Stmt.loop I var body c : Stmt V L) = sl at e
  induction e with
  | loopDone e₁ hc =>
    cases hl
    intro hF K x h hr k
    exact hb _ _ e₁ hF K x h hr fun x' h' r =>
      ht _ K x' h' r (fun hc' => absurd (hc.symm.trans hc') (by simp)) (fun _ => k)
  | loopMore e₁ hc e₂ _ ih =>
    cases hl
    intro hF K x h hr k
    exact hb _ _ e₁ ((Exec.out_prefix e₂).trans hF) K x h hr fun x' h' r =>
      ht _ K x' h' r (fun _ x'' h'' r' => ih rfl hF K x'' h'' r' k)
        (fun hc' => absurd (hc.symm.trans hc') (by simp))
  | _ => cases hl

/-- **Composition**: a simulation and a correct IR program give a machine segment. If the
IR program, from `σ`, terminates in a state satisfying `Q`, and every such state has its
output a prefix of `F`, then from every machine state coupled to `σ`, every execution keeps
`Ok` and reaches a machine state coupled to some IR final state satisfying `Q`. -/
theorem Sim.leads {R R' : St V L → X → List E → Prop} {s : Stmt V L}
    (hs : Sim step Ok ro F R R' s) {Q : St V L → Prop} {σ : St V L} (hw : wp ro s Q σ)
    (hF : ∀ σ', Q σ' → L.out σ'.io <+: F) {x : X} {h : List E} (hr : R σ x h) :
    Leads step Ok (fun x' h' => ∃ σ', Q σ' ∧ R' σ' x' h') x h := by
  obtain ⟨σ', e, hq⟩ := wp_sound ro s Q σ hw
  exact hs σ σ' e (hF σ' hq) _ x h hr fun x' h' r => .done ⟨σ', hq, r⟩

end Sim

end Silmaril.X86.TVIR
