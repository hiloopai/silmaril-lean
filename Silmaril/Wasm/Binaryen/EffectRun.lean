module

public import Silmaril.Wasm.Binaryen.Joinable
public import Silmaril.Wasm.Execution.Core.Soundness

@[expose] public section

/-! # Runs of effect-bounded code

Core 3.0 invariants on administrative code, used by the effect soundness
theorems of `Binaryen/Effects.lean`. Each is preserved by every `Step`:

* `AdmsLab S`: every free branch target of the code satisfies `S` (frames are
  opaque: labels never cross them). Used for `effects_control_br` and by the
  bottom invariant.
* `AdmsBot`: the code contains an instruction that can never fall through, so
  no run reaches plain values (`isBot_sound`).
* `AdmsB b S`: the code stays inside an effect budget `b` (the locals and
  globals it may write, whether it may call, trap, loop or return), with branch
  targets in `S`. `Step.bud` shows that a step keeps the budget, writes only
  budgeted locals and globals, and, without calls or loops, strictly decreases
  the size `aszs`: such code terminates.

`pure_run` combines the budget with Core 3.0 progress and preservation
(`Soundness/ProgressControl.lean`, `Soundness/Preservation.lean`): budgeted
code without writes, calls, traps, loops or escaping branches runs to values.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Numerics Validation

variable {H : Type}

/-! ## Label predicates -/

/-- A label predicate seen from inside one more label binder. -/
def shiftP (S : Nat → Prop) : Nat → Prop
  | 0 => True
  | n + 1 => S n

@[simp] theorem shiftP_zero (S : Nat → Prop) : shiftP S 0 = True := rfl
@[simp] theorem shiftP_succ (S : Nat → Prop) (n : Nat) : shiftP S (n + 1) = S n := rfl

theorem shiftP_pred {S : Nat → Prop} {k : Nat} (hk : 0 < k) (h : shiftP S k) : S (k - 1) := by
  cases k with
  | zero => omega
  | succ k => simpa using h

theorem mem_unbind {ns : List Nat} {n : Nat} : n ∈ unbind ns ↔ n + 1 ∈ ns := by
  simp only [unbind, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, h⟩
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      have e : a = n + 1 := by omega
      subst e
      exact ha
  · intro h
    exact ⟨n + 1, h, by simp⟩

theorem shiftP_of_unbind {S : Nat → Prop} {ns : List Nat} (h : ∀ n ∈ unbind ns, S n) :
    ∀ n ∈ ns, shiftP S n
  | 0, _ => trivial
  | n + 1, hn => h n (mem_unbind.mpr hn)

@[simp] theorem labelPred_toNat (l : LabelIdx) : (labelPred l).toNat = l.toNat - 1 := rfl

/-! ## Free labels of Core instructions -/

theorem flatMap_attach_val {α β : Type} (l : List α) (f : α → List β) :
    (l.attach.flatMap fun i => f i.val) = l.flatMap f := by
  conv_rhs => rw [← List.attach_map_subtype_val l]
  rw [List.flatMap_map]

@[simp] theorem instrsLabels_nil : instrsLabels [] = [] := rfl

@[simp] theorem instrsLabels_cons (i : Instr) (is : List Instr) :
    instrsLabels (i :: is) = instrLabels i ++ instrsLabels is := by
  simp [instrsLabels]

theorem mem_instrsLabels {is : List Instr} {n : Nat} :
    n ∈ instrsLabels is ↔ ∃ i ∈ is, n ∈ instrLabels i := by
  simp [instrsLabels, List.mem_flatMap]

theorem instrLabels_block (bt : BlockType) (body : List Instr) :
    instrLabels (.block bt body) = unbind (instrsLabels body) := by
  rw [instrLabels.eq_def]
  simp only [flatMap_attach_val, instrsLabels]

theorem instrLabels_loop (bt : BlockType) (body : List Instr) :
    instrLabels (.loop bt body) = unbind (instrsLabels body) := by
  rw [instrLabels.eq_def]
  simp only [flatMap_attach_val, instrsLabels]

theorem instrLabels_if (bt : BlockType) (t e : List Instr) :
    instrLabels (.if_ bt t e) = unbind (instrsLabels t ++ instrsLabels e) := by
  rw [instrLabels.eq_def]
  simp only [flatMap_attach_val, instrsLabels]

theorem instrLabels_tryTable (bt : BlockType) (cs : List Catch) (body : List Instr) :
    instrLabels (.tryTable bt cs body) = cs.map Catch.label ++ unbind (instrsLabels body) := by
  rw [instrLabels.eq_def]
  simp only [flatMap_attach_val, instrsLabels]

@[simp] theorem instrLabels_br (l : LabelIdx) : instrLabels (.br l) = [l.toNat] := by
  unfold instrLabels; rfl

@[simp] theorem instrLabels_brIf (l : LabelIdx) : instrLabels (.brIf l) = [l.toNat] := by
  unfold instrLabels; rfl

@[simp] theorem instrLabels_brTable (ls : List LabelIdx) (d : LabelIdx) :
    instrLabels (.brTable ls d) = d.toNat :: ls.map Idx.toNat := by
  unfold instrLabels; rfl

@[simp] theorem instrLabels_brOnNull (l : LabelIdx) : instrLabels (.brOnNull l) = [l.toNat] := by
  unfold instrLabels; rfl

@[simp] theorem instrLabels_brOnNonNull (l : LabelIdx) :
    instrLabels (.brOnNonNull l) = [l.toNat] := by
  unfold instrLabels; rfl

@[simp] theorem instrLabels_brOnCast (l : LabelIdx) (r₁ r₂ : RefType) :
    instrLabels (.brOnCast l r₁ r₂) = [l.toNat] := by
  unfold instrLabels; rfl

@[simp] theorem instrLabels_brOnCastFail (l : LabelIdx) (r₁ r₂ : RefType) :
    instrLabels (.brOnCastFail l r₁ r₂) = [l.toNat] := by
  unfold instrLabels; rfl

@[simp] theorem instrLabels_return : instrLabels .return_ = [] := by
  unfold instrLabels; rfl

@[simp] theorem instrLabels_returnCall (x : FuncIdx) : instrLabels (.returnCall x) = [] := by
  unfold instrLabels; rfl

@[simp] theorem instrLabels_returnCallRef (x : TypeIdx) :
    instrLabels (.returnCallRef x) = [] := by
  unfold instrLabels; rfl

@[simp] theorem instrLabels_returnCallIndirect (x : TableIdx) (y : TypeIdx) :
    instrLabels (.returnCallIndirect x y) = [] := by
  unfold instrLabels; rfl

/-- Flat instructions have no labels. -/
theorem instrLabels_of_flat {i : Instr} (h : i.flat = true) : instrLabels i = [] := by
  rw [instrLabels.eq_def]
  split <;> simp_all [Instr.flat]

/-! ## Free labels of administrative code -/

mutual
/-- Every free branch target of an administrative instruction satisfies `S`. -/
def AdmLab (S : Nat → Prop) : Admin → Prop
  | .plain i => ∀ n ∈ instrLabels i, S n
  | .ref _ => True
  | .callRefType _ => True
  | .returnCallRefType _ => True
  | .label _ cont body => (∀ n ∈ instrsLabels cont, S n) ∧ AdmsLab (shiftP S) body
  | .handler _ cs body => (∀ c ∈ cs, S (Catch.label c)) ∧ AdmsLab S body
  | .frame _ _ _ => True
  | .trap => True
/-- `AdmLab` on a sequence. -/
def AdmsLab (S : Nat → Prop) : List Admin → Prop
  | [] => True
  | a :: as => AdmLab S a ∧ AdmsLab S as
end

@[simp] theorem AdmsLab_nil (S : Nat → Prop) : AdmsLab S [] ↔ True := Iff.rfl

@[simp] theorem AdmsLab_cons (S : Nat → Prop) (a : Admin) (as : List Admin) :
    AdmsLab S (a :: as) ↔ AdmLab S a ∧ AdmsLab S as := Iff.rfl

@[simp] theorem AdmLab_plain (S : Nat → Prop) (i : Instr) :
    AdmLab S (.plain i) ↔ ∀ n ∈ instrLabels i, S n := Iff.rfl

@[simp] theorem AdmLab_label (S : Nat → Prop) (k : Nat) (cont : List Instr) (body : List Admin) :
    AdmLab S (.label k cont body) ↔ (∀ n ∈ instrsLabels cont, S n) ∧ AdmsLab (shiftP S) body :=
  Iff.rfl

@[simp] theorem AdmLab_handler (S : Nat → Prop) (k : Nat) (cs : List Catch) (body : List Admin) :
    AdmLab S (.handler k cs body) ↔ (∀ c ∈ cs, S (Catch.label c)) ∧ AdmsLab S body := Iff.rfl

@[simp] theorem AdmLab_ref (S : Nat → Prop) (r : Ref) : AdmLab S (.ref r) := trivial
@[simp] theorem AdmLab_callRefType (S : Nat → Prop) (d : DefType) : AdmLab S (.callRefType d) :=
  trivial
@[simp] theorem AdmLab_returnCallRefType (S : Nat → Prop) (d : DefType) :
    AdmLab S (.returnCallRefType d) := trivial
@[simp] theorem AdmLab_frame (S : Nat → Prop) (k : Nat) (fr : Frame) (body : List Admin) :
    AdmLab S (.frame k fr body) := trivial
@[simp] theorem AdmLab_trap (S : Nat → Prop) : AdmLab S .trap := trivial

@[simp] theorem AdmsLab_append (S : Nat → Prop) :
    ∀ l₁ l₂ : List Admin, AdmsLab S (l₁ ++ l₂) ↔ AdmsLab S l₁ ∧ AdmsLab S l₂
  | [], _ => by simp
  | a :: l₁, l₂ => by simp [AdmsLab_append S l₁ l₂, and_assoc]

theorem AdmsLab_mem {S : Nat → Prop} :
    ∀ {l : List Admin}, AdmsLab S l → ∀ {a : Admin}, a ∈ l → AdmLab S a
  | [], _, _, ha => absurd ha List.not_mem_nil
  | _ :: _, h, _, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h.1
    · exact AdmsLab_mem h.2 ha

theorem AdmLab_of_flat (S : Nat → Prop) {a : Admin} (h : a.flat = true) : AdmLab S a := by
  cases a with
  | plain i =>
    simp only [Admin.flat_plain] at h
    simp [instrLabels_of_flat h]
  | label => simp [Admin.flat] at h
  | handler => simp [Admin.flat] at h
  | frame => simp [Admin.flat] at h
  | _ => simp

@[simp] theorem AdmLab_val (S : Nat → Prop) (v : Val) : AdmLab S v.toAdmin :=
  AdmLab_of_flat S (Val.toAdmin_flat v)

@[simp] theorem AdmLab_constI32 (S : Nat → Prop) (c : BitVec 32) : AdmLab S (constI32 c) :=
  AdmLab_val S _

@[simp] theorem AdmsLab_vals (S : Nat → Prop) : ∀ vs : List Val, AdmsLab S (vals vs)
  | [] => trivial
  | v :: vs => (AdmsLab_cons S _ _).mpr ⟨AdmLab_val S v, AdmsLab_vals S vs⟩

theorem AdmsLab_of_allFlat (S : Nat → Prop) : ∀ {l : List Admin}, AllFlat l → AdmsLab S l
  | [], _ => trivial
  | a :: l, h => by
    simp only [AllFlat, List.all_cons, Bool.and_eq_true] at h
    exact (AdmsLab_cons S _ _).mpr ⟨AdmLab_of_flat S h.1, AdmsLab_of_allFlat S h.2⟩

@[simp] theorem AdmsLab_expression (S : Nat → Prop) :
    ∀ is : List Instr, AdmsLab S (expression is) ↔ ∀ n ∈ instrsLabels is, S n
  | [] => by simp [expression]
  | i :: is => by
    have ih := AdmsLab_expression S is
    simp only [expression, List.map_cons, AdmsLab_cons, AdmLab_plain, instrsLabels_cons,
      List.mem_append] at ih ⊢
    rw [ih]
    constructor
    · rintro ⟨h1, h2⟩ n (hn | hn)
      · exact h1 n hn
      · exact h2 n hn
    · intro h
      exact ⟨fun n hn => h n (.inl hn), fun n hn => h n (.inr hn)⟩

theorem isCallRef_cases {c : Admin} (h : c.IsCallRef) :
    (∃ y, c = .plain (.callRef y)) ∨ ∃ d, c = .callRefType d := by
  unfold Admin.IsCallRef at h
  split at h <;> simp_all

theorem isReturnCallRef_cases {c : Admin} (h : c.IsReturnCallRef) :
    (∃ y, c = .plain (.returnCallRef y)) ∨ ∃ d, c = .returnCallRefType d := by
  unfold Admin.IsReturnCallRef at h
  split at h <;> simp_all

theorem retToCallIn_cases {c : Admin} (h : c.IsReturnCallRef) (m : ModuleInst) :
    (∃ y, c.retToCallIn m = .plain (.callRef y)) ∨ ∃ d, c.retToCallIn m = .callRefType d := by
  rcases isReturnCallRef_cases h with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · simp only [Admin.retToCallIn]
    split
    · exact .inr ⟨_, rfl⟩
    · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, rfl⟩

theorem AdmLab_retCall (S : Nat → Prop) {c : Admin} (h : c.IsReturnCallRef) : AdmLab S c := by
  rcases isReturnCallRef_cases h with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;> simp

theorem AdmLab_retToCallIn (S : Nat → Prop) {c : Admin} (h : c.IsReturnCallRef)
    (m : ModuleInst) : AdmLab S (c.retToCallIn m) := by
  rcases retToCallIn_cases h m with ⟨y, e⟩ | ⟨d, e⟩ <;> rw [e]
  · simp [instrLabels_of_flat (i := .callRef y) rfl]
  · simp

theorem AdmsLab_result (S : Nat → Prop) (r : Result) : AdmsLab S r.toAdmin := by
  cases r with
  | values vs => exact AdmsLab_vals S vs
  | throw a => simp [Result.toAdmin, instrLabels_of_flat (i := .throwRef) rfl]
  | trap => simp [Result.toAdmin]

/-- **Free labels are preserved.** A step never introduces a free branch target
that is not already free in the code (up to the shifts of entered labels). -/
theorem Step.admsLab {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') : ∀ {S : Nat → Prop}, AdmsLab S c.code → AdmsLab S c'.code := by
  induction h with
  | parametric h => intro S _; exact AdmsLab_of_allFlat S h.allFlat.2
  | numeric h => intro S _; exact AdmsLab_of_allFlat S h.allFlat.2
  | vector h => intro S _; exact AdmsLab_of_allFlat S h.allFlat.2
  | «variable» h =>
    intro S _
    cases h <;> simp [instrLabels_of_flat (i := .localSet _) rfl]
  | table h => intro S _; exact AdmsLab_of_allFlat S h.allFlat.2
  | memory h => intro S _; exact AdmsLab_of_allFlat S h.allFlat.2
  | reference h => intro S _; exact AdmsLab_of_allFlat S h.allFlat.2
  | aggregate h => intro S _; exact AdmsLab_of_allFlat S h.allFlat.2
  | ctxtInstrs _ _ ih =>
    intro S hl
    simp only [AdmsLab_append, AdmsLab_vals, true_and] at hl ⊢
    exact ⟨ih hl.1, hl.2⟩
  | ctxtLabel _ ih =>
    intro S hl
    simp only [AdmsLab_cons, AdmsLab_nil, and_true, AdmLab_label] at hl ⊢
    exact ⟨hl.1, ih hl.2⟩
  | ctxtHandler _ ih =>
    intro S hl
    simp only [AdmsLab_cons, AdmsLab_nil, and_true, AdmLab_handler] at hl ⊢
    exact ⟨hl.1, ih hl.2⟩
  | ctxtFrame => intro S _; simp
  | block =>
    intro S hl
    simp only [AdmsLab_append, AdmsLab_vals, AdmsLab_cons, AdmsLab_nil, and_true, true_and,
      AdmLab_plain, AdmLab_label, instrLabels_block, AdmsLab_expression] at hl ⊢
    exact ⟨by simp, shiftP_of_unbind hl⟩
  | loop =>
    intro S hl
    simp only [AdmsLab_append, AdmsLab_vals, AdmsLab_cons, AdmsLab_nil, and_true, true_and,
      AdmLab_plain, AdmLab_label, instrLabels_loop, AdmsLab_expression, instrsLabels_cons,
      instrsLabels_nil, List.append_nil] at hl ⊢
    exact ⟨hl, shiftP_of_unbind hl⟩
  | ifTrue =>
    intro S hl
    simp only [AdmsLab_cons, AdmsLab_nil, and_true, AdmLab_constI32, true_and, AdmLab_plain,
      instrLabels_if, instrLabels_block] at hl ⊢
    intro n hn
    exact hl n (mem_unbind.mpr (List.mem_append_left _ (mem_unbind.mp hn)))
  | ifFalse =>
    intro S hl
    simp only [AdmsLab_cons, AdmsLab_nil, and_true, AdmLab_constI32, true_and, AdmLab_plain,
      instrLabels_if, instrLabels_block] at hl ⊢
    intro n hn
    exact hl n (mem_unbind.mpr (List.mem_append_right _ (mem_unbind.mp hn)))
  | labelVals => intro S _; exact AdmsLab_vals S _
  | brLabelZero =>
    intro S hl
    simp only [AdmsLab_cons, AdmsLab_nil, and_true, AdmLab_label] at hl
    simp only [AdmsLab_append, AdmsLab_vals, true_and, AdmsLab_expression]
    exact hl.1
  | brLabelSucc hl0 =>
    intro S hl
    simp only [AdmsLab_cons, AdmsLab_nil, and_true, AdmLab_label, AdmsLab_append,
      AdmsLab_vals, true_and, AdmLab_plain, instrLabels_br, List.mem_singleton,
      forall_eq] at hl
    simp only [AdmsLab_append, AdmsLab_vals, true_and, AdmsLab_cons, AdmsLab_nil, and_true,
      AdmLab_plain, instrLabels_br, List.mem_singleton, forall_eq, labelPred_toNat]
    exact shiftP_pred hl0 hl.2.1
  | brHandler =>
    intro S hl
    simp only [AdmsLab_cons, AdmsLab_nil, and_true, AdmLab_handler, AdmsLab_append,
      AdmsLab_vals, true_and] at hl
    simp only [AdmsLab_append, AdmsLab_vals, true_and, AdmsLab_cons, AdmsLab_nil, and_true]
    exact hl.2.1
  | brTableLt hi =>
    intro S hl
    simp only [AdmsLab_cons, AdmsLab_nil, and_true, AdmLab_constI32, true_and, AdmLab_plain,
      instrLabels_brTable, instrLabels_br, List.mem_singleton, forall_eq] at hl ⊢
    exact hl _ (List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_of_getElem? hi)))
  | brTableGe =>
    intro S hl
    simp only [AdmsLab_cons, AdmsLab_nil, and_true, AdmLab_constI32, true_and, AdmLab_plain,
      instrLabels_brTable, instrLabels_br, List.mem_singleton, forall_eq] at hl ⊢
    exact hl _ List.mem_cons_self
  | callRefHost => intro S _; exact AdmsLab_result S _
  | callRefHostDiv => intro S hl; exact hl
  | returnCallRefLabel hc =>
    intro S _
    simp only [AdmsLab_append, AdmsLab_vals, true_and, AdmsLab_cons, AdmsLab_nil, and_true]
    exact AdmLab_retCall S hc
  | returnCallRefHandler hc =>
    intro S _
    simp only [AdmsLab_append, AdmsLab_vals, true_and, AdmsLab_cons, AdmsLab_nil, and_true]
    exact AdmLab_retCall S hc
  | returnCallRefFrameAddr hc =>
    intro S _
    simp only [AdmsLab_append, AdmsLab_vals, true_and, AdmsLab_cons, AdmsLab_nil, and_true,
      AdmLab_ref]
    exact AdmLab_retToCallIn S hc _
  | throwRefHandlerCatch =>
    intro S hl
    simp only [AdmsLab_cons, AdmsLab_nil, and_true, AdmLab_handler] at hl
    simp only [AdmsLab_append, AdmsLab_vals, true_and, AdmsLab_cons, AdmsLab_nil, and_true,
      AdmLab_plain, instrLabels_br, List.mem_singleton, forall_eq]
    exact hl.1 _ List.mem_cons_self
  | throwRefHandlerCatchRef =>
    intro S hl
    simp only [AdmsLab_cons, AdmsLab_nil, and_true, AdmLab_handler] at hl
    simp only [AdmsLab_append, AdmsLab_vals, true_and, AdmsLab_cons, AdmsLab_nil, and_true,
      AdmLab_plain, instrLabels_br, List.mem_singleton, forall_eq, AdmLab_ref]
    exact hl.1 _ List.mem_cons_self
  | throwRefHandlerCatchAll =>
    intro S hl
    simp only [AdmsLab_cons, AdmsLab_nil, and_true, AdmLab_handler] at hl
    simp only [AdmsLab_cons, AdmsLab_nil, and_true, AdmLab_plain, instrLabels_br,
      List.mem_singleton, forall_eq]
    exact hl.1 _ List.mem_cons_self
  | throwRefHandlerCatchAllRef =>
    intro S hl
    simp only [AdmsLab_cons, AdmsLab_nil, and_true, AdmLab_handler] at hl
    simp only [AdmsLab_cons, AdmsLab_nil, and_true, AdmLab_plain, instrLabels_br,
      List.mem_singleton, forall_eq, AdmLab_ref, true_and]
    exact hl.1 _ List.mem_cons_self
  | throwRefHandlerNext =>
    intro S hl
    simp only [AdmsLab_cons, AdmsLab_nil, and_true, AdmLab_handler] at hl ⊢
    exact ⟨fun c hc => hl.1 c (List.mem_cons_of_mem _ hc), hl.2⟩
  | tryTable =>
    intro S hl
    simp only [AdmsLab_append, AdmsLab_vals, AdmsLab_cons, AdmsLab_nil, and_true, true_and,
      AdmLab_plain, AdmLab_handler, AdmLab_label, instrLabels_tryTable, List.mem_append,
      List.mem_map, AdmsLab_expression] at hl ⊢
    refine ⟨fun c hc => hl _ (.inl ⟨c, hc, rfl⟩), by simp, ?_⟩
    exact shiftP_of_unbind (fun n hn => hl n (.inr hn))
  | _ =>
    intro S hl
    simp_all [throwing, instrLabels_of_flat (i := .throwRef) rfl,
      instrLabels_of_flat (i := .tableGet _) rfl, instrLabels_of_flat (i := .refCast _) rfl,
      instrLabels_of_flat (i := .callRef _) rfl]

/-- Free labels along a run. -/
theorem Steps.admsLab {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') {S : Nat → Prop} (hl : AdmsLab S c.code) : AdmsLab S c'.code := by
  induction h with
  | refl => exact hl
  | tail _ hs ih => exact Step.admsLab hs ih

/-! ## Code that never falls through -/

/-- An instruction that never completes normally: a bottom instruction, or a
structured instruction with a bottom body whose own label is not targeted
(a loop may be targeted: it re-enters itself). -/
inductive InstrBot : Instr → Prop
  | flat {i : Instr} (h : botInstr i = true) : InstrBot i
  | block {bt : BlockType} {body : List Instr} {j : Instr} (hj : j ∈ body) (hb : InstrBot j)
      (h0 : 0 ∉ instrsLabels body) : InstrBot (.block bt body)
  | loop {bt : BlockType} {body : List Instr} {j : Instr} (hj : j ∈ body) (hb : InstrBot j) :
      InstrBot (.loop bt body)
  | if_ {bt : BlockType} {t e : List Instr} {j k : Instr} (hj : j ∈ t) (hb : InstrBot j)
      (hk : k ∈ e) (hc : InstrBot k) (h0t : 0 ∉ instrsLabels t) (h0e : 0 ∉ instrsLabels e) :
      InstrBot (.if_ bt t e)

@[simp] theorem InstrBot_iff_flat {i : Instr} (hb : ∀ bt body, i ≠ .block bt body)
    (hl : ∀ bt body, i ≠ .loop bt body) (hi : ∀ bt t e, i ≠ .if_ bt t e) :
    InstrBot i ↔ botInstr i = true := by
  constructor
  · intro h
    cases h with
    | flat h => exact h
    | block => exact absurd rfl (hb _ _)
    | loop => exact absurd rfl (hl _ _)
    | if_ => exact absurd rfl (hi _ _ _)
  · exact .flat

theorem InstrBot_block_iff {bt : BlockType} {body : List Instr} :
    InstrBot (.block bt body) ↔ (∃ j ∈ body, InstrBot j) ∧ 0 ∉ instrsLabels body := by
  constructor
  · intro h
    cases h with
    | flat h => simp [botInstr] at h
    | block hj hb h0 => exact ⟨⟨_, hj, hb⟩, h0⟩
  · rintro ⟨⟨j, hj, hb⟩, h0⟩
    exact .block hj hb h0

theorem InstrBot_loop_iff {bt : BlockType} {body : List Instr} :
    InstrBot (.loop bt body) ↔ ∃ j ∈ body, InstrBot j := by
  constructor
  · intro h
    cases h with
    | flat h => simp [botInstr] at h
    | loop hj hb => exact ⟨_, hj, hb⟩
  · rintro ⟨j, hj, hb⟩
    exact .loop hj hb

theorem InstrBot_if_iff {bt : BlockType} {t e : List Instr} :
    InstrBot (.if_ bt t e) ↔ (∃ j ∈ t, InstrBot j) ∧ (∃ k ∈ e, InstrBot k) ∧
      0 ∉ instrsLabels t ∧ 0 ∉ instrsLabels e := by
  constructor
  · intro h
    cases h with
    | flat h => simp [botInstr] at h
    | if_ hj hb hk hc h0t h0e => exact ⟨⟨_, hj, hb⟩, ⟨_, hk, hc⟩, h0t, h0e⟩
  · rintro ⟨⟨j, hj, hb⟩, ⟨k, hk, hc⟩, h0t, h0e⟩
    exact .if_ hj hb hk hc h0t h0e

mutual
/-- An administrative instruction that never falls through. -/
def AdmBot : Admin → Prop
  | .plain i => InstrBot i
  | .ref _ => False
  | .callRefType _ => False
  | .returnCallRefType _ => True
  | .label _ cont body => AdmsBot body ∧ (AdmsLab (fun n => n ≠ 0) body ∨ ∃ j ∈ cont, InstrBot j)
  | .handler _ _ body => AdmsBot body
  | .frame _ _ _ => False
  | .trap => True
/-- Some element of the sequence never falls through. -/
def AdmsBot : List Admin → Prop
  | [] => False
  | a :: as => AdmBot a ∨ AdmsBot as
end

@[simp] theorem AdmsBot_nil : AdmsBot [] ↔ False := Iff.rfl
@[simp] theorem AdmsBot_cons (a : Admin) (as : List Admin) :
    AdmsBot (a :: as) ↔ AdmBot a ∨ AdmsBot as := Iff.rfl
@[simp] theorem AdmBot_plain (i : Instr) : AdmBot (.plain i) ↔ InstrBot i := Iff.rfl
@[simp] theorem AdmBot_ref (r : Ref) : AdmBot (.ref r) ↔ False := Iff.rfl
@[simp] theorem AdmBot_callRefType (d : DefType) : AdmBot (.callRefType d) ↔ False := Iff.rfl
@[simp] theorem AdmBot_returnCallRefType (d : DefType) : AdmBot (.returnCallRefType d) :=
  trivial
@[simp] theorem AdmBot_label (k : Nat) (cont : List Instr) (body : List Admin) :
    AdmBot (.label k cont body) ↔
      AdmsBot body ∧ (AdmsLab (fun n => n ≠ 0) body ∨ ∃ j ∈ cont, InstrBot j) := Iff.rfl
@[simp] theorem AdmBot_handler (k : Nat) (cs : List Catch) (body : List Admin) :
    AdmBot (.handler k cs body) ↔ AdmsBot body := Iff.rfl
@[simp] theorem AdmBot_frame (k : Nat) (fr : Frame) (body : List Admin) :
    AdmBot (.frame k fr body) ↔ False := Iff.rfl
@[simp] theorem AdmBot_trap : AdmBot .trap := trivial

@[simp] theorem AdmsBot_append : ∀ l₁ l₂ : List Admin, AdmsBot (l₁ ++ l₂) ↔ AdmsBot l₁ ∨ AdmsBot l₂
  | [], _ => by simp
  | a :: l₁, l₂ => by simp [AdmsBot_append l₁ l₂, or_assoc]

/-- `InstrBot` on flat instructions. -/
theorem InstrBot_flat_iff {i : Instr} (hf : i.flat = true) :
    InstrBot i ↔ botInstr i = true :=
  InstrBot_iff_flat (by rintro _ _ rfl; simp [Instr.flat] at hf)
    (by rintro _ _ rfl; simp [Instr.flat] at hf) (by rintro _ _ _ rfl; simp [Instr.flat] at hf)

@[simp] theorem AdmBot_val (v : Val) : ¬ AdmBot v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, botInstr]

@[simp] theorem AdmBot_constI32 (c : BitVec 32) : ¬ AdmBot (constI32 c) := AdmBot_val _

@[simp] theorem AdmsBot_vals : ∀ vs : List Val, ¬ AdmsBot (vals vs)
  | [] => id
  | v :: vs => by
    show ¬ (AdmBot v.toAdmin ∨ AdmsBot (vals vs))
    exact fun h => h.elim (AdmBot_val v) (AdmsBot_vals vs)

@[simp] theorem AdmsBot_expression : ∀ is : List Instr, AdmsBot (expression is) ↔ ∃ j ∈ is, InstrBot j
  | [] => by simp [expression]
  | i :: is => by
    have ih := AdmsBot_expression is
    simp only [expression, List.map_cons, AdmsBot_cons, AdmBot_plain] at ih ⊢
    rw [ih]
    simp

theorem not_AdmBot_callRef {c : Admin} (h : c.IsCallRef) : ¬ AdmBot c := by
  rcases isCallRef_cases h with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · simp [botInstr]
  · simp

theorem AdmBot_retCall {c : Admin} (h : c.IsReturnCallRef) : AdmBot c := by
  rcases isReturnCallRef_cases h with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · exact InstrBot.flat rfl
  · trivial

/-- **Bottom is preserved.** Code that contains an instruction that never falls
through keeps one along every step. -/
theorem Step.admsBot {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') : AdmsBot c.code → AdmsBot c'.code := by
  induction h with
  | parametric h =>
    intro hb
    cases h <;> simp_all [botInstr]
  | numeric h => intro hb; cases h <;> simp_all [botInstr]
  | vector h => intro hb; cases h <;> simp_all [botInstr]
  | «variable» h => intro hb; cases h <;> simp_all [botInstr]
  | table h => intro hb; cases h <;> simp_all [botInstr]
  | memory h => intro hb; cases h <;> simp_all [botInstr]
  | reference h => intro hb; cases h <;> simp_all [botInstr]
  | aggregate h => intro hb; cases h <;> simp_all [botInstr]
  | ctxtInstrs _ _ ih =>
    intro hb
    simp only [AdmsBot_append] at hb ⊢
    rcases hb with (hv | hi) | hr
    · exact absurd hv (AdmsBot_vals _)
    · exact .inl (.inr (ih hi))
    · exact .inr hr
  | ctxtLabel h ih =>
    intro hb
    simp only [AdmsBot_cons, AdmsBot_nil, or_false, AdmBot_label] at hb ⊢
    exact ⟨ih hb.1, hb.2.imp_left (Step.admsLab h)⟩
  | ctxtHandler _ ih =>
    intro hb
    simp only [AdmsBot_cons, AdmsBot_nil, or_false, AdmBot_handler] at hb ⊢
    exact ih hb
  | ctxtFrame => intro hb; simp at hb
  | block =>
    intro hb
    simp only [AdmsBot_append, AdmsBot_vals, false_or, AdmsBot_cons, AdmsBot_nil, or_false,
      AdmBot_plain, InstrBot_block_iff] at hb
    simp only [AdmsBot_cons, AdmsBot_nil, or_false, AdmBot_label, AdmsBot_append,
      AdmsBot_vals, false_or, AdmsBot_expression, AdmsLab_append, AdmsLab_vals, true_and,
      AdmsLab_expression]
    exact ⟨hb.1, .inl fun n hn e => hb.2 (e ▸ hn)⟩
  | loop =>
    intro hb
    simp only [AdmsBot_append, AdmsBot_vals, false_or, AdmsBot_cons, AdmsBot_nil, or_false,
      AdmBot_plain, InstrBot_loop_iff] at hb
    simp only [AdmsBot_cons, AdmsBot_nil, or_false, AdmBot_label, AdmsBot_append,
      AdmsBot_vals, false_or, AdmsBot_expression]
    exact ⟨hb, .inr ⟨_, List.mem_singleton_self _, InstrBot_loop_iff.mpr hb⟩⟩
  | ifTrue =>
    intro hb
    simp only [AdmsBot_cons, AdmsBot_nil, or_false, AdmBot_constI32, false_or, AdmBot_plain,
      InstrBot_if_iff] at hb
    simp only [AdmsBot_cons, AdmsBot_nil, or_false, AdmBot_plain, InstrBot_block_iff]
    exact ⟨hb.1, hb.2.2.1⟩
  | ifFalse =>
    intro hb
    simp only [AdmsBot_cons, AdmsBot_nil, or_false, AdmBot_constI32, false_or, AdmBot_plain,
      InstrBot_if_iff] at hb
    simp only [AdmsBot_cons, AdmsBot_nil, or_false, AdmBot_plain, InstrBot_block_iff]
    exact ⟨hb.2.1, hb.2.2.2⟩
  | labelVals =>
    intro hb
    simp only [AdmsBot_cons, AdmsBot_nil, or_false, AdmBot_label] at hb
    exact absurd hb.1 (AdmsBot_vals _)
  | @brLabelZero _ _ _ _ _ _ l _ hl0 _ =>
    intro hb
    simp only [AdmsBot_cons, AdmsBot_nil, or_false, AdmBot_label] at hb
    rcases hb.2 with hlab | hcont
    · have h1 := AdmsLab_mem hlab (a := .plain (.br l)) (by simp)
      simp only [AdmLab_plain, instrLabels_br, List.mem_singleton, forall_eq] at h1
      exact absurd hl0 h1
    · simp only [AdmsBot_append, AdmsBot_vals, false_or, AdmsBot_expression]
      exact hcont
  | callRefFunc hc =>
    intro hb
    simp only [AdmsBot_append, AdmsBot_vals, false_or, AdmsBot_cons, AdmsBot_nil, or_false,
      AdmBot_ref] at hb
    exact absurd hb (not_AdmBot_callRef hc)
  | callRefHost hc =>
    intro hb
    simp only [AdmsBot_append, AdmsBot_vals, false_or, AdmsBot_cons, AdmsBot_nil, or_false,
      AdmBot_ref] at hb
    exact absurd hb (not_AdmBot_callRef hc)
  | callRefHostDiv => intro hb; exact hb
  | returnCallRefLabel hc =>
    intro _
    simp only [AdmsBot_append, AdmsBot_vals, false_or, AdmsBot_cons, AdmsBot_nil, or_false]
    exact AdmBot_retCall hc
  | returnCallRefHandler hc =>
    intro _
    simp only [AdmsBot_append, AdmsBot_vals, false_or, AdmsBot_cons, AdmsBot_nil, or_false]
    exact AdmBot_retCall hc
  | throwRefHandlerNext =>
    intro hb
    simp only [AdmsBot_cons, AdmsBot_nil, or_false, AdmBot_handler] at hb ⊢
    exact hb
  | _ =>
    intro hb
    simp_all [botInstr, throwing]

/-- Bottom along a run. -/
theorem Steps.admsBot {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hb : AdmsBot c.code) : AdmsBot c'.code := by
  induction h with
  | refl => exact hb
  | tail _ hs ih => exact Step.admsBot hs ih

/-! ## Effect budgets -/

/-- An effect budget: what a run is allowed to do. -/
structure Bud where
  /-- Locals the code may write. -/
  lw : Nat → Prop
  /-- Globals (module indices) the code may write. -/
  gw : Nat → Prop
  /-- The code may call. -/
  calls : Prop
  /-- The code may trap. -/
  trap : Prop
  /-- The code may loop. -/
  loops : Prop
  /-- The code may return. -/
  ret : Prop

/-- The integer operators that may trap (division and remainder). -/
def binTraps : IntBinOp → Prop
  | .div _ => True
  | .rem _ => True
  | _ => False

theorem binTraps_of_error {t : IntType} {op : IntBinOp} {x y : BitVec t.width} {e : IntTrap}
    (h : intBinOp t op x y = .error e) : binTraps op := by
  match op, h with
  | .div _, _ => trivial
  | .rem _, _ => trivial
  | .add, h => simp [intBinOp] at h
  | .sub, h => simp [intBinOp] at h
  | .mul, h => simp [intBinOp] at h
  | .and, h => simp [intBinOp] at h
  | .or, h => simp [intBinOp] at h
  | .xor, h => simp [intBinOp] at h
  | .shl, h => simp [intBinOp] at h
  | .shr .signed, h => simp [intBinOp] at h
  | .shr .unsigned, h => simp [intBinOp] at h
  | .rotl, h => simp [intBinOp] at h
  | .rotr, h => simp [intBinOp] at h

/-- The flat instructions inside a budget. -/
@[simp] def FlatB (b : Bud) (S : Nat → Prop) : Instr → Prop
  | .nop | .drop | .select _ | .intConst _ _ | .floatConst _ _ | .vecConst _ | .intUnOp _ _
  | .intTestOp _ _ | .intRelOp _ _ | .localGet _ | .globalGet _ => True
  | .intBinOp _ op => binTraps op → b.trap
  | .unreachable => b.trap
  | .localSet x | .localTee x => b.lw x.toNat
  | .globalSet g => b.gw g.toNat
  | .br l | .brIf l => S l.toNat
  | .brTable ls d => S d.toNat ∧ ∀ l ∈ ls, S l.toNat
  | .return_ => b.ret
  | .call _ | .callRef _ | .throwRef => b.calls
  | _ => False

/-- A Core instruction inside a budget, with branch targets in `S`. -/
inductive InstrB (b : Bud) : (Nat → Prop) → Instr → Prop
  | flat {S : Nat → Prop} {i : Instr} (h : FlatB b S i) : InstrB b S i
  | block {S : Nat → Prop} {bt : BlockType} {body : List Instr}
      (h : ∀ j ∈ body, InstrB b (shiftP S) j) : InstrB b S (.block bt body)
  | loop {S : Nat → Prop} {bt : BlockType} {body : List Instr} (hl : b.loops)
      (h : ∀ j ∈ body, InstrB b (shiftP S) j) : InstrB b S (.loop bt body)
  | if_ {S : Nat → Prop} {bt : BlockType} {t e : List Instr}
      (ht : ∀ j ∈ t, InstrB b (shiftP S) j) (he : ∀ j ∈ e, InstrB b (shiftP S) j) :
      InstrB b S (.if_ bt t e)

@[simp] theorem InstrB_iff_flat {b : Bud} {S : Nat → Prop} {i : Instr}
    (hb : ∀ bt body, i ≠ .block bt body) (hl : ∀ bt body, i ≠ .loop bt body)
    (hi : ∀ bt t e, i ≠ .if_ bt t e) : InstrB b S i ↔ FlatB b S i := by
  constructor
  · intro h
    cases h with
    | flat h => exact h
    | block => exact absurd rfl (hb _ _)
    | loop => exact absurd rfl (hl _ _)
    | if_ => exact absurd rfl (hi _ _ _)
  · exact .flat

theorem InstrB_flat_iff {b : Bud} {S : Nat → Prop} {i : Instr} (hf : i.flat = true) :
    InstrB b S i ↔ FlatB b S i :=
  InstrB_iff_flat (by rintro _ _ rfl; simp [Instr.flat] at hf)
    (by rintro _ _ rfl; simp [Instr.flat] at hf) (by rintro _ _ _ rfl; simp [Instr.flat] at hf)

@[simp] theorem InstrB_block_iff {b : Bud} {S : Nat → Prop} {bt : BlockType} {body : List Instr} :
    InstrB b S (.block bt body) ↔ ∀ j ∈ body, InstrB b (shiftP S) j := by
  constructor
  · intro h
    cases h with
    | flat h => simp at h
    | block h => exact h
  · exact .block

@[simp] theorem InstrB_loop_iff {b : Bud} {S : Nat → Prop} {bt : BlockType} {body : List Instr} :
    InstrB b S (.loop bt body) ↔ b.loops ∧ ∀ j ∈ body, InstrB b (shiftP S) j := by
  constructor
  · intro h
    cases h with
    | flat h => simp at h
    | loop hl h => exact ⟨hl, h⟩
  · exact fun h => .loop h.1 h.2

@[simp] theorem InstrB_if_iff {b : Bud} {S : Nat → Prop} {bt : BlockType} {t e : List Instr} :
    InstrB b S (.if_ bt t e) ↔
      (∀ j ∈ t, InstrB b (shiftP S) j) ∧ ∀ j ∈ e, InstrB b (shiftP S) j := by
  constructor
  · intro h
    cases h with
    | flat h => simp at h
    | if_ ht he => exact ⟨ht, he⟩
  · exact fun h => .if_ h.1 h.2

@[simp] theorem InstrB_br {b : Bud} {S : Nat → Prop} {l : LabelIdx} :
    InstrB b S (.br l) ↔ S l.toNat :=
  InstrB_iff_flat (by simp) (by simp) (by simp)

@[simp] theorem InstrB_brIf {b : Bud} {S : Nat → Prop} {l : LabelIdx} :
    InstrB b S (.brIf l) ↔ S l.toNat :=
  InstrB_iff_flat (by simp) (by simp) (by simp)

@[simp] theorem InstrB_brTable {b : Bud} {S : Nat → Prop} {ls : List LabelIdx} {d : LabelIdx} :
    InstrB b S (.brTable ls d) ↔ S d.toNat ∧ ∀ l ∈ ls, S l.toNat :=
  InstrB_iff_flat (by simp) (by simp) (by simp)

@[simp] theorem InstrB_return {b : Bud} {S : Nat → Prop} : InstrB b S .return_ ↔ b.ret :=
  InstrB_iff_flat (by simp) (by simp) (by simp)

/-- Free labels of budgeted code are in `S`. -/
theorem FlatB_labels {b : Bud} {S : Nat → Prop} {i : Instr} (h : FlatB b S i) :
    ∀ n ∈ instrLabels i, S n := by
  intro n hn
  cases i
  case brTable ls d =>
    simp only [instrLabels_brTable, List.mem_cons, List.mem_map] at hn
    simp only [FlatB] at h
    rcases hn with rfl | ⟨l, hl, rfl⟩
    · exact h.1
    · exact h.2 l hl
  all_goals (rw [instrLabels.eq_def] at hn; simp_all)

theorem labels_of_forall {T : Nat → Prop} {body : List Instr}
    (h : ∀ j ∈ body, ∀ n ∈ instrLabels j, T n) : ∀ n ∈ instrsLabels body, T n := by
  intro n hn
  obtain ⟨j, hj, hn⟩ := mem_instrsLabels.mp hn
  exact h j hj n hn

theorem InstrB.labels {b : Bud} {S : Nat → Prop} {i : Instr} (h : InstrB b S i) :
    ∀ n ∈ instrLabels i, S n := by
  induction h with
  | flat h => exact FlatB_labels h
  | block _ ih =>
    rw [instrLabels_block]
    intro n hn
    exact labels_of_forall ih (n + 1) (mem_unbind.mp hn)
  | loop _ _ ih =>
    rw [instrLabels_loop]
    intro n hn
    exact labels_of_forall ih (n + 1) (mem_unbind.mp hn)
  | if_ _ _ iht ihe =>
    rw [instrLabels_if]
    intro n hn
    rcases List.mem_append.mp (mem_unbind.mp hn) with hn | hn
    · exact labels_of_forall iht (n + 1) hn
    · exact labels_of_forall ihe (n + 1) hn

mutual
/-- An administrative instruction inside a budget. -/
def AdmB (b : Bud) (S : Nat → Prop) : Admin → Prop
  | .plain i => InstrB b S i
  | .ref _ => True
  | .callRefType _ => b.calls
  | .returnCallRefType _ => False
  | .label _ cont body => (∀ j ∈ cont, InstrB b S j) ∧ AdmsB b (shiftP S) body
  | .handler _ _ _ => False
  | .frame _ _ _ => b.calls
  | .trap => b.trap ∨ b.calls
/-- `AdmB` on a sequence. -/
def AdmsB (b : Bud) (S : Nat → Prop) : List Admin → Prop
  | [] => True
  | a :: as => AdmB b S a ∧ AdmsB b S as
end

section
variable {b : Bud} {S : Nat → Prop}

@[simp] theorem AdmsB_nil : AdmsB b S [] ↔ True := Iff.rfl
@[simp] theorem AdmsB_cons (a : Admin) (as : List Admin) :
    AdmsB b S (a :: as) ↔ AdmB b S a ∧ AdmsB b S as := Iff.rfl
@[simp] theorem AdmB_plain (i : Instr) : AdmB b S (.plain i) ↔ InstrB b S i := Iff.rfl
@[simp] theorem AdmB_ref (r : Ref) : AdmB b S (.ref r) := trivial
@[simp] theorem AdmB_callRefType (d : DefType) : AdmB b S (.callRefType d) ↔ b.calls := Iff.rfl
@[simp] theorem AdmB_returnCallRefType (d : DefType) : AdmB b S (.returnCallRefType d) ↔ False :=
  Iff.rfl
@[simp] theorem AdmB_label (k : Nat) (cont : List Instr) (body : List Admin) :
    AdmB b S (.label k cont body) ↔ (∀ j ∈ cont, InstrB b S j) ∧ AdmsB b (shiftP S) body :=
  Iff.rfl
@[simp] theorem AdmB_handler (k : Nat) (cs : List Catch) (body : List Admin) :
    AdmB b S (.handler k cs body) ↔ False := Iff.rfl
@[simp] theorem AdmB_frame (k : Nat) (fr : Frame) (body : List Admin) :
    AdmB b S (.frame k fr body) ↔ b.calls := Iff.rfl
@[simp] theorem AdmB_trap : AdmB b S .trap ↔ b.trap ∨ b.calls := Iff.rfl

@[simp] theorem AdmsB_append : ∀ l₁ l₂ : List Admin, AdmsB b S (l₁ ++ l₂) ↔ AdmsB b S l₁ ∧ AdmsB b S l₂
  | [], _ => by simp
  | a :: l₁, l₂ => by simp [AdmsB_append l₁ l₂, and_assoc]

@[simp] theorem AdmB_val (v : Val) : AdmB b S v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin]

@[simp] theorem AdmB_constI32 (c : BitVec 32) : AdmB b S (constI32 c) := AdmB_val _

@[simp] theorem AdmsB_vals : ∀ vs : List Val, AdmsB b S (vals vs)
  | [] => trivial
  | v :: vs => (AdmsB_cons _ _).mpr ⟨AdmB_val v, AdmsB_vals vs⟩

@[simp] theorem AdmsB_expression :
    ∀ is : List Instr, AdmsB b S (expression is) ↔ ∀ j ∈ is, InstrB b S j
  | [] => by simp [expression]
  | i :: is => by
    have ih := AdmsB_expression is
    simp only [expression, List.map_cons, AdmsB_cons, AdmB_plain] at ih ⊢
    rw [ih]
    simp

theorem AdmsB_mem : ∀ {l : List Admin}, AdmsB b S l → ∀ {a : Admin}, a ∈ l → AdmB b S a
  | [], _, _, ha => absurd ha List.not_mem_nil
  | _ :: _, h, _, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h.1
    · exact AdmsB_mem h.2 ha

theorem AdmB_callRef_calls {c : Admin} (hc : c.IsCallRef) (h : AdmB b S c) : b.calls := by
  rcases isCallRef_cases hc with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · simpa using h
  · simpa using h

theorem not_AdmB_retCall {c : Admin} (hc : c.IsReturnCallRef) : ¬ AdmB b S c := by
  rcases isReturnCallRef_cases hc with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · simp only [AdmB_plain]
    intro h
    cases h with
    | flat h => simp at h
  · simp

theorem AdmB_retToCallIn {c : Admin} (hc : c.IsReturnCallRef) (hcalls : b.calls)
    (m : ModuleInst) : AdmB b S (c.retToCallIn m) := by
  rcases retToCallIn_cases hc m with ⟨y, e⟩ | ⟨d, e⟩ <;> rw [e]
  · simpa using hcalls
  · simpa using hcalls

theorem AdmsB_result (hcalls : b.calls) (r : Result) : AdmsB b S r.toAdmin := by
  cases r with
  | values vs => exact AdmsB_vals vs
  | throw a => simpa [Result.toAdmin] using hcalls
  | trap => simp [Result.toAdmin, hcalls]

theorem AdmsB.lab : ∀ {l : List Admin} {S : Nat → Prop}, AdmsB b S l → AdmsLab S l
  | [], _, _ => trivial
  | .plain _ :: _, _, h => (AdmsLab_cons _ _ _).mpr ⟨InstrB.labels h.1, AdmsB.lab h.2⟩
  | .label _ _ _ :: _, _, h =>
    (AdmsLab_cons _ _ _).mpr ⟨(AdmLab_label _ _ _ _).mpr
      ⟨labels_of_forall fun j hj => InstrB.labels (h.1.1 j hj), AdmsB.lab h.1.2⟩, AdmsB.lab h.2⟩
  | .handler _ _ _ :: _, _, h => False.elim h.1
  | .ref _ :: _, _, h => (AdmsLab_cons _ _ _).mpr ⟨trivial, AdmsB.lab h.2⟩
  | .callRefType _ :: _, _, h => (AdmsLab_cons _ _ _).mpr ⟨trivial, AdmsB.lab h.2⟩
  | .returnCallRefType _ :: _, _, h => (AdmsLab_cons _ _ _).mpr ⟨trivial, AdmsB.lab h.2⟩
  | .frame _ _ _ :: _, _, h => (AdmsLab_cons _ _ _).mpr ⟨trivial, AdmsB.lab h.2⟩
  | .trap :: _, _, h => (AdmsLab_cons _ _ _).mpr ⟨trivial, AdmsB.lab h.2⟩

end

/-! ## Size -/

mutual
/-- A size that decreases along every step of budgeted code without calls or loops. -/
def isz : Instr → Nat
  | .intConst _ _ => 1
  | .floatConst _ _ => 1
  | .vecConst _ => 1
  | .localTee _ => 4
  | .block _ body => 2 + iszs body
  | .loop _ body => 2 + iszs body
  | .if_ _ t e => 3 + iszs t + iszs e
  | _ => 2
/-- `isz` on a sequence. -/
def iszs : List Instr → Nat
  | [] => 0
  | i :: is => isz i + iszs is
end

mutual
/-- The size of an administrative instruction. -/
def asz : Admin → Nat
  | .plain i => isz i
  | .ref _ => 1
  | .callRefType _ => 1
  | .returnCallRefType _ => 1
  | .label _ cont body => 1 + iszs cont + aszs body
  | .handler _ _ body => 1 + aszs body
  | .frame _ _ body => 1 + aszs body
  | .trap => 1
/-- `asz` on a sequence. -/
def aszs : List Admin → Nat
  | [] => 0
  | a :: as => asz a + aszs as
end

@[simp] theorem iszs_nil : iszs [] = 0 := rfl
@[simp] theorem iszs_cons (i : Instr) (is : List Instr) : iszs (i :: is) = isz i + iszs is := rfl
@[simp] theorem aszs_nil : aszs [] = 0 := rfl
@[simp] theorem aszs_cons (a : Admin) (as : List Admin) : aszs (a :: as) = asz a + aszs as := rfl
@[simp] theorem asz_plain (i : Instr) : asz (.plain i) = isz i := rfl
@[simp] theorem asz_ref (r : Ref) : asz (.ref r) = 1 := rfl
@[simp] theorem asz_trap : asz .trap = 1 := rfl
@[simp] theorem asz_label (k : Nat) (cont : List Instr) (body : List Admin) :
    asz (.label k cont body) = 1 + iszs cont + aszs body := rfl
@[simp] theorem isz_block (bt : BlockType) (body : List Instr) :
    isz (.block bt body) = 2 + iszs body := rfl
@[simp] theorem isz_loop (bt : BlockType) (body : List Instr) :
    isz (.loop bt body) = 2 + iszs body := rfl
@[simp] theorem isz_if (bt : BlockType) (t e : List Instr) :
    isz (.if_ bt t e) = 3 + iszs t + iszs e := rfl
@[simp] theorem isz_intConst (t : IntType) (c : BitVec t.width) : isz (.intConst t c) = 1 := rfl
@[simp] theorem isz_localTee (x : LocalIdx) : isz (.localTee x) = 4 := rfl

@[simp] theorem isz_nop : isz .nop = 2 := rfl
@[simp] theorem isz_drop : isz .drop = 2 := rfl
@[simp] theorem isz_unreachable : isz .unreachable = 2 := rfl
@[simp] theorem isz_select (ts : Option (List ValType)) : isz (.select ts) = 2 := rfl
@[simp] theorem isz_intUnOp (t : IntType) (op : IntUnOp) : isz (.intUnOp t op) = 2 := rfl
@[simp] theorem isz_intBinOp (t : IntType) (op : IntBinOp) : isz (.intBinOp t op) = 2 := rfl
@[simp] theorem isz_intTestOp (t : IntType) (op : IntTestOp) : isz (.intTestOp t op) = 2 := rfl
@[simp] theorem isz_intRelOp (t : IntType) (op : IntRelOp) : isz (.intRelOp t op) = 2 := rfl
@[simp] theorem isz_localGet (x : LocalIdx) : isz (.localGet x) = 2 := rfl
@[simp] theorem isz_localSet (x : LocalIdx) : isz (.localSet x) = 2 := rfl
@[simp] theorem isz_globalGet (x : GlobalIdx) : isz (.globalGet x) = 2 := rfl
@[simp] theorem isz_globalSet (x : GlobalIdx) : isz (.globalSet x) = 2 := rfl
@[simp] theorem isz_br (l : LabelIdx) : isz (.br l) = 2 := rfl
@[simp] theorem isz_brIf (l : LabelIdx) : isz (.brIf l) = 2 := rfl
@[simp] theorem isz_brTable (ls : List LabelIdx) (d : LabelIdx) : isz (.brTable ls d) = 2 := rfl
@[simp] theorem isz_return : isz .return_ = 2 := rfl

@[simp] theorem asz_val (v : Val) : asz v.toAdmin = 1 := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

@[simp] theorem asz_constI32 (c : BitVec 32) : asz (constI32 c) = 1 := asz_val _

@[simp] theorem aszs_append : ∀ l₁ l₂ : List Admin, aszs (l₁ ++ l₂) = aszs l₁ + aszs l₂
  | [], _ => by simp
  | a :: l₁, l₂ => by
    show asz a + aszs (l₁ ++ l₂) = (asz a + aszs l₁) + aszs l₂
    rw [aszs_append l₁ l₂, Nat.add_assoc]

@[simp] theorem aszs_vals : ∀ vs : List Val, aszs (vals vs) = vs.length
  | [] => rfl
  | v :: vs => by
    show asz v.toAdmin + aszs (vals vs) = vs.length + 1
    rw [asz_val, aszs_vals vs]; omega

@[simp] theorem aszs_expression : ∀ is : List Instr, aszs (expression is) = iszs is
  | [] => rfl
  | i :: is => by
    show isz i + aszs (expression is) = isz i + iszs is
    rw [aszs_expression is]

theorem isz_pos (i : Instr) : 0 < isz i := by
  unfold isz
  split <;> omega

theorem asz_pos (a : Admin) : 0 < asz a := by
  cases a <;> simp [asz, isz_pos]

theorem aszs_pos {l : List Admin} (h : l ≠ []) : 0 < aszs l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => simp only [aszs_cons]; have := asz_pos a; omega

/-! ## Steps of budgeted code -/

/-- What a step of budgeted code does. -/
structure BudConcl (P : Profile) (b : Bud) (S : Nat → Prop) (c c' : Config H) : Prop where
  /-- The budget is kept. -/
  ab : AdmsB b S c'.code
  /-- The module of the frame is unchanged. -/
  modu : c'.frame.module = c.frame.module
  /-- Unbudgeted locals are unchanged. -/
  loc : ∀ x, ¬ b.lw x → c'.frame.locals[x]? = c.frame.locals[x]?
  /-- Without calls or global writes, the store is unchanged. -/
  st : ¬ b.calls → (∀ g, ¬ b.gw g) → c'.store = c.store
  /-- Without calls, a global address no budgeted global index refers to is unchanged. -/
  glob : ¬ b.calls → ∀ a, (∀ g, c.frame.module.globals[g]? = some a → ¬ b.gw g) →
    (c'.store.globals[a]?).map GlobalInst.value = (c.store.globals[a]?).map GlobalInst.value
  /-- Without calls or loops, the size decreases. -/
  size : ¬ b.calls → ¬ b.loops → aszs c'.code < aszs c.code
  /-- Without calls, the host is irrelevant. -/
  rehost : ¬ b.calls → ∀ host' : HostSemantics H, Step P host' c c'

theorem BudConcl.same {P : Profile} {b : Bud} {S : Nat → Prop} {s : Store H} {f : Frame}
    {is is' : List Admin} (hab : AdmsB b S is')
    (hsz : ¬ b.calls → ¬ b.loops → aszs is' < aszs is)
    (hre : ∀ host' : HostSemantics H, Step P host' ⟨s, f, is⟩ ⟨s, f, is'⟩) :
    BudConcl P b S ⟨s, f, is⟩ ⟨s, f, is'⟩ :=
  ⟨hab, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, hsz, fun _ => hre⟩

theorem BudConcl.calls {P : Profile} {b : Bud} {S : Nat → Prop} {c c' : Config H}
    (hc : b.calls) (hab : AdmsB b S c'.code) (hm : c'.frame = c.frame) : BudConcl P b S c c' :=
  ⟨hab, by rw [hm], fun _ _ => by rw [hm], fun h => absurd hc h, fun h => absurd hc h,
    fun h => absurd hc h, fun h => absurd hc h⟩

/-- **One step of budgeted code.** -/
theorem Step.bud {P : Profile} {host : HostSemantics H} {b : Bud} {c c' : Config H}
    (h : Step P host c c') : ∀ {S : Nat → Prop}, AdmsB b S c.code → BudConcl P b S c c' := by
  induction h with
  | @parametric s f is is' h =>
    intro S hab
    have hre : ∀ host' : HostSemantics H, Step P host' ⟨s, f, is⟩ ⟨s, f, is'⟩ :=
      fun _ => Step.parametric h
    cases h with
    | unreachable =>
      refine BudConcl.same ?_ (by simp) hre
      simp at hab ⊢
      exact .inl hab
    | _ => exact BudConcl.same (by simp_all) (by simp) hre
  | @numeric s f is is' h =>
    intro S hab
    have hre : ∀ host' : HostSemantics H, Step P host' ⟨s, f, is⟩ ⟨s, f, is'⟩ :=
      fun _ => Step.numeric h
    cases h with
    | intBinOpTrap he =>
      refine BudConcl.same ?_ (by simp) hre
      simp at hab ⊢
      exact .inl (hab (binTraps_of_error he))
    | intUnOp => exact BudConcl.same (by simp) (by simp) hre
    | intBinOp => exact BudConcl.same (by simp) (by simp) hre
    | intTestOp => exact BudConcl.same (by simp) (by simp) hre
    | intRelOp => exact BudConcl.same (by simp) (by simp) hre
    | _ => exfalso; simp at hab
  | vector h => intro S hab; exfalso; cases h <;> simp at hab
  | @«variable» c c' h =>
    intro S hab
    have hre : ∀ host' : HostSemantics H, Step P host' c c' := fun _ => Step.variable h
    cases h with
    | localGet => exact BudConcl.same (by simp) (by simp) hre
    | globalGet => exact BudConcl.same (by simp) (by simp) hre
    | localTee =>
      refine BudConcl.same ?_ (by simp) hre
      simp at hab ⊢
      exact hab
    | @localSet _ f x v _ =>
      simp at hab
      refine ⟨by simp, rfl, ?_, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => by simp,
        fun _ => hre⟩
      intro y hy
      show (f.locals.set x.toNat (some v))[y]? = f.locals[y]?
      rw [List.getElem?_set_ne]
      rintro rfl
      exact hy hab
    | @globalSet s _ _ a _ v hg =>
      simp at hab
      obtain ⟨hxa, -⟩ := Store.global?_spec hg
      refine ⟨by simp, rfl, fun _ _ => rfl, fun _ hng => absurd hab (hng _), ?_,
        fun _ _ => by simp, fun _ => hre⟩
      intro _ a' ha'
      have hne : a ≠ a' := by
        rintro rfl
        exact ha' _ hxa hab
      show ((s.globals.modify a fun g => { g with value := v })[a']?).map GlobalInst.value = _
      rw [List.getElem?_modify_ne _ _ hne]
  | table h => intro S hab; exfalso; cases h <;> simp at hab
  | memory h => intro S hab; exfalso; cases h <;> simp at hab
  | reference h => intro S hab; exfalso; cases h <;> simp at hab
  | aggregate h => intro S hab; exfalso; cases h <;> simp at hab
  | ctxtInstrs _ hne ih =>
    intro S hab
    simp only [AdmsB_append, AdmsB_vals, true_and] at hab
    have r := ih hab.1
    refine ⟨?_, r.modu, r.loc, r.st, r.glob, ?_, fun hc host' => Step.ctxtInstrs (r.rehost hc host') hne⟩
    · simp only [AdmsB_append, AdmsB_vals, true_and]
      exact ⟨r.ab, hab.2⟩
    · intro hc hl
      have := r.size hc hl
      simp only [aszs_append] at this ⊢
      omega
  | ctxtLabel _ ih =>
    intro S hab
    simp only [AdmsB_cons, AdmsB_nil, and_true, AdmB_label] at hab
    have r := ih hab.2
    refine ⟨?_, r.modu, r.loc, r.st, r.glob, ?_, fun hc host' => Step.ctxtLabel (r.rehost hc host')⟩
    · simp only [AdmsB_cons, AdmsB_nil, and_true, AdmB_label]
      exact ⟨hab.1, r.ab⟩
    · intro hc hl
      have := r.size hc hl
      simp only [aszs_cons, aszs_nil, asz_label] at this ⊢
      omega
  | ctxtHandler => intro S hab; simp at hab
  | ctxtFrame =>
    intro S hab
    simp only [AdmsB_cons, AdmsB_nil, and_true, AdmB_frame] at hab
    exact BudConcl.calls hab (by simpa using hab) rfl
  | block hbt hm =>
    intro S hab
    refine BudConcl.same ?_ ?_ (fun _ => Step.block hbt hm)
    · simp_all
    · intro _ _
      simp
      omega
  | loop hbt hm =>
    intro S hab
    simp at hab
    refine BudConcl.same ?_ (fun _ hl => absurd hab.1 hl) (fun _ => Step.loop hbt hm)
    simp_all
  | ifTrue hc =>
    intro S hab
    refine BudConcl.same ?_ ?_ (fun _ => Step.ifTrue hc)
    · simp_all
    · intro _ _
      simp
      omega
  | ifFalse =>
    intro S hab
    refine BudConcl.same ?_ ?_ (fun _ => Step.ifFalse)
    · simp_all
    · intro _ _
      simp
      omega
  | labelVals =>
    intro S _
    refine BudConcl.same (AdmsB_vals _) ?_ (fun _ => Step.labelVals)
    intro _ _
    simp
  | brLabelZero hl hn =>
    intro S hab
    simp only [AdmsB_cons, AdmsB_nil, and_true, AdmB_label] at hab
    refine BudConcl.same ?_ ?_ (fun _ => Step.brLabelZero hl hn)
    · simp only [AdmsB_append, AdmsB_vals, true_and, AdmsB_expression]
      exact hab.1
    · intro _ _
      simp
      omega
  | @brLabelSucc _ _ _ _ _ l _ hl =>
    intro S hab
    simp only [AdmsB_cons, AdmsB_nil, and_true, AdmB_label] at hab
    have hbr := AdmsB_mem hab.2 (a := .plain (.br l)) (by simp)
    simp only [AdmB_plain, InstrB_br] at hbr
    refine BudConcl.same ?_ ?_ (fun _ => Step.brLabelSucc hl)
    · simp only [AdmsB_append, AdmsB_vals, true_and, AdmsB_cons, AdmsB_nil, and_true,
        AdmB_plain, InstrB_br, labelPred_toNat]
      exact shiftP_pred hl hbr
    · intro _ _
      simp
      omega
  | brHandler => intro S hab; simp at hab
  | brIfTrue hc =>
    intro S hab
    exact BudConcl.same (by simpa using hab) (by simp) (fun _ => Step.brIfTrue hc)
  | brIfFalse =>
    intro S _
    exact BudConcl.same (by simp) (by simp) (fun _ => Step.brIfFalse)
  | brTableLt hi =>
    intro S hab
    simp at hab
    refine BudConcl.same ?_ (by simp) (fun _ => Step.brTableLt hi)
    simp
    exact hab.2 _ (List.mem_of_getElem? hi)
  | brTableGe hi =>
    intro S hab
    simp at hab
    refine BudConcl.same ?_ (by simp) (fun _ => Step.brTableGe hi)
    simpa using hab.1
  | call =>
    intro S hab
    simp at hab
    exact BudConcl.calls hab (by simpa using hab) rfl
  | callRefNull hc =>
    intro S hab
    have hcalls := AdmB_callRef_calls hc (AdmsB_mem hab (by simp))
    exact BudConcl.calls hcalls (by simp [hcalls]) rfl
  | callRefFunc hc =>
    intro S hab
    have hcalls := AdmB_callRef_calls hc (AdmsB_mem hab (by simp))
    exact BudConcl.calls hcalls (by simpa using hcalls) rfl
  | callRefHost hc =>
    intro S hab
    have hcalls := AdmB_callRef_calls hc (AdmsB_mem hab (by simp))
    exact BudConcl.calls hcalls (AdmsB_result hcalls _) rfl
  | callRefHostDiv hc =>
    intro S hab
    have hcalls := AdmB_callRef_calls hc (AdmsB_mem hab (by simp))
    exact BudConcl.calls hcalls hab rfl
  | returnCallRefLabel hc =>
    intro S hab
    simp only [AdmsB_cons, AdmsB_nil, and_true, AdmB_label] at hab
    exact absurd (AdmsB_mem hab.2 (by simp)) (not_AdmB_retCall hc)
  | returnCallRefFrameNull =>
    intro S hab
    simp only [AdmsB_cons, AdmsB_nil, and_true, AdmB_frame] at hab
    exact BudConcl.calls hab (by simp [hab]) rfl
  | returnCallRefFrameAddr hc =>
    intro S hab
    simp only [AdmsB_cons, AdmsB_nil, and_true, AdmB_frame] at hab
    refine BudConcl.calls hab ?_ rfl
    simp only [AdmsB_append, AdmsB_vals, true_and, AdmsB_cons, AdmsB_nil, and_true, AdmB_ref]
    exact AdmB_retToCallIn hc hab _
  | frameVals =>
    intro S hab
    simp only [AdmsB_cons, AdmsB_nil, and_true, AdmB_frame] at hab
    exact BudConcl.calls hab (AdmsB_vals _) rfl
  | returnFrame =>
    intro S hab
    simp only [AdmsB_cons, AdmsB_nil, and_true, AdmB_frame] at hab
    exact BudConcl.calls hab (AdmsB_vals _) rfl
  | returnLabel =>
    intro S hab
    simp only [AdmsB_cons, AdmsB_nil, and_true, AdmB_label] at hab
    have hret := AdmsB_mem hab.2 (a := .plain .return_) (by simp)
    simp only [AdmB_plain, InstrB_return] at hret
    exact BudConcl.same (by simpa using hret) (fun _ _ => by simp; omega)
      (fun _ => Step.returnLabel)
  | throwRefNull =>
    intro S hab
    simp at hab
    exact BudConcl.calls hab (by simp [hab]) rfl
  | throwRefInstrs =>
    intro S hab
    have hcalls := AdmsB_mem hab (a := .plain .throwRef) (by simp [throwing])
    simp at hcalls
    exact BudConcl.calls hcalls (by simpa [throwing] using hcalls) rfl
  | throwRefLabel =>
    intro S hab
    have hcalls : b.calls := by simp [throwing] at hab; tauto
    exact BudConcl.calls hcalls (by simpa [throwing] using hcalls) rfl
  | throwRefFrame =>
    intro S hab
    simp only [AdmsB_cons, AdmsB_nil, and_true, AdmB_frame] at hab
    exact BudConcl.calls hab (by simpa [throwing] using hab) rfl
  | trapInstrs hne =>
    intro S hab
    have ht := AdmsB_mem hab (a := .trap) (by simp)
    refine BudConcl.same (by simpa using ht) ?_ (fun _ => Step.trapInstrs hne)
    intro _ _
    simp only [aszs_append, aszs_vals, aszs_cons, aszs_nil, asz_trap]
    rcases hne with hne | hne
    · have := List.length_pos_iff.mpr hne
      omega
    · have := aszs_pos hne
      omega
  | trapLabel =>
    intro S hab
    simp only [AdmsB_cons, AdmsB_nil, and_true, AdmB_label, AdmB_trap] at hab
    refine BudConcl.same (by simpa using hab.2) ?_ (fun _ => Step.trapLabel)
    intro _ _
    simp
  | trapFrame =>
    intro S hab
    simp only [AdmsB_cons, AdmsB_nil, and_true, AdmB_frame] at hab
    exact BudConcl.calls hab (by simp [hab]) rfl
  | _ => intro S hab; exfalso; simp [throwing] at hab

/-- Budgeted runs: the budget, the module, unbudgeted locals and (without calls)
unbudgeted global addresses are kept. -/
theorem Steps.bud {P : Profile} {host : HostSemantics H} {b : Bud} {S : Nat → Prop}
    {c c' : Config H} (h : Steps P host c c') (hab : AdmsB b S c.code) :
    AdmsB b S c'.code ∧ c'.frame.module = c.frame.module ∧
      (∀ x, ¬ b.lw x → c'.frame.locals[x]? = c.frame.locals[x]?) ∧
      (¬ b.calls → ∀ a, (∀ g, c.frame.module.globals[g]? = some a → ¬ b.gw g) →
        (c'.store.globals[a]?).map GlobalInst.value =
          (c.store.globals[a]?).map GlobalInst.value) := by
  induction h with
  | refl => exact ⟨hab, rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | tail _ hs ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    have r := Step.bud hs h1
    refine ⟨r.ab, r.modu.trans h2, fun x hx => (r.loc x hx).trans (h3 x hx), fun hc a ha => ?_⟩
    rw [r.glob hc a (by rw [h2]; exact ha)]
    exact h4 hc a ha

/-- Budgeted code without calls or loops does not diverge. -/
theorem not_diverges_bud {P : Profile} {host : HostSemantics H} {b : Bud} {S : Nat → Prop}
    (hc : ¬ b.calls) (hl : ¬ b.loops) :
    ∀ (n : Nat) (c : Config H), aszs c.code < n → AdmsB b S c.code → ¬ Diverges P host c
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, c, h, hab, hd => by
    obtain ⟨c', hs, hd'⟩ := InfiniteTrace.unfold hd
    have r := Step.bud hs hab
    exact not_diverges_bud hc hl n c' (by have := r.size hc hl; omega) r.ab hd'

/-! ## Budgeted code without effects runs to values -/

/-- A host whose every call diverges: it satisfies `HostOk`. -/
def divHost : HostSemantics H := fun _ _ _ out => out = .diverged

theorem divHost_ok : HostOk (divHost (H := H)) := by
  intro _ _ _ _ _ _ _ _ _ _ _
  refine ⟨⟨.diverged, rfl⟩, fun out hout => ?_⟩
  cases hout
  trivial

theorem BlockTypeOk.reshape' {C : Context} {bt : BlockType} {t₁ t₂ : List CValType}
    (h : BlockTypeOk C bt t₁ t₂) (lo : List LocalType) (lb : List (List CValType))
    (r : Option (List CValType)) : BlockTypeOk (C.reshape lo lb r) bt t₁ t₂ := by
  cases h <;> constructor <;> assumption

theorem agree_shift {S : Nat → Prop} {lb L : List (List CValType)} (t : List CValType)
    (h : ∀ n, S n → lb[n]? = L[n]?) : ∀ n, shiftP S n → (t :: lb)[n]? = (t :: L)[n]?
  | 0, _ => rfl
  | n + 1, hn => by simpa using h n hn

mutual
/-- Budgeted code without returns keeps its typing when the labels it does not
target are replaced. -/
theorem InstrOk.budRelabel {b : Bud} (hr : ¬ b.ret) :
    ∀ {C : Context} {i : Instr} {it : InstrType}, InstrOk C i it →
      ∀ {S : Nat → Prop} {lb : List (List CValType)} (r : Option (List CValType)),
      InstrB b S i → (∀ n, S n → lb[n]? = C.labels[n]?) →
      InstrOk (C.reshape C.locals lb r) i it
  | _, _, _, .parametric h, _, _, _, _, _ => .parametric h.relabel
  | _, _, _, .numeric h, _, _, _, _, _ => .numeric h.reshape
  | _, _, _, .vector h, _, _, _, _, _ => .vector h.reshape
  | _, _, _, .variable h, _, _, _, _, _ => .variable h.relabel
  | _, _, _, .memory h, _, _, _, _, _ => .memory h.reshape
  | _, _, _, .table h, _, _, _, _, _ => .table h.reshape
  | _, _, _, .reference h, _, _, _, _, _ => .reference h.reshape
  | _, _, _, .block hbt hb, S, lb, r, hi, hS =>
    .block (BlockTypeOk.reshape' hbt _ _ _)
      (InstrsOk.budRelabel hr hb (S := shiftP S) (lb := _ :: lb) r (InstrB_block_iff.mp hi)
        (agree_shift _ hS))
  | _, _, _, .loop hbt hb, S, lb, r, hi, hS =>
    .loop (BlockTypeOk.reshape' hbt _ _ _)
      (InstrsOk.budRelabel hr hb (S := shiftP S) (lb := _ :: lb) r (InstrB_loop_iff.mp hi).2
        (agree_shift _ hS))
  | _, _, _, .if_ hbt h₁ h₂, S, lb, r, hi, hS =>
    .if_ (BlockTypeOk.reshape' hbt _ _ _)
      (InstrsOk.budRelabel hr h₁ (S := shiftP S) (lb := _ :: lb) r (InstrB_if_iff.mp hi).1
        (agree_shift _ hS))
      (InstrsOk.budRelabel hr h₂ (S := shiftP S) (lb := _ :: lb) r (InstrB_if_iff.mp hi).2
        (agree_shift _ hS))
  | _, _, _, .br hl hok, _, _, _, hi, hS => .br ((hS _ (InstrB_br.mp hi)).trans hl) hok
  | _, _, _, .brIf hl, _, _, _, hi, hS => .brIf ((hS _ (InstrB_brIf.mp hi)).trans hl)
  | _, _, _, .brTable hls hl' hok, _, _, _, hi, hS =>
    .brTable
      (fun l hl => by
        obtain ⟨lt, h1, h2⟩ := hls l hl
        exact ⟨lt, (hS _ ((InstrB_brTable.mp hi).2 l hl)).trans h1, h2⟩)
      (by
        obtain ⟨lt, h1, h2⟩ := hl'
        exact ⟨lt, (hS _ (InstrB_brTable.mp hi).1).trans h1, h2⟩)
      hok
  | _, _, _, .brOnNull .., _, _, _, hi, _ => by
    simp at hi
  | _, _, _, .brOnNonNull .., _, _, _, hi, _ => by
    simp at hi
  | _, _, _, .brOnCast .., _, _, _, hi, _ => by
    simp at hi
  | _, _, _, .brOnCastFail .., _, _, _, hi, _ => by
    simp at hi
  | _, _, _, .call hf he, _, _, _, _, _ => .call hf he
  | _, _, _, .callRef hd he, _, _, _, _, _ => .callRef hd he
  | _, _, _, .callIndirect ht hs hd he, _, _, _, _, _ => .callIndirect ht hs hd he
  | _, _, _, .return_ .., _, _, _, hi, _ => absurd (InstrB_return.mp hi) hr
  | _, _, _, .returnCall .., _, _, _, hi, _ => by
    simp at hi
  | _, _, _, .returnCallRef .., _, _, _, hi, _ => by
    simp at hi
  | _, _, _, .returnCallIndirect .., _, _, _, hi, _ => by
    simp at hi
  | _, _, _, .throw hx he hok, _, _, _, _, _ => .throw hx he hok
  | _, _, _, .throwRef hok, _, _, _, _, _ => .throwRef hok
  | _, _, _, .tryTable .., _, _, _, hi, _ => by
    simp at hi
/-- `InstrOk.budRelabel` on sequences. -/
theorem InstrsOk.budRelabel {b : Bud} (hr : ¬ b.ret) :
    ∀ {C : Context} {is : List Instr} {it : InstrType}, InstrsOk C is it →
      ∀ {S : Nat → Prop} {lb : List (List CValType)} (r : Option (List CValType)),
      (∀ j ∈ is, InstrB b S j) → (∀ n, S n → lb[n]? = C.labels[n]?) →
      InstrsOk (C.reshape C.locals lb r) is it
  | _, _, _, .nil, _, _, _, _, _ => .nil
  | _, _, _, .instr h, _, _, r, hi, hS =>
    .instr (InstrOk.budRelabel hr h r (hi _ (List.mem_singleton_self _)) hS)
  | C, _, _, @InstrsOk.seq _ _ _ _ _ _ xs₁ _ h₁ hx h₂, _, lb, r, hi, hS => by
    refine .seq (InstrsOk.budRelabel hr h₁ r (fun j hj => hi j (List.mem_append_left _ hj)) hS)
      hx ?_
    rw [Context.initLocals_reshape C lb r xs₁]
    exact InstrsOk.budRelabel hr h₂ r (fun j hj => hi j (List.mem_append_right _ hj))
      (by simpa using hS)
  | C, _, _, @InstrsOk.cons _ _ _ _ _ _ xs₁ _ h₁ hx h₂, _, lb, r, hi, hS => by
    refine .cons (InstrOk.budRelabel hr h₁ r (hi _ List.mem_cons_self) hS) hx ?_
    rw [Context.initLocals_reshape C lb r xs₁]
    exact InstrsOk.budRelabel hr h₂ r (fun j hj => hi j (List.mem_cons_of_mem _ hj))
      (by simpa using hS)
  | _, _, _, .sub h hs hok, _, _, r, hi, hS => .sub (InstrsOk.budRelabel hr h r hi hS) hs hok
  | _, _, _, .frame h hok, _, _, r, hi, hS => .frame (InstrsOk.budRelabel hr h r hi hS) hok
end

theorem frame_eq {f f' : Frame} (h1 : f'.locals = f.locals) (h2 : f'.module = f.module) :
    f' = f := by
  cases f; cases f'; cases h1; cases h2; rfl

/-- The progress/termination induction for `pure_run`. -/
theorem pure_run_aux {P : Profile} {b : Bud} {S : Nat → Prop}
    (hc : ¬ b.calls) (hl : ¬ b.loops) (ht : ¬ b.trap) (hr : ¬ b.ret) (hS : ∀ n, ¬ S n)
    (hw : ∀ x, ¬ b.lw x) (hg : ∀ g, ¬ b.gw g) {s : Store H} {f : Frame} (hs : StoreOk s) :
    ∀ (n : Nat) (code : List Admin), aszs code < n → AdmsB b S code →
    ∀ (Cf Ct : Context) (it : InstrType), it.params = [] → FrameOk s f Cf → CtxUnder Ct Cf →
      Ct.Wf → AdminsOk s Ct code it → ∃ ws, Steps P closedHost ⟨s, f, code⟩ ⟨s, f, vals ws⟩
  | 0, _, h, _, _, _, _, _, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, code, hn, hab, Cf, Ct, it, hp, hf, hu, hwf, hty => by
    have hts : StoreTypesOk s := ⟨hs.structsClosed, hs.arraysClosed⟩
    have hctx := wireCallRef_ctxOk hf hu
    have hty' := AdminsOk.weaken (wireCallRef_le hu) hty
    have hout := progress_aux (P := P) (host := divHost) divHost_ok hs hty' f []
      hctx (by rw [hp]; exact .nil)
    have e : vals [] ++ code = code := rfl
    rw [e] at hout
    rcases hout with ⟨ws, hws, -⟩ | ⟨c', hstep⟩ | ⟨_, _, hcode⟩ | ⟨_, _, _, hcode⟩ |
        ⟨_, l, _, _, hcode, -, -⟩ | ⟨_, _, _, hcode, -, -⟩ |
        ⟨_, _, c, _, _, hcode, hcr, -, -⟩
    · subst hws
      exact ⟨ws, .refl⟩
    · obtain ⟨s', f', code'⟩ := c'
      have r := Step.bud hstep hab
      have hs' : s' = s := r.st hc hg
      have hf' : f' = f := frame_eq (List.ext_getElem? fun x => r.loc x (hw x)) r.modu
      subst s'
      subst f'
      obtain ⟨Cf', Ct', -, -, hf2, -, hu2, hle, hty2⟩ :=
        Step.preservation_gen divHost_ok hstep hs hf hu hwf hts hty
      have hwf2 : Ct'.Wf := by
        refine hle.wf hwf ?_
        intro lt hlt
        obtain ⟨y, hy⟩ := List.mem_iff_getElem?.mp hlt
        obtain ⟨_, hi, -⟩ := hu2.le y lt hy
        have h3 := (FrameOk.ctxWf hs hts hf2).locals _ (List.mem_of_getElem? hi)
        rw [hu2.toTypeCtx]
        exact h3
      obtain ⟨ws, hrun⟩ := pure_run_aux hc hl ht hr hS hw hg hs n code'
        (Nat.lt_of_lt_of_le (r.size hc hl) (Nat.le_of_lt_succ hn)) r.ab Cf' Ct' it hp hf2 hu2
        hwf2 hty2
      exact ⟨ws, .head (r.rehost hc closedHost) hrun⟩
    · have h1 := AdmsB_mem hab (a := .trap) (by rw [hcode]; simp)
      simp only [AdmB_trap] at h1
      exact absurd h1 (by tauto)
    · have h1 := AdmsB_mem hab (a := .plain .throwRef) (by rw [hcode]; simp [throwing])
      simp at h1
      exact absurd h1 hc
    · have h1 := AdmsB_mem hab (a := .plain (.br l)) (by rw [hcode]; simp)
      simp only [AdmB_plain, InstrB_br] at h1
      exact absurd h1 (hS _)
    · have h1 := AdmsB_mem hab (a := .plain .return_) (by rw [hcode]; simp)
      simp only [AdmB_plain, InstrB_return] at h1
      exact absurd h1 hr
    · have h1 := AdmsB_mem hab (a := c) (by rw [hcode]; simp)
      exact absurd h1 (not_AdmB_retCall hcr)

/-- **Budgeted code without effects runs to values.** Typed code with no writes,
calls, traps, loops, returns or escaping branches reaches values, in host-free
steps, with store and frame unchanged. -/
theorem pure_run {P : Profile} {b : Bud} {S : Nat → Prop}
    (hc : ¬ b.calls) (hl : ¬ b.loops) (ht : ¬ b.trap) (hr : ¬ b.ret) (hS : ∀ n, ¬ S n)
    (hw : ∀ x, ¬ b.lw x) (hg : ∀ g, ¬ b.gw g) {C : Context} {it : InstrType} {is : List Instr}
    (hok : InstrsOk C is it) (hib : ∀ j ∈ is, InstrB b S j)
    {s : Store H} {f : Frame} {vs : List Val}
    (hs : StoreOk s) (hf : FrameOk s f { C with labels := [], return_ := none })
    (hv : List.Forall₂ (ValOk s) vs it.params) :
    ∃ ws, Steps P closedHost ⟨s, f, vals vs ++ expression is⟩ ⟨s, f, vals ws⟩ := by
  have hts : StoreTypesOk s := ⟨hs.structsClosed, hs.arraysClosed⟩
  have hok0 : InstrsOk (C.reshape C.locals [] none) is it :=
    InstrsOk.budRelabel hr hok none hib (fun n h => absurd h (hS n))
  have hf0 : FrameOk s f (C.reshape C.locals [] none) := hf
  have hwf : (C.reshape C.locals [] none).Wf := FrameOk.ctxWf hs hts hf0
  have hreg := InstrsOk.regular hwf hok0
  have hvals : AdminsOk s (C.reshape C.locals [] none) (vals vs) (.plain [] it.params) :=
    AdminsOk.of_vals hv hreg.1
  have h2 : AdminsOk s ((C.reshape C.locals [] none).initLocals []) (expression is)
      ⟨it.params, it.inits, it.results⟩ := AdminsOk.of_instrsOk hok0
  have hcode := AdminsOk.append hvals (by simp) h2
  have hab : AdmsB b S (vals vs ++ expression is) := by
    simp only [AdmsB_append, AdmsB_vals, true_and, AdmsB_expression]
    exact hib
  exact pure_run_aux hc hl ht hr hS hw hg hs _ _ (Nat.lt_succ_self _) hab _ _
    ⟨[], [] ++ it.inits, it.results⟩ rfl hf0 (CtxUnder.refl _) hwf hcode

end Silmaril.Wasm.Binaryen
