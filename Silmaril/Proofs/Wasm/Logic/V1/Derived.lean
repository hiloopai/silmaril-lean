module

public import Silmaril.Wasm.Logic.V1.Judgement.Defs

/-!
# Derived Wasm Logic rules

The rules of `Silmaril.Wasm.Logic.V1.Judgement.Defs` are the paper's, stated for the
smallest state they need: an empty stack below the operands, an empty heap, and
a context whose labels and return matter. Using them directly means an
`[extension]`, a `[frame]` and a `[consequence]` around every instruction.

This file derives the forms a proof actually uses. §4 of the paper describes the
same two strategies for getting a `[frame]` past a non-empty label context:
specialising "falsey" labels by `[consequence]` (`Triple.falseLabels`), or
removing them with `[context]` (`Triple.frameStraight`, which the paper prefers).
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

variable {Γ : Ctx} {P Q : Assert} {e : Silmaril.Wasm.V1.Expr}

/-! ### Reshaping assertions -/

theorem Assert.extend_mk (S S' : List (Term Value)) (H : HAssert) :
    Assert.extend S (Assert.mk S' H) = Assert.mk (S ++ S') H := by
  ext ρ vs h
  simp only [Assert.extend, Assert.mk, List.map_append]
  constructor
  · rintro ⟨vs', rfl, rfl, hH⟩
    exact ⟨rfl, hH⟩
  · rintro ⟨rfl, hH⟩
    exact ⟨_, rfl, rfl, hH⟩

theorem Assert.frame_mk (S : List (Term Value)) (H Hf : HAssert) :
    Assert.frame (Assert.mk S H) Hf = Assert.mk S (HAssert.star H Hf) := by
  ext ρ vs h
  simp only [Assert.frame, Assert.mk, HAssert.star]
  constructor
  · rintro ⟨h₁, h₂, d, rfl, ⟨rfl, hH⟩, hf⟩
    exact ⟨rfl, h₁, h₂, d, rfl, hH, hf⟩
  · rintro ⟨rfl, h₁, h₂, d, rfl, hH, hf⟩
    exact ⟨h₁, h₂, d, rfl, ⟨rfl, hH⟩, hf⟩

@[simp] theorem Assert.extend_nil (P : Assert) : Assert.extend [] P = P := by
  ext ρ vs h
  simp only [Assert.extend, List.map_nil, List.nil_append]
  constructor
  · rintro ⟨vs', rfl, hP⟩
    exact hP
  · intro hP
    exact ⟨vs, rfl, hP⟩

/-- `[extension]` commutes with an existential. -/
theorem Assert.extend_ex {α : Type} (S : List (Term Value)) (f : α → Assert) :
    Assert.extend S (Assert.ex f) = Assert.ex fun a => Assert.extend S (f a) := by
  ext ρ vs h
  simp only [Assert.extend, Assert.ex]
  constructor
  · rintro ⟨vs', hv, a, hP⟩
    exact ⟨a, vs', hv, hP⟩
  · rintro ⟨a, vs', hv, hP⟩
    exact ⟨vs', hv, a, hP⟩

/-- `⊗` commutes with an existential. -/
theorem Assert.frame_ex {α : Type} (f : α → Assert) (Hf : HAssert) :
    Assert.frame (Assert.ex f) Hf = Assert.ex fun a => Assert.frame (f a) Hf := by
  ext ρ vs h
  simp only [Assert.frame, Assert.ex]
  constructor
  · rintro ⟨h₁, h₂, d, hh, ⟨a, hP⟩, hf⟩
    exact ⟨a, h₁, h₂, d, hh, hP, hf⟩
  · rintro ⟨a, h₁, h₂, d, hh, hP, hf⟩
    exact ⟨h₁, h₂, d, hh, ⟨a, hP⟩, hf⟩

/-- `emp` is a unit for `∗`: needed because `Assert.stack S = Assert.mk S emp`,
so framing a stack-only assertion leaves an `emp ∗ H` behind. -/
@[simp] theorem HAssert.emp_star (H : HAssert) : HAssert.star HAssert.emp H = H := by
  ext ρ h
  simp only [HAssert.star, HAssert.emp]
  constructor
  · rintro ⟨h₁, h₂, -, rfl, rfl, hH⟩
    simpa using hH
  · intro hH
    exact ⟨AHeap.emp, h, AHeap.emp_disj h, (AHeap.emp_union h).symm, rfl, hH⟩

@[simp] theorem HAssert.star_emp (H : HAssert) : HAssert.star H HAssert.emp = H := by
  ext ρ h
  simp only [HAssert.star, HAssert.emp]
  constructor
  · rintro ⟨h₁, h₂, -, rfl, hH, rfl⟩
    simpa using hH
  · intro hH
    exact ⟨h, AHeap.emp, AHeap.disj_emp h, (AHeap.union_emp h).symm, hH, rfl⟩

/-- Framing a pure assertion: `(emp ∧ φ) ∗ H` is `H ∧ φ`. This is how the
`stackIf` side conditions of the basic rules survive a `[frame]`. -/
@[simp] theorem HAssert.empAnd_star (φ : Sto → Prop) (H : HAssert) :
    HAssert.star (HAssert.empAnd φ) H = HAssert.and H (HAssert.pure φ) := by
  ext ρ h
  simp only [HAssert.star, HAssert.empAnd, HAssert.and, HAssert.emp, HAssert.pure]
  constructor
  · rintro ⟨h₁, h₂, -, rfl, ⟨rfl, hφ⟩, hH⟩
    simpa using ⟨hH, hφ⟩
  · rintro ⟨hH, hφ⟩
    exact ⟨AHeap.emp, h, AHeap.emp_disj h, (AHeap.emp_union h).symm, ⟨rfl, hφ⟩, hH⟩

/-! ### Independence -/

/-- Insensitivity to a larger set of variables is a stronger property. -/
theorem Term.Indep.mono {α : Type} {X Y : Set Var} {τ : Term α} (h : Term.Indep X τ)
    (hsub : Y ⊆ X) : Term.Indep Y τ :=
  fun ρ ρ' agree => h ρ ρ' fun x hx => agree x fun hy => hx (hsub hy)

theorem HAssert.Indep.mono {X Y : Set Var} {H : HAssert} (h : HAssert.Indep X H)
    (hsub : Y ⊆ X) : HAssert.Indep Y H :=
  fun ρ ρ' hp agree => h ρ ρ' hp fun x hx => agree x fun hy => hx (hsub hy)

/-- Everything is insensitive to the empty set of variables. -/
theorem Term.indep_empty {α : Type} (τ : Term α) : Term.Indep (∅ : Set Var) τ := by
  intro ρ ρ' agree
  have hρ : ρ = ρ' := funext fun x => agree x (by simp)
  rw [hρ]

theorem HAssert.indep_empty (H : HAssert) : HAssert.Indep (∅ : Set Var) H := by
  intro ρ ρ' hp agree
  have hρ : ρ = ρ' := funext fun x => agree x (by simp)
  rw [hρ]

/-! ### Structural shorthands -/

/-- Pre-strengthening and post-weakening with the context left alone. -/
theorem Triple.conseq (h : Triple Γ P e Q) {P' Q' : Assert}
    (pre : Assert.Entails P' P) (post : Assert.Entails Q Q') : Triple Γ P' e Q' := by
  obtain ⟨F, A, L, R⟩ := Γ
  refine Triple.consequence h pre post rfl ?_ ?_
  · intro i P₁ P₁' h₁ h₂
    rw [h₁] at h₂
    obtain rfl : P₁ = P₁' := Option.some.inj h₂
    exact Assert.Entails.refl _
  · intro R₁' hR
    exact ⟨R₁', hR, Assert.Entails.refl _⟩

theorem Triple.conseqPre (h : Triple Γ P e Q) {P' : Assert} (pre : Assert.Entails P' P) :
    Triple Γ P' e Q := h.conseq pre (Assert.Entails.refl Q)

theorem Triple.conseqPost (h : Triple Γ P e Q) {Q' : Assert} (post : Assert.Entails Q Q') :
    Triple Γ P e Q' := h.conseq (Assert.Entails.refl P) post

/-- Strategy S1 of the paper's §4: a derivation whose labels are all `⊥` — one
that provably never branches out — is a derivation in *any* label context of the
same length, and with any return assertion. Specialising the labels like this is
the alternative to `Triple.frameStraight` for applying `[frame]`. -/
theorem Triple.falseLabels {F : List FuncDef} {A : FuncSpecs} {L : List Assert}
    {R : Option Assert} (h : Triple ⟨F, A, L.map fun _ => Assert.false_, none⟩ P e Q) :
    Triple ⟨F, A, L, R⟩ P e Q := by
  refine Triple.consequence h (Assert.Entails.refl P) (Assert.Entails.refl Q) (by simp) ?_ ?_
  · intro i P₁ P₁' h₁ h₂
    rw [List.getElem?_map, h₁] at h₂
    obtain rfl : Assert.false_ = P₁' := Option.some.inj h₂
    exact fun _ _ _ hf => hf.elim
  · intro R₁' hR
    exact absurd hR (by simp)

/-- Prepend one instruction to a program. -/
theorem Triple.cons {i : Silmaril.Wasm.V1.Instr} {R : Assert} (first : Triple Γ P [i] Q)
    (rest : Triple Γ Q e R) : Triple Γ P (i :: e) R := Triple.seq first rest

/-- Append one instruction to a program. -/
theorem Triple.snoc {i : Silmaril.Wasm.V1.Instr} {R : Assert} (init : Triple Γ P e Q)
    (last : Triple Γ Q [i] R) : Triple Γ P (e ++ [i]) R := Triple.seq init last

/-- `[seq]` for a goal already written as a concatenation of three parts. -/
theorem Triple.seq3 {Q₁ Q₂ R : Assert} {e₁ e₂ e₃ : Silmaril.Wasm.V1.Expr} (h₁ : Triple Γ P e₁ Q₁)
    (h₂ : Triple Γ Q₁ e₂ Q₂) (h₃ : Triple Γ Q₂ e₃ R) : Triple Γ P (e₁ ++ e₂ ++ e₃) R :=
  Triple.seq (Triple.seq h₁ h₂) h₃

/-- Transport a triple along an equality of programs, for reassociating
concatenations. -/
theorem Triple.codeEq {e' : Silmaril.Wasm.V1.Expr} (h : Triple Γ P e Q) (he : e = e') : Triple Γ P e' Q := he ▸ h

/-- The `[frame]` rule for code that neither branches nor returns: the labels
and the return are removed by `[context]` first, so only the state is framed. -/
theorem Triple.frameStraight {F : List FuncDef} {A : FuncSpecs} {L : List Assert}
    {R : Option Assert} (Hf : HAssert) (h : Triple ⟨F, A, [], none⟩ P e Q)
    (indep : HAssert.Indep (Expr.modified e) Hf) :
    Triple ⟨F, A, L, R⟩ (P.frame Hf) e (Q.frame Hf) := by
  have h₁ : Triple ⟨F, A, [], none⟩ (P.frame Hf) e (Q.frame Hf) := Triple.frame Hf h indep
  exact Triple.contextRet (Triple.context (Lf := L) h₁)

/-- `[extension]` for terms that execution cannot change, the common case. -/
theorem Triple.extendConst (S : List (Term Value)) (h : Triple Γ P e Q)
    (const : ∀ τ ∈ S, ∀ ρ ρ' : Sto, τ ρ = τ ρ') :
    Triple Γ (Assert.extend S P) e (Assert.extend S Q) :=
  Triple.extension S h fun τ hτ ρ ρ' _ => const τ hτ ρ ρ'

/-! ### Instruction rules on a larger state

Each of these is its rule from `Rules.lean`, generalised by `[extension]` over a
stack `S` and by `[frame]` over a heap assertion `H`. They are stated for a
straight-line context, which is what `Triple.frameStraight` requires; use
`Triple.context` and `Triple.contextRet` to put the labels back. -/

variable {F : List FuncDef} {A : FuncSpecs} {L : List Assert} {R : Option Assert}
variable (S : List (Term Value)) (H : HAssert)

/-- The recipe shared by every `*On` rule: `[extension]` by a stack `S` under
the operands, then `[frame]` by a heap assertion `H` beside the footprint, then
`Assert.extend_mk` and `Assert.frame_mk` to put the result back in `(S | H)`
form. `X` over-approximates the variables `e` may assign to. -/
theorem Triple.liftOn {S₁ S₂ : List (Term Value)} {H₁ H₂ : HAssert} {X : Set Var}
    (h : Triple ⟨F, A, [], none⟩ (Assert.mk S₁ H₁) e (Assert.mk S₂ H₂))
    (hmod : Expr.modified e ⊆ X) (indepS : ∀ τ ∈ S, Term.Indep X τ)
    (indepH : HAssert.Indep X H) :
    Triple ⟨F, A, L, R⟩ (Assert.mk (S ++ S₁) (HAssert.star H₁ H)) e
      (Assert.mk (S ++ S₂) (HAssert.star H₂ H)) := by
  have h₁ := Triple.extension S h fun τ hτ => (indepS τ hτ).mono hmod
  rw [Assert.extend_mk, Assert.extend_mk] at h₁
  have h₂ := Triple.frameStraight (L := L) (R := R) H h₁ (indepH.mono hmod)
  rwa [Assert.frame_mk, Assert.frame_mk] at h₂

/-- `Triple.liftOn` for an instruction sequence that assigns to no variable, so
that both independence premises are free. -/
theorem Triple.liftOnPure {S₁ S₂ : List (Term Value)} {H₁ H₂ : HAssert}
    (h : Triple ⟨F, A, [], none⟩ (Assert.mk S₁ H₁) e (Assert.mk S₂ H₂))
    (hmod : Expr.modified e = ∅) :
    Triple ⟨F, A, L, R⟩ (Assert.mk (S ++ S₁) (HAssert.star H₁ H)) e
      (Assert.mk (S ++ S₂) (HAssert.star H₂ H)) :=
  Triple.liftOn S H h (by rw [hmod]) (fun τ _ => Term.indep_empty τ) (HAssert.indep_empty H)

private theorem modified_constInstr (v : Value) : Expr.modified [constInstr v] = ∅ := by
  obtain ⟨t, bits⟩ := v
  cases t <;> simp [constInstr, Instr.modified]

theorem Triple.constOn (v : Value) :
    Triple ⟨F, A, L, R⟩ (Assert.mk S H) [constInstr v]
      (Assert.mk (S ++ [Term.const v]) H) := by
  have h₀ : Triple (⟨F, A, [], none⟩ : Ctx) (Assert.mk [] HAssert.emp) [constInstr v]
      (Assert.mk [Term.const v] HAssert.emp) := Triple.const _ v
  simpa using Triple.liftOnPure S H h₀ (modified_constInstr v)

theorem Triple.nopOn : Triple ⟨F, A, L, R⟩ (Assert.mk S H) [.nop] (Assert.mk S H) := by
  have h₀ : Triple (⟨F, A, [], none⟩ : Ctx) (Assert.mk [] HAssert.emp) [.nop]
      (Assert.mk [] HAssert.emp) := Triple.nop _
  simpa using Triple.liftOnPure S H h₀ (by simp [Instr.modified])

theorem Triple.dropOn (τ : Term Value) :
    Triple ⟨F, A, L, R⟩ (Assert.mk (S ++ [τ]) H) [.drop] (Assert.mk S H) := by
  have h₀ : Triple (⟨F, A, [], none⟩ : Ctx) (Assert.mk [τ] HAssert.emp) [.drop]
      (Assert.mk [] HAssert.emp) := Triple.drop _ τ
  simpa using Triple.liftOnPure S H h₀ (by simp [Instr.modified])

/-- Anything holds after `unreachable`, whose precondition has no models. -/
theorem Triple.unreachableOn (Q : Assert) :
    Triple ⟨F, A, L, R⟩ (Assert.mk S (HAssert.and H (HAssert.pure fun _ => False)))
      [.unreachable] Q := by
  refine Triple.conseqPre (Triple.unreachable _ Q) ?_
  rintro ρ vs h ⟨-, -, hf⟩
  exact hf.elim

theorem Triple.localGetOn (i : LocalIdx) :
    Triple ⟨F, A, L, R⟩ (Assert.mk S H) [.localGet i]
      (Assert.mk (S ++ [Term.local_ i.toNat]) H) := by
  have h₀ : Triple (⟨F, A, [], none⟩ : Ctx) (Assert.mk [] HAssert.emp) [.localGet i]
      (Assert.mk [Term.local_ i.toNat] HAssert.emp) := Triple.localGet _ i
  simpa using Triple.liftOnPure S H h₀ (by simp [Instr.modified])

theorem Triple.globalGetOn (i : GlobalIdx) :
    Triple ⟨F, A, L, R⟩ (Assert.mk S H) [.globalGet i]
      (Assert.mk (S ++ [Term.global i.toNat]) H) := by
  have h₀ : Triple (⟨F, A, [], none⟩ : Ctx) (Assert.mk [] HAssert.emp) [.globalGet i]
      (Assert.mk [Term.global i.toNat] HAssert.emp) := Triple.globalGet _ i
  simpa using Triple.liftOnPure S H h₀ (by simp [Instr.modified])

theorem Triple.intUnOpOn (t : IntType) (op : Silmaril.Wasm.V1.IntUnOp) (x : Term (BitVec t.width)) :
    Triple ⟨F, A, L, R⟩ (Assert.mk (S ++ [Term.int t x]) H) [.intUnOp t op]
      (Assert.mk (S ++ [Term.int t fun ρ => Numerics.intUnOp t op.toCore (x ρ)]) H) := by
  have h₀ : Triple (⟨F, A, [], none⟩ : Ctx) (Assert.mk [Term.int t x] HAssert.emp)
      [.intUnOp t op]
      (Assert.mk [Term.int t fun ρ => Numerics.intUnOp t op.toCore (x ρ)] HAssert.emp) :=
    Triple.intUnOp _ t op x
  simpa using Triple.liftOnPure S H h₀ (by simp [Instr.modified])

theorem Triple.intBinOpOn (t : IntType) (op : IntBinOp) (x y z : Term (BitVec t.width))
    (defined : ∀ ρ, Numerics.intBinOp t op (x ρ) (y ρ) = .ok (z ρ)) :
    Triple ⟨F, A, L, R⟩ (Assert.mk (S ++ [Term.int t x, Term.int t y]) H) [.intBinOp t op]
      (Assert.mk (S ++ [Term.int t z]) H) := by
  have h₀ : Triple (⟨F, A, [], none⟩ : Ctx)
      (Assert.mk [Term.int t x, Term.int t y]
        (HAssert.empAnd fun ρ => Numerics.intBinOp t op (x ρ) (y ρ) = .ok (z ρ)))
      [.intBinOp t op] (Assert.mk [Term.int t z] HAssert.emp) := Triple.intBinOp _ t op x y z
  have h₁ := Triple.liftOnPure (L := L) (R := R) S H h₀ (by simp [Instr.modified])
  simp only [HAssert.empAnd_star, HAssert.emp_star] at h₁
  refine Triple.conseqPre h₁ ?_
  rintro ρ vs h ⟨hvs, hH⟩
  exact ⟨hvs, hH, defined ρ⟩

theorem Triple.intRelOpOn (t : IntType) (op : IntRelOp) (x y : Term (BitVec t.width)) :
    Triple ⟨F, A, L, R⟩ (Assert.mk (S ++ [Term.int t x, Term.int t y]) H) [.intRelOp t op]
      (Assert.mk (S ++ [Term.i32 fun ρ => Numerics.intRelOp t op (x ρ) (y ρ)]) H) := by
  have h₀ : Triple (⟨F, A, [], none⟩ : Ctx)
      (Assert.mk [Term.int t x, Term.int t y] HAssert.emp) [.intRelOp t op]
      (Assert.mk [Term.i32 fun ρ => Numerics.intRelOp t op (x ρ) (y ρ)] HAssert.emp) :=
    Triple.intRelOp _ t op x y
  simpa using Triple.liftOnPure S H h₀ (by simp [Instr.modified])

theorem Triple.intTestOpOn (t : IntType) (op : IntTestOp) (x : Term (BitVec t.width)) :
    Triple ⟨F, A, L, R⟩ (Assert.mk (S ++ [Term.int t x]) H) [.intTestOp t op]
      (Assert.mk (S ++ [Term.i32 fun ρ => Numerics.intTestOp t op (x ρ)]) H) := by
  have h₀ : Triple (⟨F, A, [], none⟩ : Ctx) (Assert.mk [Term.int t x] HAssert.emp)
      [.intTestOp t op]
      (Assert.mk [Term.i32 fun ρ => Numerics.intTestOp t op (x ρ)] HAssert.emp) :=
    Triple.intTestOp _ t op x
  simpa using Triple.liftOnPure S H h₀ (by simp [Instr.modified])

theorem Triple.intLoadOn (t : IntType) (arg : Silmaril.Wasm.V1.MemArg) (a : Term (BitVec 32))
    (v : Term (BitVec t.width)) :
    Triple ⟨F, A, L, R⟩
      (Assert.mk (S ++ [Term.i32 a]) (HAssert.star (HAssert.cellNum (.int t) (memAddr arg a) v) H))
      [.intLoad t none arg]
      (Assert.mk (S ++ [Term.int t v])
        (HAssert.star (HAssert.cellNum (.int t) (memAddr arg a) v) H)) :=
  Triple.liftOnPure S H (Triple.intLoad ⟨F, A, [], none⟩ t arg a v) (by simp [Instr.modified])

theorem Triple.intStoreOn (t : IntType) (arg : Silmaril.Wasm.V1.MemArg) (a : Term (BitVec 32))
    (v : Term (BitVec t.width)) :
    Triple ⟨F, A, L, R⟩
      (Assert.mk (S ++ [Term.i32 a, Term.int t v])
        (HAssert.star (HAssert.cellNumAny (.int t) (memAddr arg a)) H))
      [.intStore t none arg]
      (Assert.mk S (HAssert.star (HAssert.cellNum (.int t) (memAddr arg a) v) H)) := by
  have h₁ := Triple.liftOnPure (L := L) (R := R) S H
    (Triple.intStore ⟨F, A, [], none⟩ t arg a v) (by simp [Instr.modified])
  simpa using h₁

/-! ### Variable-assigning instructions on a larger state

These modify a local or a global, so the surrounding stack and heap assertion
must be independent of it; that is the paper's `fv(H) ∩ mv(e*) = ∅`. -/

theorem Triple.localSetOn (i : LocalIdx) (v : Value)
    (indepS : ∀ τ ∈ S, Term.Indep {Var.loc i.toNat} τ)
    (indepH : HAssert.Indep {Var.loc i.toNat} H) :
    Triple ⟨F, A, L, R⟩ (Assert.mk (S ++ [Term.const v]) H) [.localSet i]
      (Assert.mk S (HAssert.and H (HAssert.pure fun ρ => ρ (.loc i.toNat) = v))) := by
  have h₀ : Triple (⟨F, A, [], none⟩ : Ctx) (Assert.mk [Term.const v] HAssert.emp)
      [.localSet i] (Assert.mk [] (HAssert.empAnd fun ρ => ρ (.loc i.toNat) = v)) :=
    Triple.localSet _ i v
  have h₁ := Triple.liftOn (L := L) (R := R) S H h₀ (by simp [Instr.modified]) indepS indepH
  simpa using h₁

theorem Triple.localTeeOn (i : LocalIdx) (v : Value)
    (indepS : ∀ τ ∈ S, Term.Indep {Var.loc i.toNat} τ)
    (indepH : HAssert.Indep {Var.loc i.toNat} H) :
    Triple ⟨F, A, L, R⟩ (Assert.mk (S ++ [Term.const v]) H) [.localTee i]
      (Assert.mk (S ++ [Term.const v])
        (HAssert.and H (HAssert.pure fun ρ => ρ (.loc i.toNat) = v))) := by
  have h₀ : Triple (⟨F, A, [], none⟩ : Ctx) (Assert.mk [Term.const v] HAssert.emp)
      [.localTee i]
      (Assert.mk [Term.const v] (HAssert.empAnd fun ρ => ρ (.loc i.toNat) = v)) :=
    Triple.localTee _ i v
  have h₁ := Triple.liftOn (L := L) (R := R) S H h₀ (by simp [Instr.modified]) indepS indepH
  simpa using h₁

theorem Triple.globalSetOn (i : GlobalIdx) (v : Value)
    (indepS : ∀ τ ∈ S, Term.Indep {Var.glob i.toNat} τ)
    (indepH : HAssert.Indep {Var.glob i.toNat} H) :
    Triple ⟨F, A, L, R⟩ (Assert.mk (S ++ [Term.const v]) H) [.globalSet i]
      (Assert.mk S (HAssert.and H (HAssert.pure fun ρ => ρ (.glob i.toNat) = v))) := by
  have h₀ : Triple (⟨F, A, [], none⟩ : Ctx) (Assert.mk [Term.const v] HAssert.emp)
      [.globalSet i] (Assert.mk [] (HAssert.empAnd fun ρ => ρ (.glob i.toNat) = v)) :=
    Triple.globalSet _ i v
  have h₁ := Triple.liftOn (L := L) (R := R) S H h₀ (by simp [Instr.modified]) indepS indepH
  simpa using h₁

/-- `select` on a larger state. Its postcondition is existential, so the recipe
of `Triple.liftOn` is carried out by hand through `Assert.extend_ex` and
`Assert.frame_ex`. -/
theorem Triple.selectOn (τ₁ τ₂ : Term Value) (c : Term (BitVec 32))
    (sameType : ∀ ρ, (τ₁ ρ).type = (τ₂ ρ).type) :
    Triple ⟨F, A, L, R⟩ (Assert.mk (S ++ [τ₁, τ₂, Term.i32 c]) H) [.select]
      (Assert.ex fun x : Value => Assert.mk (S ++ [Term.const x])
        (HAssert.and H (HAssert.pure fun ρ =>
          (c ρ ≠ 0 → x = τ₁ ρ) ∧ (c ρ = 0 → x = τ₂ ρ)))) := by
  have hmod : Expr.modified [Silmaril.Wasm.V1.Instr.select] ⊆ (∅ : Set Var) := by simp [Instr.modified]
  have h₀ := Triple.select (⟨F, A, [], none⟩ : Ctx) τ₁ τ₂ c sameType
  have h₁ := Triple.extension S h₀ fun τ _ => (Term.indep_empty τ).mono hmod
  have h₂ := Triple.frameStraight (L := L) (R := R) H h₁
    ((HAssert.indep_empty H).mono hmod)
  simpa [Assert.stack, Assert.stackIf, Assert.extend_mk, Assert.frame_mk, Assert.extend_ex,
    Assert.frame_ex] using h₂

end Silmaril.Wasm.Logic.V1
