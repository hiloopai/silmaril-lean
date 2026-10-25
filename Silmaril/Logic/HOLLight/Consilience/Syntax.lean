module

public import Silmaril.Logic.HOLLight.Typing
public import Mathlib.Data.Finset.Image
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

/-!
# A second term presentation for the HOL Light kernel

Types and finite signatures use the established HOL type interface. Terms,
typing, binding operations and free support are specified independently here.
Equality and choice are separate term constructors, rather than a native
constant datatype embedded in a term constructor. Binders are locally nameless;
free identities retain both their name and type, including under instantiation.
-/
namespace Silmaril.Logic.HOLLight.Consilience

inductive Term where
  | bound (index : Nat)
  | free (name : Nat) (type : Ty)
  | equality (type : Ty)
  | choice (type : Ty)
  | user (name : Nat) (instances : List Ty)
  | app (function argument : Term)
  | lam (domain : Ty) (body : Term)
  deriving DecidableEq, Repr

namespace Term

def encode : Term → Tm
  | .bound i => .bvar i
  | .free n A => .fvar n A
  | .equality A => .const (.eq A)
  | .choice A => .const (.select A)
  | .user c As => .const (.user c As)
  | .app f x => .app f.encode x.encode
  | .lam A b => .lam A b.encode

def decode : Tm → Term
  | .bvar i => .bound i
  | .fvar n A => .free n A
  | .const (.eq A) => .equality A
  | .const (.select A) => .choice A
  | .const (.user c As) => .user c As
  | .app f x => .app (decode f) (decode x)
  | .lam A b => .lam A (decode b)

@[simp] theorem decode_encode (t : Term) : decode t.encode = t := by
  induction t <;> simp_all [encode, decode]

@[simp] theorem encode_decode (t : Tm) : (decode t).encode = t := by
  induction t with
  | const c => cases c <;> rfl
  | bvar | fvar => rfl
  | app | lam => simp_all [encode, decode]

theorem encode_injective : Function.Injective encode :=
  fun _ _ h => by simpa using congrArg decode h

theorem decode_injective : Function.Injective decode :=
  fun _ _ h => by simpa using congrArg encode h

/-- A syntax equivalence, without any assertion about proof fibers. -/
def syntaxEquiv : Term ≃ Tm := ⟨encode, decode, decode_encode, encode_decode⟩

def equal (A : Ty) (s t : Term) : Term := .app (.app (.equality A) s) t

def support : Term → List (Nat × Ty)
  | .free n A => [(n, A)]
  | .app f x => f.support ++ x.support
  | .lam _ b => b.support
  | _ => []

def Fresh (v : Nat × Ty) (t : Term) : Prop := v ∉ t.support

def rename (ρ : Nat → Nat) : Term → Term
  | .bound i => .bound (ρ i)
  | .app f x => .app (f.rename ρ) (x.rename ρ)
  | .lam A b => .lam A (b.rename (DeBruijn.lift ρ))
  | t => t

def weaken (t : Term) : Term := t.rename Nat.succ

def liftSub (σ : Nat → Term) : Nat → Term
  | 0 => .bound 0
  | i + 1 => (σ i).weaken

def subst (σ : Nat → Term) : Term → Term
  | .bound i => σ i
  | .app f x => .app (f.subst σ) (x.subst σ)
  | .lam A b => .lam A (b.subst (liftSub σ))
  | t => t

def openSub (x : Term) : Nat → Term
  | 0 => x
  | i + 1 => .bound i

def «open» (b x : Term) : Term := b.subst (openSub x)

def freeSubst (σ : Nat → Ty → Term) : Term → Term
  | .free n A => σ n A
  | .app f x => .app (f.freeSubst σ) (x.freeSubst σ)
  | .lam A b => .lam A (b.freeSubst (fun n B => (σ n B).weaken))
  | t => t

def replaceFree (t : Term) (v : Nat × Ty) (x : Term) : Term :=
  t.freeSubst (fun n A => if (n, A) = v then x else .free n A)

def tySubst (σ : Nat → Ty) : Term → Term
  | .bound i => .bound i
  | .free n A => .free n (A.subst σ)
  | .equality A => .equality (A.subst σ)
  | .choice A => .choice (A.subst σ)
  | .user c As => .user c (As.map (Ty.subst σ))
  | .app f x => .app (f.tySubst σ) (x.tySubst σ)
  | .lam A b => .lam (A.subst σ) (b.tySubst σ)

@[simp] theorem encode_equal (A : Ty) (s t : Term) :
    (equal A s t).encode = Tm.equal A s.encode t.encode := rfl

@[simp] theorem encode_support (t : Term) : t.encode.freeVars = t.support := by
  induction t <;> simp_all [encode, support, Tm.freeVars]

@[simp] theorem encode_fresh (v : Nat × Ty) (t : Term) :
    t.encode.Fresh v ↔ t.Fresh v := by simp [Fresh, Tm.Fresh]

@[simp] theorem encode_rename (t : Term) (ρ : Nat → Nat) :
    (t.rename ρ).encode = t.encode.rename ρ := by
  induction t generalizing ρ <;> simp_all [encode, rename, Tm.rename]

@[simp] theorem encode_weaken (t : Term) : t.weaken.encode = t.encode.weaken :=
  encode_rename t _

theorem encode_liftSub (σ : Nat → Term) :
    (fun i => (liftSub σ i).encode) = Tm.liftSub (fun i => (σ i).encode) := by
  funext i
  cases i <;> simp [liftSub, Tm.liftSub, encode]

@[simp] theorem encode_subst (t : Term) (σ : Nat → Term) :
    (t.subst σ).encode = t.encode.subst (fun i => (σ i).encode) := by
  induction t generalizing σ <;> simp_all [encode, subst, Tm.subst, encode_liftSub]

@[simp] theorem encode_open (b x : Term) :
    (b.open x).encode = b.encode.open x.encode := by
  simp only [«open», Tm.«open», encode_subst]
  congr 1
  funext i
  cases i <;> rfl

@[simp] theorem encode_freeSubst (t : Term) (σ : Nat → Ty → Term) :
    (t.freeSubst σ).encode = t.encode.freeSubst (fun n A => (σ n A).encode) := by
  induction t generalizing σ <;> simp_all [encode, freeSubst, Tm.freeSubst]

@[simp] theorem encode_replaceFree (t : Term) (v : Nat × Ty) (x : Term) :
    (t.replaceFree v x).encode = t.encode.replaceFree v x.encode := by
  simp only [replaceFree, Tm.replaceFree, encode_freeSubst]
  congr 1
  funext n A
  split <;> rfl

@[simp] theorem encode_tySubst (t : Term) (σ : Nat → Ty) :
    (t.tySubst σ).encode = t.encode.tySubst σ := by
  induction t <;> simp_all [encode, tySubst, Tm.tySubst, Const.tySubst]

@[simp] theorem decode_equal (A : Ty) (s t : Tm) :
    decode (Tm.equal A s t) = equal A (decode s) (decode t) := rfl

@[simp] theorem decode_fresh (v : Nat × Ty) (t : Tm) :
    (decode t).Fresh v ↔ t.Fresh v := by
  rw [← encode_fresh, encode_decode]

@[simp] theorem decode_open (b x : Tm) : decode (b.open x) = (decode b).open (decode x) := by
  apply encode_injective
  simp

@[simp] theorem decode_replaceFree (t : Tm) (v : Nat × Ty) (x : Tm) :
    decode (t.replaceFree v x) = (decode t).replaceFree v (decode x) := by
  apply encode_injective
  simp

@[simp] theorem decode_freeSubst (t : Tm) (σ : Nat → Ty → Tm) :
    decode (t.freeSubst σ) = (decode t).freeSubst (fun n A => decode (σ n A)) := by
  apply encode_injective
  simp

@[simp] theorem decode_tySubst (t : Tm) (σ : Nat → Ty) :
    decode (t.tySubst σ) = (decode t).tySubst σ := by
  apply encode_injective
  simp

end Term

/-- Separate declarative typing; no premise appeals to native term typing. -/
inductive Typed (sig : Signature) : List Ty → Term → Ty → Prop where
  | bound {Γ i A} (lookup : Γ[i]? = some A) (wf : A.WellFormed sig.tyOps) :
      Typed sig Γ (.bound i) A
  | free {Γ A} (n : Nat) (wf : A.WellFormed sig.tyOps) : Typed sig Γ (.free n A) A
  | equality {Γ A} (wf : A.WellFormed sig.tyOps) :
      Typed sig Γ (.equality A) (.arr A (.arr A .bool))
  | choice {Γ A} (wf : A.WellFormed sig.tyOps) :
      Typed sig Γ (.choice A) (.arr (.arr A .bool) A)
  | user {Γ c s As} (lookup : sig.consts[c]? = some s) (scheme : s.WellFormed sig.tyOps)
      (arity : As.length = s.arity) (args : ∀ A ∈ As, A.WellFormed sig.tyOps) :
      Typed sig Γ (.user c As) (s.body.instantiate As)
  | app {Γ f x A B} : Typed sig Γ f (.arr A B) → Typed sig Γ x A →
      Typed sig Γ (.app f x) B
  | lam {Γ A B b} (wf : A.WellFormed sig.tyOps) :
      Typed sig (A :: Γ) b B → Typed sig Γ (.lam A b) (.arr A B)

namespace Typed

theorem encode {sig Γ t A} (h : Typed sig Γ t A) : HasType sig Γ t.encode A := by
  induction h with
  | bound lookup wf => exact .bvar lookup wf
  | free n wf => exact .fvar n wf
  | equality wf => exact .const (.eq wf)
  | choice wf => exact .const (.select wf)
  | user lookup scheme arity args => exact .const (.user lookup scheme arity args)
  | app _ _ ihf ihx => exact .app ihf ihx
  | lam wf _ ih => exact .lam wf ih

theorem decode {sig Γ t A} (h : HasType sig Γ t A) : Typed sig Γ (Term.decode t) A := by
  induction h with
  | bvar lookup wf => exact .bound lookup wf
  | fvar n wf => exact .free n wf
  | const hc =>
    cases hc with
    | eq wf => exact .equality wf
    | select wf => exact .choice wf
    | user lookup scheme arity args => exact .user lookup scheme arity args
  | app _ _ ihf ihx => exact .app ihf ihx
  | lam wf _ ih => exact .lam wf ih

@[simp] theorem encode_iff {sig Γ t A} : HasType sig Γ t.encode A ↔ Typed sig Γ t A :=
  ⟨fun h => by simpa using decode h, encode⟩

@[simp] theorem decode_iff {sig Γ t A} : Typed sig Γ (Term.decode t) A ↔ HasType sig Γ t A :=
  ⟨fun h => by simpa using encode h, decode⟩

end Typed

structure Formula (sig : Signature) where
  term : Term
  typing : Typed sig [] term .bool

structure Sequent where
  hyps : Finset Term
  conclusion : Term

end Silmaril.Logic.HOLLight.Consilience
