module

public import Silmaril.Logic.SetTheory.Inductive.ZF
public import Silmaril.Logic.Metamath.Peano.ZFC

@[expose] public section

/-!
# Certified finite membership syntax bridge to the native ZF grammar

`encode`/`decode` compare independently defined finite named syntax with actual
native syntax trees. Only class expressions of the form `cv setvar` belong to
this fragment. Formula/class metavariables and larger class definitions are
outside it. The scoped encoder permits an explicit binder-name stream; its
semantic use requires freshness, rather than silently identifying names.
-/

namespace Silmaril.Logic.SetTheory.Inductive.MetamathZF

open Silmaril.Logic.Metamath Grammar

namespace Native

abbrev V := Peano.ZF.V
abbrev L := Peano.ZF.L
abbrev C := Peano.ZF.C
abbrev grammar := Peano.ZF.grammar

end Native

namespace T

export Peano.ZF.T (weq wel wn wi wb wa wo wal wex pf)

end T

-- Native variable constructors share ordinary binder names.
set_option linter.constructorNameAsVariable false

/-- Encode independent named formulas into the actual native ZF trees. -/
def encode : Named.Formula Native.V → Tree Native.L Native.V
  | .eq x y => T.weq x y
  | .mem x y => T.wel x y
  | .neg p => T.wn (encode p)
  | .imp p q => T.wi (encode p) (encode q)
  | .iff p q => T.wb (encode p) (encode q)
  | .conj p q => T.wa (encode p) (encode q)
  | .disj p q => T.wo (encode p) (encode q)
  | .all x p => T.wal x (encode p)
  | .ex x p => T.wex x (encode p)

/-- Partial inverse: reject class metavariables, malformed arities and wff metavariables. -/
def decode : Tree Native.L Native.V → Option (Named.Formula Native.V)
  | .node .wceq [.node .cv [.var x], .node .cv [.var y]] => some (.eq x y)
  | .node .wcel [.node .cv [.var x], .node .cv [.var y]] => some (.mem x y)
  | .node .wn [p] => .neg <$> decode p
  | .node .wi [p, q] => .imp <$> decode p <*> decode q
  | .node .wb [p, q] => .iff <$> decode p <*> decode q
  | .node .wa [p, q] => .conj <$> decode p <*> decode q
  | .node .wo [p, q] => .disj <$> decode p <*> decode q
  | .node .wal [p, .var x] => .all x <$> decode p
  | .node .wex [p, .var x] => .ex x <$> decode p
  | _ => none

@[simp] theorem decode_encode (p : Named.Formula Native.V) : decode (encode p) = some p := by
  induction p <;> simp [encode, decode, *]

/-- Encoding loses no finite syntactic information. -/
theorem encode_injective : Function.Injective encode := by
  intro p q h
  have := congrArg decode h
  simpa using this

/-- The syntactic variable list, including binders, agrees exactly with the native list. -/
@[simp] theorem vars_encode (p : Named.Formula Native.V) : (encode p).vars = p.vars := by
  induction p <;> simp [encode, Named.Formula.vars, *]

/-- Lower a scoped formula to named syntax with an explicit binder-name supply.
Freshness is a separate semantic obligation; this function alone does not assert it. -/
def name {n : Nat} (p : Formula n) (ρ : Fin n → Native.V) (fresh : Nat → Native.V) :
    Named.Formula Native.V :=
  match p with
  | .bot => .neg (.all (fresh 0) (.eq (fresh 0) (fresh 0)))
  | .eq x y => .eq (ρ x) (ρ y)
  | .mem x y => .mem (ρ x) (ρ y)
  | .neg p => .neg (name p ρ fresh)
  | .imp p q => .imp (name p ρ fresh) (name q ρ fresh)
  | .iff p q => .iff (name p ρ fresh) (name q ρ fresh)
  | .conj p q => .conj (name p ρ fresh) (name q ρ fresh)
  | .disj p q => .disj (name p ρ fresh) (name q ρ fresh)
  | .all p => .all (fresh 0) (name p (Fin.cons (fresh 0) ρ) (fresh ∘ Nat.succ))
  | .ex p => .ex (fresh 0) (name p (Fin.cons (fresh 0) ρ) (fresh ∘ Nat.succ))

/-- Scoped syntax to the native tree language. -/
def encodeScoped {n : Nat} (p : Formula n) (ρ : Fin n → Native.V) (fresh : Nat → Native.V) :
    Tree Native.L Native.V := encode (name p ρ fresh)

/-- Fresh binder names make scoped naming semantically capture avoiding. -/
theorem eval_name {M : Type*} [Membership M M] {n : Nat} (p : Formula n)
    (ρ : Fin n → Native.V) (fresh : Nat → Native.V)
    (hinj : Function.Injective fresh) (hdisj : ∀ i j, fresh i ≠ ρ j)
    (E : Native.V → M) : (name p ρ fresh).eval E ↔ p.eval (E ∘ ρ) := by
  induction p generalizing fresh E with
  | bot => simp [name, Named.Formula.eval, Formula.eval]
  | eq x y | mem x y => rfl
  | neg p ih => exact not_congr (ih _ _ hinj hdisj E)
  | imp p q ih iq => exact imp_congr (ih _ _ hinj hdisj E) (iq _ _ hinj hdisj E)
  | iff p q ih iq => exact iff_congr (ih _ _ hinj hdisj E) (iq _ _ hinj hdisj E)
  | conj p q ih iq => exact and_congr (ih _ _ hinj hdisj E) (iq _ _ hinj hdisj E)
  | disj p q ih iq => exact or_congr (ih _ _ hinj hdisj E) (iq _ _ hinj hdisj E)
  | @all n p ih | @ex n p ih =>
    have hi : Function.Injective (fresh ∘ Nat.succ) := hinj.comp Nat.succ_injective
    have hd : ∀ i (j : Fin (n + 1)), (fresh ∘ Nat.succ) i ≠ Fin.cons (α := fun _ => Native.V) (fresh 0) ρ j := by
      intro i j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact fun h => Nat.succ_ne_zero i (hinj h)
      · exact hdisj (i + 1) j
    have he : ∀ a, Function.update E (fresh 0) a ∘ Fin.cons (fresh 0) ρ = Fin.cons a (E ∘ ρ) := by
      intro a
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · exact Function.update_of_ne (Ne.symm (hdisj 0 j)) a E
    have hh := fun a => (ih _ _ hi hd (Function.update E (fresh 0) a)).trans (by rw [he])
    first | exact forall_congr' hh | exact exists_congr hh

/-- Tarski satisfaction is preserved by the exact named encoding. -/
theorem sem_encode {M : Type*} [Membership M M] (p : Named.Formula Native.V)
    (E : Native.V → M) : Peano.ZF.sem id (encode p) E ↔ p.eval E := by
  induction p generalizing E <;> simp [encode, Named.Formula.eval, *]

/-- Scoped-to-native semantic correspondence with its binder freshness assumptions explicit. -/
theorem sem_encodeScoped {M : Type*} [Membership M M] {n : Nat} (p : Formula n)
    (ρ : Fin n → Native.V) (fresh : Nat → Native.V)
    (hinj : Function.Injective fresh) (hdisj : ∀ i j, fresh i ≠ ρ j)
    (E : Native.V → M) : Peano.ZF.sem id (encodeScoped p ρ fresh) E ↔ p.eval (E ∘ ρ) := by
  exact (sem_encode (name p ρ fresh) E).trans (eval_name p ρ fresh hinj hdisj E)

/-- Encodings are well sorted in any frame declaring their names as set variables. -/
theorem encode_sorted (p : Named.Formula Native.V) {ctx : Native.V → Native.C → Prop}
    (hctx : ∀ v, ctx v .setvar) : Native.grammar.HasSort ctx (encode p) .wff := by
  have cv : ∀ x, Native.grammar.HasSort ctx (.node .cv [.var x]) .class := by
    intro x
    refine .node rfl ?_
    intro a ha
    simp [Native.grammar, Peano.ZF.grammar, Peano.ZF.rules] at ha
    subst a
    exact .var (hctx x)
  induction p with
  | eq x y | mem x y =>
    refine .node rfl ?_
    intro a ha
    simp [Native.grammar, Peano.ZF.grammar, Peano.ZF.rules] at ha
    rcases ha with rfl | rfl <;> exact cv _
  | neg p ih =>
    refine .node rfl ?_
    intro a ha
    simp [Native.grammar, Peano.ZF.grammar, Peano.ZF.rules] at ha
    subst a
    exact ih
  | imp p q ih iq | iff p q ih iq | conj p q ih iq | disj p q ih iq =>
    refine .node rfl ?_
    intro a ha
    simp [Native.grammar, Peano.ZF.grammar, Peano.ZF.rules] at ha
    rcases ha with rfl | rfl
    · exact ih
    · exact iq
  | all x p ih | ex x p ih =>
    refine .node rfl ?_
    intro a ha
    simp [Native.grammar, Peano.ZF.grammar, Peano.ZF.rules] at ha
    rcases ha with rfl | rfl
    · exact ih
    · exact .var (hctx x)

/-- Sort transport restricted to names that actually occur in a tree. -/
theorem sorted_on_vars {ctx ctx' : Native.V → Native.C → Prop}
    {t : Tree Native.L Native.V} {s : Native.C}
    (h : Native.grammar.HasSort ctx t s)
    (hctx : ∀ v ∈ t.vars, ∀ c, ctx v c → ctx' v c) :
    Native.grammar.HasSort ctx' t s := by
  induction h with
  | var hv => exact .var (hctx _ (by simp) _ hv)
  | @node l args hlen hargs ih =>
    refine .node hlen ?_
    intro a ha
    apply ih a ha
    intro v hv c hc
    apply hctx v ?_ c hc
    simpa only [Tree.vars_node] using
      (List.mem_flatMap).mpr ⟨a.1, (List.of_mem_zip ha).1, hv⟩

/-- Finite-frame sorting needs declarations only for the formula's occurring names. -/
theorem encode_sorted_on_vars (p : Named.Formula Native.V)
    {ctx : Native.V → Native.C → Prop} (hctx : ∀ v ∈ p.vars, ctx v .setvar) :
    Native.grammar.HasSort ctx (encode p) .wff := by
  apply sorted_on_vars (encode_sorted p (ctx := Peano.ZF.setCtx) (fun _ => rfl))
  intro v hv c hc
  cases hc
  exact hctx v (by simpa using hv)

/-- The named encoding lies in the native pure membership fragment. -/
theorem encode_pure (p : Named.Formula Native.V) : Peano.ZF.IsPure (encode p) :=
  encode_sorted p (fun _ => rfl)

/-- Every native pure formula comes from an independent finite formula. -/
theorem pure_exists_encode (t : Tree Native.L Native.V) (h : Peano.ZF.IsPure t) :
    ∃ p : Named.Formula Native.V, encode p = t := by
  induction t using Tree.induction with
  | var v => cases h with | var hv => cases hv
  | node l args ih =>
    rcases h.cases with ⟨a, e, ha⟩ | ⟨l', a, b, e, hl, ha, hb⟩ | ⟨l', a, x, e, hl, ha⟩ |
      ⟨l', x, y, e, hl⟩ <;> cases e
    · obtain ⟨p, rfl⟩ := ih a (by simp) ha
      exact ⟨.neg p, rfl⟩
    · obtain ⟨p, rfl⟩ := ih a (by simp) ha
      obtain ⟨q, rfl⟩ := ih b (by simp) hb
      rcases hl with rfl | rfl | rfl | rfl
      · exact ⟨.imp p q, rfl⟩
      · exact ⟨.iff p q, rfl⟩
      · exact ⟨.conj p q, rfl⟩
      · exact ⟨.disj p q, rfl⟩
    · obtain ⟨p, rfl⟩ := ih a (by simp) ha
      rcases hl with rfl | rfl
      · exact ⟨.all x p, rfl⟩
      · exact ⟨.ex x p, rfl⟩
    · rcases hl with rfl | rfl
      · exact ⟨.eq x y, rfl⟩
      · exact ⟨.mem x y, rfl⟩

/-- Exact syntax coverage, rather than agreement only in a particular model. -/
theorem pure_iff_encoded (t : Tree Native.L Native.V) :
    Peano.ZF.IsPure t ↔ ∃ p : Named.Formula Native.V, encode p = t := by
  constructor
  · exact pure_exists_encode t
  · rintro ⟨p, rfl⟩
    exact encode_pure p

/-- Renaming an environment commutes with named binders when names are distinct. -/
theorem sem_encode_names {M N : Type*} [Membership M M] [DecidableEq N]
    (nm : Native.V → N) (hinj : Function.Injective nm) (p : Named.Formula Native.V)
    (E : N → M) : Peano.ZF.sem nm (encode p) E ↔ p.eval (E ∘ nm) := by
  induction p generalizing E with
  | eq x y | mem x y => rfl
  | neg p ih => exact not_congr (ih E)
  | imp p q ih iq => exact imp_congr (ih E) (iq E)
  | iff p q ih iq => exact iff_congr (ih E) (iq E)
  | conj p q ih iq => exact and_congr (ih E) (iq E)
  | disj p q ih iq => exact or_congr (ih E) (iq E)
  | all x p ih | ex x p ih =>
    have hh := fun a => (ih (Function.update E (nm x) a)).trans (by
      have he' : Function.update E (nm x) a ∘ nm = Function.update (E ∘ nm) x a := by
        funext v
        by_cases h : v = x
        · simp [h]
        · have hn : nm v ≠ nm x := fun hv => h (hinj hv)
          simp [Function.comp_def, Function.update_of_ne h, Function.update_of_ne hn]
      rw [he'])
    first | exact forall_congr' hh | exact exists_congr hh

/-- The native environment model agrees with independent finite Tarski syntax.
This theorem is semantic and makes no proof-system completeness claim. -/
theorem value_encode {M N : Type 1} [Membership M M] [DecidableEq N] [Infinite N]
    {ctx : Native.V → Native.C → Prop} (ρ : (Peano.ZF.model M N).Valuation ctx)
    (nm : Native.V → N) (hinj : Function.Injective nm) (hnm : ∀ a h, ρ a .setvar h = nm a)
    (hext : Silmaril.Logic.Metamath.Model.SetMM.Extensional M)
    (p : Named.Formula Native.V)
    (ht : Native.grammar.HasSort (Native.grammar.synCtx ctx) (encode p) .wff)
    (E : N → M) :
    ((Peano.ZF.model M N).value ρ (encode p) ht : Env.Term M N Prop).1 E ↔
      p.eval (E ∘ nm) := by
  have hp := Peano.ZF.value_pure ρ nm hnm hext (encode p) (encode_pure p) ht E
  exact hp.trans (sem_encode_names nm hinj p E)

end Silmaril.Logic.SetTheory.Inductive.MetamathZF
