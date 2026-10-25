module

public import Silmaril.Logic.Metamath.Syntax
public import Silmaril.Logic.Metatheory.Theory.Model

@[expose] public section

/-!
# Metamath grammars

A syntax axiom is an axiom such as `wi $a wff ( ph -> ps ) $.`: its typecode is
a syntax typecode, it has no essential hypotheses and no disjointness
conditions, and its body mentions each of its variables exactly once. It is a
production of a many-sorted context-free grammar whose nonterminals are the
syntax typecodes (Carneiro, *Models for Metamath*, 2016, §2.3).

A grammar packages labelled syntax rules, the set of syntax typecodes, and the
syntax typecode of each provable typecode (`|-` is read as `wff`). This is
Carneiro's `Syn` restricted to provable typecodes. The syntax rules form a
many-sorted signature (`Metatheory.TheoryModel.Signature`), whose algebras
interpret the syntax of the system.
-/

namespace Silmaril.Logic.Metamath

open Silmaril.Logic.Metatheory.TheoryModel

universe u

variable {C V : Type u}

namespace Grammar

/-- The entry for `v` in a list of values indexed by the variables of `ps`.
The first occurrence of `v` wins; `none` if `v` is absent. -/
def lookupArg {α : Type*} [DecidableEq V] : List (C × V) → List α → V → Option α
  | p :: ps, a :: as, v => if p.2 = v then some a else lookupArg ps as v
  | _, _, _ => none

section lookupArg

variable {α β : Type*} [DecidableEq V]

@[simp] theorem lookupArg_nil_left (as : List α) (v : V) :
    lookupArg ([] : List (C × V)) as v = none := rfl

@[simp] theorem lookupArg_nil_right (ps : List (C × V)) (v : V) :
    lookupArg ps ([] : List α) v = none := by
  cases ps <;> rfl

theorem lookupArg_cons (p : C × V) (ps : List (C × V)) (a : α) (as : List α) (v : V) :
    lookupArg (p :: ps) (a :: as) v = if p.2 = v then some a else lookupArg ps as v := rfl

theorem lookupArg_map (f : α → β) (ps : List (C × V)) (as : List α) (v : V) :
    lookupArg ps (as.map f) v = (lookupArg ps as v).map f := by
  induction ps generalizing as with
  | nil => rfl
  | cons p ps ih =>
    cases as with
    | nil => rfl
    | cons a as => simp only [List.map_cons, lookupArg_cons, ih]; split <;> rfl

/-- A successful lookup comes from a pair of the zipped lists. -/
theorem lookupArg_eq_some {ps : List (C × V)} {as : List α} {v : V} {a : α}
    (h : lookupArg ps as v = some a) : ∃ p, (a, p) ∈ as.zip ps ∧ p.2 = v := by
  induction ps generalizing as with
  | nil => simp at h
  | cons p ps ih =>
    cases as with
    | nil => simp at h
    | cons b as =>
      rw [lookupArg_cons] at h
      split at h
      · cases h; exact ⟨p, by simp, by assumption⟩
      · obtain ⟨q, hq, rfl⟩ := ih h
        exact ⟨q, by simp [hq], rfl⟩

/-- With distinct variables, every zipped pair is found by its variable. -/
theorem lookupArg_of_mem_zip {ps : List (C × V)} {as : List α} (hnd : (ps.map Prod.snd).Nodup)
    {p : C × V} {a : α} (h : (a, p) ∈ as.zip ps) : lookupArg ps as p.2 = some a := by
  induction ps generalizing as with
  | nil => simp at h
  | cons q ps ih =>
    cases as with
    | nil => simp at h
    | cons b as =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
      rw [lookupArg_cons]
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · simp
      · have hp : p ∈ ps := (List.of_mem_zip h).2
        simp only [show ¬ q.2 = p.2 from fun e => hnd.1 p hp e.symm, ite_false]
        exact ih hnd.2 h

/-- A lookup succeeds for every listed variable when the lists have equal length. -/
theorem lookupArg_isSome {ps : List (C × V)} {as : List α} (hlen : as.length = ps.length)
    {v : V} (hv : v ∈ ps.map Prod.snd) : ∃ p a, (a, p) ∈ as.zip ps ∧ p.2 = v ∧
      lookupArg ps as v = some a := by
  induction ps generalizing as with
  | nil => simp at hv
  | cons q ps ih =>
    cases as with
    | nil => simp at hlen
    | cons b as =>
      rw [lookupArg_cons]
      by_cases hq : q.2 = v
      · exact ⟨q, b, by simp, hq, by simp [hq]⟩
      · simp only [List.map_cons, List.mem_cons] at hv
        obtain ⟨p, a, hm, hp, hl⟩ :=
          ih (by simpa using hlen) (hv.resolve_left (Ne.symm hq))
        exact ⟨p, a, by simp [hm], hp, by simp [hq, hl]⟩

/-- Lists of the same length as `ps` agree when all their lookups agree. -/
theorem lookupArg_ext {ps : List (C × V)} {as bs : List α} (hnd : (ps.map Prod.snd).Nodup)
    (ha : as.length = ps.length) (hb : bs.length = ps.length)
    (h : ∀ p ∈ ps, lookupArg ps as p.2 = lookupArg ps bs p.2) : as = bs := by
  induction ps generalizing as bs with
  | nil => rw [List.length_eq_zero_iff.1 ha, List.length_eq_zero_iff.1 hb]
  | cons q ps ih =>
    cases as with
    | nil => simp at ha
    | cons a as =>
      cases bs with
      | nil => simp at hb
      | cons b bs =>
        simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
        have hq := h q (by simp)
        simp only [lookupArg_cons, ite_true, Option.some.injEq] at hq
        subst hq
        congr 1
        refine ih hnd.2 (by simpa using ha) (by simpa using hb) fun p hp => ?_
        have hne : ¬ q.2 = p.2 := fun e => hnd.1 p hp e.symm
        have := h p (by simp [hp])
        simpa [lookupArg_cons, hne] using this

end lookupArg

/-- A syntax rule: the floating hypotheses `args` in database order, the
result typecode `tc`, and a body mentioning each variable of `args` exactly
once. The axiom `wi $a wff ( ph -> ps ) $.` has `args = [(wff, ph), (wff, ps)]`. -/
structure SyntaxRule (C V : Type u) where
  tc : C
  args : List (C × V)
  body : Str C V
  args_nodup : (args.map Prod.snd).Nodup
  body_perm : (Str.vars body).Perm (args.map Prod.snd)

namespace SyntaxRule

/-- The syntax axiom as a Metamath assertion. -/
def toAssertion (r : SyntaxRule C V) : Assertion C V where
  dv := []
  hyps := r.args.map fun p => .float p.1 p.2
  concl := ⟨r.tc, r.body⟩

/-- The number of arguments. -/
abbrev arity (r : SyntaxRule C V) : Nat := r.args.length

variable [DecidableEq V]

/-- The sort of an argument variable. -/
def argSort (r : SyntaxRule C V) (v : V) : Option C :=
  lookupArg r.args (r.args.map Prod.fst) v

/-- The grammar symbol of a body symbol: a constant, or the nonterminal given
by the sort of an argument variable. -/
def itemOf (r : SyntaxRule C V) : Sym C V → Option (Sym C C)
  | .const c => some (.const c)
  | .var v => (r.argSort v).map .var

/-- The grammar symbols of the body. -/
def items (r : SyntaxRule C V) : List (Sym C C) := r.body.filterMap r.itemOf

theorem argSort_of_mem {r : SyntaxRule C V} {p : C × V} (hp : p ∈ r.args) :
    r.argSort p.2 = some p.1 := by
  have h : ∀ ps : List (C × V), p ∈ ps → (p.1, p) ∈ (ps.map Prod.fst).zip ps := by
    intro ps hps
    induction ps with
    | nil => simp at hps
    | cons q ps ih =>
      rcases List.mem_cons.1 hps with rfl | hps
      · simp
      · simp [ih hps]
  exact lookupArg_of_mem_zip r.args_nodup (h _ hp)

omit [DecidableEq V] in
theorem mem_args_of_mem_body {r : SyntaxRule C V} {v : V} (h : Sym.var v ∈ r.body) :
    v ∈ r.args.map Prod.snd :=
  r.body_perm.subset (Str.mem_vars.2 h)

end SyntaxRule

end Grammar

/-- An assertion is a syntax axiom over the syntax typecodes `S`. -/
def Assertion.IsSyntaxAxiom (S : Set C) (A : Assertion C V) : Prop :=
  ∃ r : Grammar.SyntaxRule C V, r.toAssertion = A ∧ r.tc ∈ S ∧ ∀ p ∈ r.args, p.1 ∈ S

/-- A grammar: labelled syntax rules over the syntax typecodes `sorts`, and the
syntax typecode `prov c` of each provable typecode `c`. Provable typecodes are
not syntax typecodes. -/
structure Grammar (L C V : Type u) where
  sorts : Set C
  prov : C → Option C
  rule : L → Grammar.SyntaxRule C V
  rule_tc : ∀ l, (rule l).tc ∈ sorts
  rule_args : ∀ l, ∀ p ∈ (rule l).args, p.1 ∈ sorts
  prov_sort : ∀ {c s}, prov c = some s → s ∈ sorts
  prov_not_sort : ∀ {c s}, prov c = some s → c ∉ sorts

namespace Grammar

variable {L : Type u} (G : Grammar L C V)

/-- The syntax axioms of the grammar, as Metamath assertions. -/
def syntaxAxioms : Set (Assertion C V) := Set.range fun l => (G.rule l).toAssertion

theorem isSyntaxAxiom_of_mem {A : Assertion C V} (h : A ∈ G.syntaxAxioms) :
    A.IsSyntaxAxiom G.sorts := by
  obtain ⟨l, rfl⟩ := h
  exact ⟨G.rule l, rfl, G.rule_tc l, G.rule_args l⟩

/-- The many-sorted signature of the grammar: operations of sort `s` are the
rules producing `s`, and argument sorts are the sorts of their floating
hypotheses. -/
abbrev signature : Signature.{u, u} C where
  Op s := {l : L // (G.rule l).tc = s}
  arity o := (G.rule o.1).arity
  argSort o j := ((G.rule o.1).args.get j).1

end Grammar

end Silmaril.Logic.Metamath
