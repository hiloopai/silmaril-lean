module

public import Silmaril.Wasm.Component.BinaryP3.Strict.Defs
public import Silmaril.Wasm.Component.BinaryP3.Thms

/-!
# Strict parsing: laws

For `parseStrict` (`Silmaril.Wasm.Component.BinaryP3.Strict.Defs`):

* `parseStrict_ok_iff`: it succeeds with `c` exactly when `parse` does and `c` satisfies the
  three rules (`StrictOk`);
* `parseStrict_sound`: its result is an AST of the grammar for the input, and satisfies the rules;
* `parseStrict_encode`: **round trip** for components that satisfy the rules;
* `parseStrict_functional`: at most one AST (the grammar is unambiguous);
* `parseStrict_ofV0`: **conservativity** over the old decoder, for components that satisfy the
  rules;
* `parseStrict_rejects`: a component of the grammar that breaks a rule is rejected;
* the characterisation of the rules by sections: `strictOk_mk_cons`,
  `strictOk_coreModule`, `strictOk_component`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryP3

open Silmaril.Parse.ByteParse (Error)

theorem strictOk_iff (c : Ast) : strictOk c = true ↔ StrictOk c := by
  simp only [strictOk, decide_eq_true_eq]

/-- **Strict parsing is parsing and the rules.** -/
theorem parseStrict_ok_iff {b : ByteArray} {c : Ast} :
    parseStrict b = .ok c ↔ parse b = .ok c ∧ StrictOk c := by
  unfold parseStrict
  cases h : parse b with
  | error e => simp
  | ok c' =>
    by_cases hs : StrictOk c'
    · have hb : strictOk c' = true := (strictOk_iff _).2 hs
      simp only [hb, ite_true, Except.ok.injEq]
      exact ⟨fun e => ⟨e, e ▸ hs⟩, fun h => h.1⟩
    · have hb : strictOk c' = false := by
        cases e : strictOk c'
        · rfl
        · exact absurd ((strictOk_iff _).1 e) hs
      simp only [hb, Bool.false_eq_true, ite_false, reduceCtorEq, false_iff, not_and,
        Except.ok.injEq]
      rintro rfl
      exact hs

/-- **Soundness**: the result is an AST of the grammar for the input, satisfying the rules. -/
theorem parseStrict_sound {b : ByteArray} {c : Ast} (h : parseStrict b = .ok c) :
    (componentG (b.size + 1)).G b.data.toList c ∧ StrictOk c :=
  let h' := parseStrict_ok_iff.1 h
  ⟨parse_sound h'.1, h'.2⟩

/-- **Round trip**: a component satisfying the rules is read back from its encoding. -/
theorem parseStrict_encode {c : Ast} {b : ByteArray} (h : encode c = some b) (hs : StrictOk c) :
    parseStrict b = .ok c :=
  parseStrict_ok_iff.2 ⟨parse_encode h, hs⟩

/-- **Unambiguity**: strict parsing determines the component, and any AST of the grammar for
the input is it. -/
theorem parseStrict_functional {b : ByteArray} {c c' : Ast} (h : parseStrict b = .ok c)
    (h' : (componentG (b.size + 1)).G b.data.toList c') : c' = c :=
  componentG_functional h' (parseStrict_sound h).1

/-- **Conservativity**: a component the old decoder reads, and that satisfies the rules, is read
by strict parsing as its embedding. -/
theorem parseStrict_ofV0 {b : ByteArray} {c : Binary.Ast} (h : Binary.parse b = .ok c)
    (hs : StrictOk (Ast.ofV0 c)) : parseStrict b = .ok (Ast.ofV0 c) :=
  parseStrict_ok_iff.2 ⟨parse_ofV0 h, hs⟩

/-- **Rejection**: a component that parses but breaks a rule is rejected, with the strict error. -/
theorem parseStrict_rejects {b : ByteArray} {c : Ast} (h : parse b = .ok c) (hs : ¬ StrictOk c) :
    parseStrict b = .error (strictError b) := by
  have : strictOk c = false := by
    cases e : strictOk c
    · rfl
    · exact absurd ((strictOk_iff c).1 e) hs
  simp only [parseStrict, h, this, Bool.false_eq_true, ite_false]

/-- Errors of `parse` are errors of `parseStrict`. -/
theorem parseStrict_error {b : ByteArray} {e : Error} (h : parse b = .error e) :
    parseStrict b = .error e := by
  simp only [parseStrict, h]

/-! ## The rules section by section -/

theorem collect_app_modules (a b : Collected) : (a.app b).modules = a.modules ++ b.modules := rfl
theorem collect_app_aliases (a b : Collected) : (a.app b).aliases = a.aliases ++ b.aliases := rfl
theorem collect_app_names (a b : Collected) : (a.app b).names = a.names ++ b.names := rfl

/-- The rules for a section. -/
def SectionOk (s : Section) : Prop :=
  s.collect.modules.all moduleOk = true ∧ s.collect.aliases.all aliasOk = true ∧
    s.collect.names.all nameOk = true

/-- **The rules hold in a component exactly when they hold in each of its sections.** -/
theorem strictOk_mk_cons (s : Section) (ss : List Section) :
    StrictOk (.mk (s :: ss)) ↔ SectionOk s ∧ StrictOk (.mk ss) := by
  simp only [StrictOk, SectionOk, Ast.collect, Section.collectList, collect_app_modules,
    collect_app_aliases, collect_app_names, List.all_append, Bool.and_eq_true]
  tauto

/-- The empty component satisfies the rules. -/
theorem strictOk_nil : StrictOk (.mk []) := ⟨rfl, rfl, rfl⟩

/-- A core module section satisfies the rules exactly when its bytes decode. -/
theorem sectionOk_coreModule (b : ByteArray) :
    SectionOk (.coreModule b) ↔ (Silmaril.Wasm.Binary.Core.decode? b).isSome = true := by
  simp [SectionOk, Section.collect, moduleOk]

/-- A nested component section satisfies the rules exactly when the component does. -/
theorem sectionOk_component (c : Ast) : SectionOk (.component c) ↔ StrictOk c := by
  simp only [SectionOk, StrictOk, Section.collect]

/-- An alias section satisfies the rules exactly when its aliases do. -/
theorem sectionOk_aliases (xs : List Binary.Alias) :
    SectionOk (.aliases xs) ↔ xs.all aliasOk = true := by
  simp [SectionOk, Section.collect]

/-- A `canon` section never breaks a rule. -/
theorem sectionOk_canons (xs : List Canon) : SectionOk (.canons xs) := by
  simp [SectionOk, Section.collect]

/-- **An `outer` alias of a function breaks the rules.** -/
theorem not_strictOk_outer_func (n i : Nat) :
    ¬ StrictOk (.mk [.aliases [⟨.func, .outer n i⟩]]) := by
  simp [StrictOk, Ast.collect, Section.collectList, Section.collect, Collected.app, aliasOk,
    outerSortOk]

/-- **A name with two `implements` attributes breaks the rules.** -/
theorem not_strictOk_dup_attr (x a b : String) (d : Binary.ExternDesc) :
    ¬ StrictOk (.mk [.imports [⟨⟨x, .attrs [.implements a, .implements b]⟩, d⟩]]) := by
  simp [StrictOk, Ast.collect, Section.collectList, Section.collect, Collected.app, nameOk,
    attrKind]

end Silmaril.Wasm.Component.BinaryP3

end
