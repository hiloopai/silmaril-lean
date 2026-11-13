module

public import Silmaril.Compiler.Mir.Semantics.Defs
public import Silmaril.Compile.Category.Pass

@[expose] public section

/-!
# Mir in SSA form: a worked example of the pass API

`ssaLang cfg` is the language of Mir programs in **static single assignment** form (every
virtual register of a function is written by one instruction or parameter: `IsSSA`), with
the semantics of Mir. It is the smallest SSA language of the zoo, and the worked example of
`Silmaril.Compile.Category.Pass`:

* `lift : Pass up` (Mir → Mir.SSA) checks the SSA condition (a compile-time failure
  otherwise); `lower : Pass down` (Mir.SSA → Mir) forgets it; together they are a
  `RoundTrip` (`roundTrip`), since `up ≫ down = 𝟙`;
* any optimization `E : EndoPass (ssaLang cfg)` conjugates to an optimization of Mir
  (`roundTrip.conj E`), and composing with `Mir.linkCompiler` gives a Mir → Lir pipeline
  whose end-to-end validity follows from the parts alone (`optimizeAndLink_sound`), for
  **every** `E`; `pipeline_sound` is the same for an explicit `Pipeline` value
  Mir → SSA → SSA → Mir → Lir.

The real SSA languages of the zoo (`Machine.RTL.SSA`, Isotope λSSA/LetIter,
docs/RTLSSALambdaSSA.md) take the place of `ssaLang` with a lift that renames registers and
inserts φ-nodes; the composition is unchanged.
-/

namespace Silmaril.Compile.Mir

open Silmaril.Machine
open Silmaril.Compile.Category
open CategoryTheory

/-! ## SSA form -/

/-- Registers written by an instruction. -/
def Instr.defs : Instr → List Reg
  | .op (.const d _) | .op (.move d _) | .op (.unary _ d _) | .op (.binary _ d _ _)
  | .op (.load _ _ d _ _) | .op (.slotGet d _) | .addr d _ _ => [d]
  | .op (.store ..) | .op (.slotSet ..) => []
  | .call _ _ rs | .callIndirect _ _ rs => rs
  | .fop _ d _ _ => [d]

/-- Registers written in a function: its parameters, then every instruction's results. -/
def Func.defs (f : Func) : List Reg :=
  f.params ++ (f.blocks.toList.flatMap fun b => b.instrs.toList.flatMap Instr.defs)

/-- Static single assignment: no register of a function is written twice. -/
def IsSSA (us : Array Unit) : Bool :=
  us.all fun u => u.funcs.all fun f => decide f.defs.Nodup

/-- Mir programs in SSA form, with the semantics of Mir. -/
def ssaLang (cfg : Config) : Language.{0} :=
  ⟨PUnit, {us : Array Unit // IsSSA us = true}, fun _ => ⟨⟩, LirOutcome, fun q => beh cfg q.1⟩

/-! ## The round trip -/

variable (cfg : Config)

/-- The lifting convention: same observations. -/
def up : lang cfg ⟶ ssaLang cfg := ⟨id, Eq⟩

/-- The lowering convention: same observations. -/
def down : ssaLang cfg ⟶ lang cfg := ⟨id, Eq⟩

theorem up_down : up cfg ≫ down cfg = 𝟙 (lang cfg) :=
  Convention.ext rfl Relation.eq_comp

/-- Lift into SSA form: check the SSA condition. -/
def lift : Pass (up cfg) where
  run us := if h : IsSSA us = true then some ⟨us, h⟩ else none
  sound us q h := by
    refine (valid_iff_beh _ _ _).2 ⟨rfl, fun o ho => ⟨o, ?_, rfl⟩⟩
    split at h
    · cases h; exact ho
    · cases h

/-- Lower out of SSA form: forget the condition. -/
def lower : Pass (down cfg) where
  run q := some q.1
  sound q us h := by
    cases h
    exact (valid_iff_beh _ _ _).2 ⟨rfl, fun o ho => ⟨o, ho, rfl⟩⟩

/-- Mir → Mir.SSA → Mir is a round trip. -/
def roundTrip : RoundTrip (lang cfg) (ssaLang cfg) where
  lift := lift cfg
  lower := lower cfg
  le_id := le_of_eq (up_down cfg)

/-! ## End-to-end theorems -/

/-- The trivial SSA optimization. -/
def ssaNop : EndoPass (ssaLang cfg) := EndoPass.id _

/-- Optimize in SSA form, then link: a pass from Mir to closed Lir programs at the link's
convention. -/
def optimizeAndLink (E : EndoPass (ssaLang cfg)) : Pass (𝟙 (lang cfg) ≫ (linkCompiler cfg).conv) :=
  (roundTrip cfg).conj E ≫ₚ Pass.ofCompiler (linkCompiler cfg)

/-- **End-to-end validity for every SSA optimization.** Whatever the endo-pass `E` on SSA Mir
does, lifting into SSA, running `E`, lowering and linking is a valid compilation from Mir to
Lir, with the link's convention; nothing about `E` beyond its own refinement lemma is used. -/
theorem optimizeAndLink_sound (E : EndoPass (ssaLang cfg)) {us : Array Unit} {q : LirProgram}
    (h : (optimizeAndLink cfg E).run us = some q) : Valid (linkCompiler cfg).conv us q := by
  have := (optimizeAndLink cfg E).sound us q h
  rwa [Category.id_comp] at this

/-- The same as an explicit pipeline value: Mir → SSA → SSA → Mir → Lir. -/
def pipeline (E : EndoPass (ssaLang cfg)) :=
  Pipeline.cons (lift cfg) <| Pipeline.cons E.toPass <| Pipeline.cons (lower cfg) <|
    Pipeline.cons (Pass.ofCompiler (linkCompiler cfg)) (Pipeline.nil lirLang)

/-- The pipeline's end-to-end theorem, from `Pipeline.sound`; its convention normalises to
the link's. -/
theorem pipeline_sound (E : EndoPass (ssaLang cfg)) {us : Array Unit} {q : LirProgram}
    (h : (pipeline cfg E).run us = some q) : Valid (linkCompiler cfg).conv us q := by
  have := (pipeline cfg E).sound h
  have e : up cfg ≫ 𝟙 (ssaLang cfg) ≫ down cfg ≫ (linkCompiler cfg).conv ≫ 𝟙 lirLang =
      (linkCompiler cfg).conv := by
    rw [Category.comp_id, Category.id_comp, ← Category.assoc, up_down, Category.id_comp]
  rwa [e] at this

/-- The trivial instance. -/
example {us : Array Unit} {q : LirProgram} (h : (pipeline cfg (ssaNop cfg)).run us = some q) :
    Valid (linkCompiler cfg).conv us q :=
  pipeline_sound cfg _ h

end Silmaril.Compile.Mir
