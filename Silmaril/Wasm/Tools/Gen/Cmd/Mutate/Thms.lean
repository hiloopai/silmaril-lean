module

public import Silmaril.Wasm.Tools.Gen.Cmd.Mutate.Defs
public import Silmaril.Wasm.Tools.Gen.Core.Thms

/-!
# `wasm-tools mutate`: specification

* `mutate_validIn`: **every output of `mutate` is valid in the model `S`** (whatever the input);
* `mutateExtend_extends`, `mutate_preserve_extends`: with `--preserve-semantics`, the output is
  `extend m d` for some `Delta` `d`: the input with function types, functions and globals
  appended;
* `extend_*`: what an extension keeps: every existing type, function and global at its index,
  and the imports, memories, tables, tags, data and element segments, start function and
  exports unchanged. So every index of `m` keeps its meaning and no new definition is exported
  or started. That the output of `--preserve-semantics` is export-equivalent to its input is
  `Silmaril.Wasm.Tools.Gen.Cmd.Equiv.Thms.mutate_preserve_equiv`.
* `mutator S cfg o`: `mutate` as a partial mutator (`PMutator`) of the API
  (`Silmaril.Wasm.Tools.Gen.API`) for the language `Core.featLang S`; `preserving S cfg`: the
  `--preserve-semantics` mutations as a `PMutator.Preserving` for the class of extensions.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Mutate

open Silmaril.Wasm Silmaril.Wasm.Models Smith

theorem find_validIn {S : FeatureSet} {l : List Module} {m' : Module}
    (h : l.find? (Core.featCheck S) = some m') : ValidIn S m' :=
  (Core.featCheck_iff S _).mp (List.find?_some h)

/-- **Every output of `mutate` is valid in the model.** -/
theorem mutate_validIn {S : FeatureSet} {cfg : Config} {o : Opts} {seed : UInt64}
    {m m' : Module} (h : mutate S cfg o seed m = some m') : ValidIn S m' := by
  unfold mutate mutateExtend at h
  split at h
  · split at h
    · cases h
    · split at h
      · exact find_validIn h
      · cases h
  · exact find_validIn h

/-- Every output of the extending mutation is valid in the model. -/
theorem mutateExtend_validIn {S : FeatureSet} {cfg : Config} {seed : UInt64} {m m' : Module}
    (h : mutateExtend S cfg seed m = some m') : ValidIn S m' := by
  unfold mutateExtend at h
  split at h
  · exact find_validIn h
  · cases h

/-- **The semantics-preserving mutation appends one function**, and only to a module whose
function types take numeric parameters. -/
theorem mutateExtend_appends {S : FeatureSet} {cfg : Config} {seed : UInt64} {m m' : Module}
    (h : mutateExtend S cfg seed m = some m') :
    numParamsB m = true ∧ ∃ f, m' = appendFunc m f := by
  unfold mutateExtend at h
  split at h
  · rename_i hn
    obtain ⟨f, -, hf⟩ := List.mem_map.mp (List.mem_of_find?_eq_some h)
    exact ⟨hn, f, hf.symm⟩
  · cases h

theorem appendFunc_eq_extend (m : Module) (f : Func) : appendFunc m f = extend m { funcs := [f] } := by
  simp [appendFunc, extend]

/-- **The extending mutation appends.** -/
theorem mutateExtend_extends {S : FeatureSet} {cfg : Config} {seed : UInt64} {m m' : Module}
    (h : mutateExtend S cfg seed m = some m') : ∃ d, m' = extend m d := by
  obtain ⟨-, f, rfl⟩ := mutateExtend_appends h
  exact ⟨_, appendFunc_eq_extend m f⟩

/-- With `--preserve-semantics`, `mutate` is `mutateExtend`. -/
theorem mutate_preserve_eq {S : FeatureSet} {cfg : Config} {o : Opts} {seed : UInt64}
    {m m' : Module} (ho : o.preserveSemantics = true) (h : mutate S cfg o seed m = some m') :
    mutateExtend S cfg seed m = some m' := by
  unfold mutate at h
  simp only [ho, ↓reduceIte] at h
  split at h
  · cases h
  · exact h

/-- With `--preserve-semantics`, `mutate` appends. -/
theorem mutate_preserve_extends {S : FeatureSet} {cfg : Config} {o : Opts} {seed : UInt64}
    {m m' : Module} (ho : o.preserveSemantics = true) (h : mutate S cfg o seed m = some m') :
    ∃ d, m' = extend m d :=
  mutateExtend_extends (mutate_preserve_eq ho h)

/-! ## What an extension keeps -/

section Extend

variable (m : Module) (d : Delta)

theorem extend_types_get {i : Nat} (hi : i < m.types.length) :
    (extend m d).types[i]? = m.types[i]? := by
  simp [extend, List.getElem?_append_left hi]

theorem extend_funcs_get {i : Nat} (hi : i < m.funcs.length) :
    (extend m d).funcs[i]? = m.funcs[i]? := by
  simp [extend, List.getElem?_append_left hi]

theorem extend_globals_get {i : Nat} (hi : i < m.globals.length) :
    (extend m d).globals[i]? = m.globals[i]? := by
  simp [extend, List.getElem?_append_left hi]

theorem extend_keeps :
    (extend m d).imports = m.imports ∧ (extend m d).memories = m.memories ∧
    (extend m d).tables = m.tables ∧ (extend m d).tags = m.tags ∧
    (extend m d).data.length = m.data.length ∧ (extend m d).elems.length = m.elems.length ∧
    (extend m d).start = m.start ∧ (extend m d).exports = m.exports :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem extend_empty : extend m {} = m := by
  simp [extend]

end Extend

/-- `mutate` as a mutator of the interface. -/
def mutator (S : FeatureSet) (cfg : Config) (o : Opts) : PMutator (Core.featLang S).toLang :=
  ⟨mutate S cfg o, fun _ _ _ _ h => mutate_validIn h⟩

/-- **The `--preserve-semantics` mutations** as a partial mutator in the class of extensions
(`m'` is `m` with types, functions and globals appended). -/
def preserving (S : FeatureSet) (cfg : Config) :
    PMutator.Preserving (Core.featLang S).toLang (fun m m' => ∃ d, m' = extend m d) where
  mutate := mutateExtend S cfg
  valid _ _ _ _ h := mutateExtend_validIn h
  preserves _ _ _ h := mutateExtend_extends h

end Silmaril.Wasm.Tools.Gen.Cmd.Mutate
