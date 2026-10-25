module

public import Silmaril.Wasm.Binaryen.Merge

@[expose] public section

/-! # Checked in-order GC merge

The original `merge?` resolves import base names after retargeting namespaces.
This additive entry checks the namespace-sensitive graph assumptions used by
`merge_sound`, distinct module names, every input's profile and validity, and
output validity. It rejects memory/table/tag/segment/start support explicitly
through the existing GC profile. It does not sort modules or admit cyclic links.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics Link.GC

/-- Every import resolves by both namespace and base name in an earlier module.
The finite check supplies both `ImportsResolve` and `ImportsBackward`. -/
def importsResolveB (prog : List (String × Module)) : Bool :=
  prog.zipIdx.all fun (p, i) =>
    p.2.imports.all fun imp =>
      (prog.take i).any fun q =>
        q.1 == imp.moduleName && q.2.exports.any fun e => e.name == imp.name

theorem importsResolveB_sound {prog : List (String × Module)}
    (h : importsResolveB prog = true) : ImportsResolve prog := by
  intro i p hp imp himp
  have hentry := List.all_eq_true.mp h (p, i)
    (List.mem_zipIdx_iff_getElem?.mpr hp)
  have himp' := List.all_eq_true.mp hentry imp himp
  obtain ⟨q, hq, hmatch⟩ := List.any_eq_true.mp himp'
  obtain ⟨j, hj, heq⟩ := List.mem_take_iff_getElem.mp hq
  have hjlen : j < prog.length := lt_of_lt_of_le hj (Nat.min_le_right _ _)
  have hji : j < i := lt_of_lt_of_le hj (Nat.min_le_left _ _)
  obtain ⟨hname, hexp⟩ := Bool.and_eq_true_iff.mp hmatch
  obtain ⟨e, he, hen⟩ := List.any_eq_true.mp hexp
  exact ⟨j, hji, q, by simpa [List.getElem?_eq_getElem hjlen] using congrArg some heq,
    by simpa using hname, e, he, by simpa using hen⟩

theorem importsResolve_backward {prog : List (String × Module)}
    (h : ImportsResolve prog) : ImportsBackward prog := by
  intro i p hp imp himp
  obtain ⟨j, hj, q, hq, hn, -⟩ := h i p hp imp himp
  exact ⟨j, hj, q, hq, hn⟩

/-- A fully executable precondition for the scoped N-ary semantic theorem. -/
def mergeInputsB (prog : List (String × Module)) : Bool :=
  importsResolveB prog && decide (prog.map Prod.fst).Nodup &&
    prog.all fun p => inProfile p.2 && (validate? p.2).isSome

/-- Add checked namespace/graph conditions to the existing merge implementation.
The final validation also covers singleton input, where `merge?` is identity. -/
def checkedMerge? (prog : List (String × Module)) : Option Module := do
  if !mergeInputsB prog then none else do
    let result ← merge? (prog.map Prod.snd)
    if (validate? result).isSome then some result else none

theorem checkedMerge?_conditions {prog : List (String × Module)} {result : Module}
    (h : checkedMerge? prog = some result) :
    merge? (prog.map Prod.snd) = some result ∧
      ImportsBackward prog ∧ ImportsResolve prog ∧
      (∀ p ∈ prog, inProfile p.2 = true) ∧ InitsPure prog ∧
      (prog.map Prod.fst).Nodup ∧ ModuleValid result := by
  unfold checkedMerge? at h
  split at h
  · cases h
  · rename_i hi
    have hi' : mergeInputsB prog = true := by simpa using hi
    simp only [mergeInputsB, Bool.and_eq_true] at hi'
    obtain ⟨⟨hgraph, hnames⟩, hmodules⟩ := hi'
    have hresolve := importsResolveB_sound hgraph
    cases hm : merge? (prog.map Prod.snd) with
    | none => simp [hm] at h
    | some m =>
      simp only [Option.bind_eq_bind, hm, Option.bind_some] at h
      split at h
      · rename_i hv
        cases h
        obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp hv
        have hprof : ∀ p ∈ prog, inProfile p.2 = true := by
          intro p hp
          exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hmodules p hp)).1
        refine ⟨rfl, importsResolve_backward hresolve, hresolve, hprof, ?_,
          by simpa using hnames, ⟨mt, validate?_sound hmt⟩⟩
        intro p hp
        have hi := hprof p hp
        simp only [inProfile, Bool.and_eq_true, List.isEmpty_iff,
          Option.isNone_iff_eq_none] at hi
        exact ⟨hi.1.1.1.2, hi.1.1.2, hi.1.2⟩
      · cases h

/-- Every successful checked merge has the exact existing separate-instantiation
behaviour theorem. Grow choices remain deterministic; the host is closed. -/
theorem checkedMerge?_sound {H : Type} {prog : List (String × Module)} {result : Module}
    (h : checkedMerge? prog = some result)
    {o : SingleThreaded.GrowOracle} {n x : String} {vs : List Val}
    (hx : ∃ p ∈ prog, p.1 = n ∧ ∃ e ∈ p.2.exports, e.name = x) :
    Program.beh (SingleThreaded.profile o) (SingleThreaded.Det.noHost (H := H)) prog n x vs =
      (moduleEntryPoints (SingleThreaded.profile o) (SingleThreaded.Det.noHost (H := H))
        closedEnv).beh result x vs := by
  obtain ⟨hm, hb, hr, hp, hi, hn, -⟩ := checkedMerge?_conditions h
  exact merge_sound hm hb hr hp hi hn hx

end Silmaril.Wasm.Binaryen
