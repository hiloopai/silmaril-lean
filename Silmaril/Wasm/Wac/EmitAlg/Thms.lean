module

public import Silmaril.Wasm.Wac.EmitAlg.Defs
public import Silmaril.Wasm.Wac.Emit.Thms
public import Silmaril.Wasm.Component.Algebra.Wac.Thms
public import Silmaril.Wasm.Component.Algebra.Equiv.Thms

/-!
# WAC: the entry point of `wasm-wac compose --wasm`, through the component algebra

`Emit.composeWasm_congr` reads equivalence of the composed binary off `Graph.toComp_congr`.
Here the same entry point is stated in the component algebra
(`Silmaril.Wasm.Component.Algebra`, `docs/projects/wasm-components.md`):

* `composeWasm_binTerm`: the term of the binary (`binTerm S b`) is the algebra term
  `Graph.term S (toGraph S g)` of the elaborated document `g`, and the binary's component for
  packages `P` is that term evaluated at `P` (`Algebra.eval_term`);
* `composeWasm_equiv` (**substituting equivalent packages gives an equivalent composed
  binary**): for package interfaces `S` and packages `P`, `P'` that are pairwise equivalent
  (`CompEquiv C`, the algebra's equivalence), the binary's components are equivalent. This is
  `Algebra.build_equiv`, the congruence of term evaluation. There is no hypothesis on names or
  types: the interfaces `S` are those the document was elaborated against;
* `composeWasm_refines`: the same for refinement (`build_refines`);
* `composeWasm_ctxEquiv`: the same for contextual equivalence (`CtxEquiv`), through
  `ctxEquiv_iff`: packages indistinguishable in every context give composed binaries
  indistinguishable in every context;
* `composeWasm_congr_alg`: the restatement of `composeWasm_congr` with the binary's own
  lowering `Lower.toComp` (interfaces read off the packages, so they must agree, `sigOf`), via
  `Algebra.toComp_equiv`; `composeWasm_update_equiv`: replacing one package.

`composeWasmRaw` (what the tool runs) gives the same bytes when the packages' bytes are
canonical encodings (`composeWasmRaw_correct`); its graph is the same `toGraph S g`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Emit

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Algebra
open Silmaril.Wasm.Component.Binary

variable {M : Type}

theorem binGraph_of {S : Nat → PkgSig} {b : ByteArray} {a : Ast} {G : Graph}
    (hp : parse b = .ok a) (hg : Lower.graph S a = .ok G) : binGraph S b = .ok G := by
  unfold binGraph
  rw [hp]
  exact hg

/-- The graph read off a composed binary is the elaborated document's graph. -/
theorem composeWasm_binGraph {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {pkgs : List (String × Ast)} {embed : Bool} {d : FuncAlias.Document} {b : ByteArray}
    (h : composeWasm env noms pkgs embed d = .ok b)
    (hnv : ∀ g, Bridge.elabDocXV (tablesOf noms d) env d = .ok g → Bridge.NoValue g)
    (S : Nat → PkgSig) :
    ∃ g, Bridge.elabDocXV (tablesOf noms d) env d = .ok g ∧
      binGraph S b = .ok (Bridge.toGraph S g) := by
  obtain ⟨g, c, hg, -, hp, -, hl⟩ := composeWasm_correct h
  exact ⟨g, hg, binGraph_of hp (hl (hnv g hg) S)⟩

/-- **The composed binary is a term of the algebra**: its term is the term of the
elaborated document's graph, and its component for packages `P` is that term evaluated
at `P`. -/
theorem composeWasm_binTerm {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {pkgs : List (String × Ast)} {embed : Bool} {d : FuncAlias.Document} {b : ByteArray}
    (h : composeWasm env noms pkgs embed d = .ok b)
    (hnv : ∀ g, Bridge.elabDocXV (tablesOf noms d) env d = .ok g → Bridge.NoValue g)
    (S : Nat → PkgSig) (P : Nat → Comp M) :
    ∃ g, Bridge.elabDocXV (tablesOf noms d) env d = .ok g ∧
      binTerm (M := M) S b = .ok ((Bridge.toGraph S g).term S) ∧
      binComp S P b = .ok (((Bridge.toGraph S g).term S).eval P) := by
  obtain ⟨g, hg, hb⟩ := composeWasm_binGraph h hnv S
  refine ⟨g, hg, ?_, ?_⟩
  · simp only [binTerm, hb, Except.map]
  · simp only [binComp, hb, Except.map, eval_term]

variable [CoreModule M]

/-- **Substituting equivalent packages gives an equivalent composed binary**: for the
package interfaces `S` the document was elaborated against, pairwise equivalent packages
give equivalent components of the binary `wasm-wac compose --wasm` (and `plug`) writes. -/
theorem composeWasm_equiv {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {pkgs : List (String × Ast)} {embed : Bool} {d : FuncAlias.Document} {b : ByteArray}
    (h : composeWasm env noms pkgs embed d = .ok b)
    (hnv : ∀ g, Bridge.elabDocXV (tablesOf noms d) env d = .ok g → Bridge.NoValue g)
    (S : Nat → PkgSig) {C : CoreSem M} {P P' : Nat → Comp M}
    (hP : ∀ k, CompEquiv C (P k) (P' k)) :
    ∃ X X', binComp S P b = .ok X ∧ binComp S P' b = .ok X' ∧ CompEquiv C X X' := by
  obtain ⟨g, -, hb⟩ := composeWasm_binGraph h hnv S
  refine ⟨_, _, ?_, ?_, build_equiv S hP (Bridge.toGraph S g)⟩
  · simp only [binComp, hb, Except.map]
  · simp only [binComp, hb, Except.map]

/-- **Refining packages refine the composed binary.** -/
theorem composeWasm_refines {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {pkgs : List (String × Ast)} {embed : Bool} {d : FuncAlias.Document} {b : ByteArray}
    (h : composeWasm env noms pkgs embed d = .ok b)
    (hnv : ∀ g, Bridge.elabDocXV (tablesOf noms d) env d = .ok g → Bridge.NoValue g)
    (S : Nat → PkgSig) {C : CoreSem M} {P P' : Nat → Comp M}
    (hP : ∀ k, CompRefines C (P k) (P' k)) :
    ∃ X X', binComp S P b = .ok X ∧ binComp S P' b = .ok X' ∧ CompRefines C X X' := by
  obtain ⟨g, -, hb⟩ := composeWasm_binGraph h hnv S
  refine ⟨_, _, ?_, ?_, build_refines S hP (Bridge.toGraph S g)⟩
  · simp only [binComp, hb, Except.map]
  · simp only [binComp, hb, Except.map]

/-- **Contextually equivalent packages give contextually equivalent composed binaries**:
packages that no context (a term of the algebra) tells apart give composed binaries that no
context tells apart. -/
theorem composeWasm_ctxEquiv {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {pkgs : List (String × Ast)} {embed : Bool} {d : FuncAlias.Document} {b : ByteArray}
    (h : composeWasm env noms pkgs embed d = .ok b)
    (hnv : ∀ g, Bridge.elabDocXV (tablesOf noms d) env d = .ok g → Bridge.NoValue g)
    (S : Nat → PkgSig) {C : CoreSem M} {P P' : Nat → Comp M}
    (hP : ∀ k, CtxEquiv C (P k) (P' k)) :
    ∃ X X', binComp S P b = .ok X ∧ binComp S P' b = .ok X' ∧ CtxEquiv C X X' := by
  obtain ⟨X, X', hX, hX', he⟩ := composeWasm_equiv h hnv S (fun k => ctxEquiv_iff.1 (hP k))
  exact ⟨X, X', hX, hX', ctxEquiv_iff.2 he⟩

/-- **`composeWasm_congr` through the algebra**: the components `Lower.toComp` of the
binary, for two package assignments with the same interfaces that are pairwise equivalent,
are equivalent (`Algebra.toComp_equiv`). -/
theorem composeWasm_congr_alg {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {pkgs : List (String × Ast)} {embed : Bool} {d : FuncAlias.Document} {b : ByteArray}
    (h : composeWasm env noms pkgs embed d = .ok b)
    (hnv : ∀ g, Bridge.elabDocXV (tablesOf noms d) env d = .ok g → Bridge.NoValue g)
    {C : CoreSem M} {P P' : Nat → Comp M}
    (hs : ∀ k, sigOf (P k) = sigOf (P' k)) (hP : ∀ k, CompEquiv C (P k) (P' k)) :
    ∃ a X X', parse b = .ok a ∧ Lower.toComp P a = .ok X ∧ Lower.toComp P' a = .ok X' ∧
      CompEquiv C X X' := by
  obtain ⟨g, a, hg, hp, ht⟩ := composeWasm_toComp h P
  obtain ⟨g', a', hg', hp', ht'⟩ := composeWasm_toComp h P'
  have hgg : g' = g := by rw [hg] at hg'; cases hg'; rfl
  have haa : a' = a := by rw [hp] at hp'; cases hp'; rfl
  rw [hgg, haa] at ht'
  have hS : (fun k => sigOf (P k)) = fun k => sigOf (P' k) := funext hs
  refine ⟨a, _, _, hp, ht (hnv g hg), ht' (hnv g hg), ?_⟩
  rw [← hS]
  exact toComp_equiv hs (fun k => (hP k).2) _

/-- **Replacing one package by an equivalent component with the same interface** gives an
equivalent composed binary. -/
theorem composeWasm_update_equiv {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {pkgs : List (String × Ast)} {embed : Bool} {d : FuncAlias.Document} {b : ByteArray}
    (h : composeWasm env noms pkgs embed d = .ok b)
    (hnv : ∀ g, Bridge.elabDocXV (tablesOf noms d) env d = .ok g → Bridge.NoValue g)
    {C : CoreSem M} (P : Nat → Comp M) (k : Nat) {c : Comp M}
    (hs : sigOf c = sigOf (P k)) (he : CompEquiv C (P k) c) :
    ∃ a X X', parse b = .ok a ∧ Lower.toComp P a = .ok X ∧
      Lower.toComp (Function.update P k c) a = .ok X' ∧ CompEquiv C X X' := by
  refine composeWasm_congr_alg h hnv (fun j => ?_) (fun j => ?_)
  · by_cases hj : j = k
    · rw [hj, Function.update_self, hs]
    · rw [Function.update_of_ne hj]
  · by_cases hj : j = k
    · rw [hj, Function.update_self]; exact he
    · rw [Function.update_of_ne hj]; exact CompEquiv.refl C (P j)

end Silmaril.Wasm.Wac.Emit
