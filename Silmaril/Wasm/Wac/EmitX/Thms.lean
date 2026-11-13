module

public import Silmaril.Wasm.Wac.EmitX.Defs
public import Silmaril.Wasm.Wac.EmitAlg.Thms
public import Silmaril.Wasm.Wac.SpliceX.Thms
public import Silmaril.Wasm.Perf.CanonB.Thms

/-!
# WAC: the entry point with async packages, and equivalence read off the bytes

* `composeWasmRaw_correctX`: `composeWasmRaw_correct` for packages with the async built-ins:
  when the packages' bytes are canonical encodings of extended ASTs `tbl` (`AgreesX`), the
  binary parses (`parseX`) to `embedX tbl c`, which is in the profile, lowers to the elaborated
  graph, and whose components are the packages of `c`'s imports, looked up in `tbl`;
* `composeWasmX_correct`: the same with no hypothesis, when the tool's check succeeded
  (`composeWasmX` returned the table);
* `composeWasmX_binCompX`: the binary's component, with the packages' meanings read from the
  bytes embedded in it (`binPkgs`), is the term of the elaborated document evaluated at the
  lowerings of the packages in `tbl`;
* `composeWasmX_bytes_equiv`: **two binaries of the same document whose packages lower to
  equivalent components are equivalent**, each read entirely from its own bytes. This is
  `composeWasm_equiv` with the package meanings coming from the embedded bytes instead of a
  parameter.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Emit

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Algebra
open Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.BinaryAsync
open Silmaril.Wasm.Wac.SpliceX

/-- **Correctness of the tool's `compose --wasm` with async packages.** -/
theorem composeWasmRaw_correctX {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {raw : List (String × ByteArray)} {d : FuncAlias.Document} {b : ByteArray}
    (h : composeWasmRaw env noms raw d = .ok b) :
    ∃ g c, Bridge.elabDocXV (tablesOf noms d) env d = .ok g ∧
      Bridge.encode (nomOf noms d) g = .ok c ∧ Splice.splice (Splice.table raw) c = some b ∧
      ∀ tbl, AgreesX tbl (Splice.table raw) →
        parseX b = .ok (embedX tbl c) ∧ Profile (embedX tbl c).erase ∧
        (Bridge.NoValue g → ∀ S, Lower.graph S (embedX tbl c).erase = .ok (Bridge.toGraph S g)) ∧
        pkgsOf (embedX tbl c) = (pkgSrcs c).map (PkgSrc.resolve tbl) := by
  obtain ⟨g, c, hg, he, hs, -⟩ := composeWasmRaw_correct h
  refine ⟨g, c, hg, he, hs, fun tbl ha => ⟨parseX_splice ha hs, ?_, fun hnv S => ?_,
    pkgsOf_embedX tbl c⟩⟩
  · show isProfile (embedX tbl c).erase = true
    rw [isProfile_embedX]
    exact Bridge.encode_profile he
  · rw [graph_embedX]
    exact Bridge.lower_encode S hnv he

theorem composeWasmX_ok {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {raw : List (String × ByteArray)} {d : FuncAlias.Document} {b : ByteArray}
    {t : Option PkgTableX} (h : composeWasmX env noms raw d = .ok (b, t)) :
    composeWasmRaw env noms raw d = .ok b ∧ canonTable (Splice.table raw) = t := by
  unfold composeWasmX at h
  cases hr : composeWasmRaw env noms raw d with
  | error e => rw [hr] at h; cases h
  | ok b' =>
    rw [hr] at h
    cases h
    exact ⟨rfl, by rw [Silmaril.Wasm.Perf.EncodeB.canonTable_eq_canonTableF]⟩

/-- **Correctness of `wasm-wac compose --wasm` when its canonicity check succeeds**: no
hypothesis on the packages. -/
theorem composeWasmX_correct {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {raw : List (String × ByteArray)} {d : FuncAlias.Document} {b : ByteArray}
    {tbl : PkgTableX} (h : composeWasmX env noms raw d = .ok (b, some tbl)) :
    ∃ g c, Bridge.elabDocXV (tablesOf noms d) env d = .ok g ∧
      Bridge.encode (nomOf noms d) g = .ok c ∧ AgreesX tbl (Splice.table raw) ∧
      parseX b = .ok (embedX tbl c) ∧ Profile (embedX tbl c).erase ∧
      (Bridge.NoValue g → ∀ S, Lower.graph S (embedX tbl c).erase = .ok (Bridge.toGraph S g)) ∧
      pkgsOf (embedX tbl c) = (pkgSrcs c).map (PkgSrc.resolve tbl) := by
  obtain ⟨hr, ht⟩ := composeWasmX_ok h
  have ha := canonTable_agrees ht
  obtain ⟨g, c, hg, he, -, hall⟩ := composeWasmRaw_correctX hr
  exact ⟨g, c, hg, he, ha, hall tbl ha⟩

theorem getElem?_join_map {α β : Type} (f : α → Option β) (l : List α) (k : Nat) :
    ((l.map f)[k]?).join = (l[k]?).bind f := by
  rw [List.getElem?_map]
  cases l[k]? <;> rfl

variable {M : Type}

/-- The packages' meanings read from a binary that parses to `embedX tbl c`. -/
theorem binPkgs_embedX {rd : AstX → Option (Comp M)} {dflt : Comp M} {b : ByteArray}
    {tbl : PkgTableX} {c : Ast} (hp : parseX b = .ok (embedX tbl c)) (k : Nat) :
    binPkgs rd dflt b k = pkgMeaning rd dflt (((pkgSrcs c)[k]?).bind (PkgSrc.resolve tbl)) := by
  simp only [binPkgs, hp, pkgsOf_embedX, getElem?_join_map]

/-- **The binary's component, with the packages read from its own bytes**: the term of the
elaborated document, evaluated at the lowerings of the packages. -/
theorem composeWasmRaw_binCompX {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {raw : List (String × ByteArray)} {d : FuncAlias.Document} {b : ByteArray}
    (h : composeWasmRaw env noms raw d = .ok b)
    (hnv : ∀ g, Bridge.elabDocXV (tablesOf noms d) env d = .ok g → Bridge.NoValue g)
    {tbl : PkgTableX} (ha : AgreesX tbl (Splice.table raw)) (S : Nat → PkgSig)
    (rd : AstX → Option (Comp M)) (dflt : Comp M) :
    ∃ g c, Bridge.elabDocXV (tablesOf noms d) env d = .ok g ∧
      Bridge.encode (nomOf noms d) g = .ok c ∧
      binGraphX S b = .ok (Bridge.toGraph S g) ∧
      binTermX (M := M) S b = .ok ((Bridge.toGraph S g).term S) ∧
      binCompX S rd dflt b = .ok (((Bridge.toGraph S g).term S).eval
        fun k => pkgMeaning rd dflt (((pkgSrcs c)[k]?).bind (PkgSrc.resolve tbl))) := by
  obtain ⟨g, c, hg, he, -, hall⟩ := composeWasmRaw_correctX h
  obtain ⟨hp, -, hl, -⟩ := hall tbl ha
  have hb : binGraphX S b = .ok (Bridge.toGraph S g) := by
    simp only [binGraphX, hp]
    exact hl (hnv g hg) S
  refine ⟨g, c, hg, he, hb, ?_, ?_⟩
  · simp only [binTermX, hb, Except.map]
  · have hP : binPkgs rd dflt b = fun k =>
        pkgMeaning rd dflt (((pkgSrcs c)[k]?).bind (PkgSrc.resolve tbl)) :=
      funext (binPkgs_embedX hp)
    simp only [binCompX, hb, Except.map, hP, eval_term]

variable [CoreModule M]

theorem pkgMeaning_resolve_equiv {C : CoreSem M} {rd : AstX → Option (Comp M)} {dflt : Comp M}
    {tbl tbl' : PkgTableX}
    (hP : ∀ n, CompEquiv C (pkgMeaning rd dflt (tbl.lookup n)) (pkgMeaning rd dflt (tbl'.lookup n)))
    (o : Option PkgSrc) :
    CompEquiv C (pkgMeaning rd dflt (o.bind (PkgSrc.resolve tbl)))
      (pkgMeaning rd dflt (o.bind (PkgSrc.resolve tbl'))) := by
  cases o with
  | none => exact CompEquiv.refl C _
  | some s =>
    cases s with
    | named n => exact hP n
    | inline d => exact CompEquiv.refl C _
    | other => exact CompEquiv.refl C _

/-- **Equivalent packages give equivalent binaries, read off the bytes.** Two runs of the tool
on the same document, with package bytes `raw` and `raw'` (canonical encodings of `tbl` and
`tbl'`) whose packages lower (`rd`) to pairwise equivalent components, give binaries whose
components, each read entirely from its own bytes (`binCompX`: graph and package meanings), are
equivalent. -/
theorem composeWasmX_bytes_equiv {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {raw raw' : List (String × ByteArray)} {d : FuncAlias.Document} {b b' : ByteArray}
    (h : composeWasmRaw env noms raw d = .ok b) (h' : composeWasmRaw env noms raw' d = .ok b')
    (hnv : ∀ g, Bridge.elabDocXV (tablesOf noms d) env d = .ok g → Bridge.NoValue g)
    {tbl tbl' : PkgTableX} (ha : AgreesX tbl (Splice.table raw))
    (ha' : AgreesX tbl' (Splice.table raw')) (S : Nat → PkgSig) {C : CoreSem M}
    (rd : AstX → Option (Comp M)) (dflt : Comp M)
    (hP : ∀ n, CompEquiv C (pkgMeaning rd dflt (tbl.lookup n)) (pkgMeaning rd dflt (tbl'.lookup n))) :
    ∃ X X', binCompX S rd dflt b = .ok X ∧ binCompX S rd dflt b' = .ok X' ∧ CompEquiv C X X' := by
  obtain ⟨g, c, hg, he, -, -, hX⟩ := composeWasmRaw_binCompX h hnv ha S rd dflt
  obtain ⟨g', c', hg', he', -, -, hX'⟩ := composeWasmRaw_binCompX h' hnv ha' S rd dflt
  have hgg : g' = g := by rw [hg] at hg'; cases hg'; rfl
  subst hgg
  have hcc : c' = c := by rw [he] at he'; cases he'; rfl
  subst hcc
  refine ⟨_, _, hX, hX', ?_⟩
  rw [eval_term, eval_term]
  exact build_equiv S (fun k => pkgMeaning_resolve_equiv hP _) _

/-- The same for the tool's checked entry point `composeWasmX`: no hypothesis on the bytes. -/
theorem composeWasmX_equiv {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {raw raw' : List (String × ByteArray)} {d : FuncAlias.Document} {b b' : ByteArray}
    {tbl tbl' : PkgTableX}
    (h : composeWasmX env noms raw d = .ok (b, some tbl))
    (h' : composeWasmX env noms raw' d = .ok (b', some tbl'))
    (hnv : ∀ g, Bridge.elabDocXV (tablesOf noms d) env d = .ok g → Bridge.NoValue g)
    (S : Nat → PkgSig) {C : CoreSem M} (rd : AstX → Option (Comp M)) (dflt : Comp M)
    (hP : ∀ n, CompEquiv C (pkgMeaning rd dflt (tbl.lookup n)) (pkgMeaning rd dflt (tbl'.lookup n))) :
    ∃ X X', binCompX S rd dflt b = .ok X ∧ binCompX S rd dflt b' = .ok X' ∧ CompEquiv C X X' := by
  obtain ⟨hr, ht⟩ := composeWasmX_ok h
  obtain ⟨hr', ht'⟩ := composeWasmX_ok h'
  exact composeWasmX_bytes_equiv hr hr' hnv (canonTable_agrees ht) (canonTable_agrees ht') S rd
    dflt hP

end Silmaril.Wasm.Wac.Emit
