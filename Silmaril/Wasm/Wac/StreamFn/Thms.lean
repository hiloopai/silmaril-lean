module

public import Silmaril.Wasm.Wac.StreamFn.Defs
public import Silmaril.Wasm.Wac.EndToEnd.Thms

/-!
# WAC: stream packages read as functions, substitution from the text and the bytes

* `fnComp_equiv`: two codes with the same whole output give equivalent function components
  (same export name), in `callSem`;
* `readFn_lowerFn`: a stream package is read by `lowerFn κ` whatever `other` is;
* **`composeText_fn_equiv`**: the same WAC text with two sets of package bytes, whose packages
  decode to the same types and agree up to the whole outputs of the stream packages' codes
  (`RunAgreeF`, export names kept), gives two binaries whose components, each read entirely off
  its own bytes by `readFn κ other`, are equivalent in `callSem`. Unlike
  `EndToEnd.composeText_stream_equiv`, the packages keep the shape and the export name they
  have in the bytes, so a driver's argument `sI["tI"]` reads the stream function `tI`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.StreamFn

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Algebra
open Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.BinaryAsync
open Silmaril.Wasm.Component.Streams.Alg Silmaril.Wasm.Wac.StreamPkg
open Silmaril.Wasm.Wac.SpliceX Silmaril.Wasm.Wac.Emit Silmaril.Wasm.Wac.EndToEnd

theorem callSem_sem {n : String} {k k' : TCode} (h : k.run = k'.run) :
    callSem.sem (⟨n, k⟩ : FCode) = callSem.sem (⟨n, k'⟩ : FCode) := by
  simp only [callSem, h]
  rfl

/-- **Codes with the same whole output give equivalent function components.** -/
theorem fnComp_equiv {n : String} {k k' : TCode} (h : k.run = k'.run) :
    CompEquiv callSem (fnComp n k) (fnComp n k') := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  simp only [fnComp, Comp.denU, denNodes, Node.den, coreNode, callSem_sem h]
  rfl

theorem lowerFn_eq {κ : Interp} {a : AstX} {s : XfShape} {k : TCode}
    (hs : fnShape a = some s) (hk : κ s.core = some k) : lowerFn κ a = some (fnComp s.name k) := by
  simp only [lowerFn, hs, hk, Option.bind_some, Option.map_some]

/-- A stream package is read by `lowerFn κ`, whatever the reading of the others. -/
theorem readFn_lowerFn {κ : Interp} {other : AstX → Option (Comp FCode)} {a : AstX}
    {s : XfShape} {k : TCode} (hs : fnShape a = some s) (hk : κ s.core = some k) :
    readFn κ other a = some (fnComp s.name k) := by
  simp only [readFn, lowerFn_eq hs hk]

theorem runAgreeF_equiv {κ : Interp} {other : AstX → Option (Comp FCode)} {dflt : Comp FCode}
    {tbl tbl' : PkgTableX} (h : RunAgreeF κ tbl tbl') (n : String) :
    CompEquiv callSem (pkgMeaning (readFn κ other) dflt (tbl.lookup n))
      (pkgMeaning (readFn κ other) dflt (tbl'.lookup n)) := by
  rcases h n with he | ⟨a, a', s, s', k, k', ha, ha', hs, hk, hs', hk', hn, hrun⟩
  · rw [he]; exact CompEquiv.refl _ _
  · simp only [ha, ha', pkgMeaning, Option.bind_some, readFn_lowerFn hs hk, readFn_lowerFn hs' hk',
      Option.getD_some, hn]
    exact fnComp_equiv hrun

/-- **What `binShapes` reports is what the reading reads**: a package that `binShapes b` lists
as the stream package `s`, whose core module implements `k`, is read from `b` as the function
`fnComp s.name k`. -/
theorem binPkgs_of_binShapes {κ : Interp} {other : AstX → Option (Comp FCode)} {dflt : Comp FCode}
    {b : ByteArray} {l : List (Option XfShape)} {i : Nat} {s : XfShape} {k : TCode}
    (hb : binShapes b = .ok l) (hi : l[i]? = some (some s)) (hk : κ s.core = some k) :
    binPkgs (readFn κ other) dflt b i = fnComp s.name k := by
  unfold binShapes at hb
  unfold binPkgs
  cases hp : parseX b with
  | error e => simp [hp] at hb
  | ok a =>
    simp only [hp, Except.ok.injEq] at hb
    subst hb
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hi
    obtain ⟨o, ho, hs⟩ := hi
    obtain ⟨x, rfl, hx⟩ := Option.bind_eq_some_iff.1 hs
    simp only [ho, Option.join_some, pkgMeaning, Option.bind_some, readFn_lowerFn hx hk,
      Option.getD_some]

/-- **Stream packages with the same whole output, read as the functions they export, give
equivalent compositions, from the WAC text and the bytes.** -/
theorem composeText_fn_equiv {src : String} {raw raw' : List (String × ByteArray)}
    {b b' : ByteArray} {tbl tbl' : PkgTableX}
    (h : composeText src raw = .ok (b, some tbl, true))
    (h' : composeText src raw' = .ok (b', some tbl', true))
    (hT : ∀ k, (raw.lookup k).map TypeOf.decodeAnyX = (raw'.lookup k).map TypeOf.decodeAnyX)
    (S : Nat → PkgSig) (κ : Interp) (other : AstX → Option (Comp FCode)) (dflt : Comp FCode)
    (hr : RunAgreeF κ tbl tbl') :
    ∃ X X', binCompX S (readFn κ other) dflt b = .ok X ∧
      binCompX S (readFn κ other) dflt b' = .ok X' ∧ CompEquiv callSem X X' :=
  composeText_equiv h h' hT S (readFn κ other) dflt (runAgreeF_equiv hr)

end Silmaril.Wasm.Wac.StreamFn
