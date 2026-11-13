module

public import Silmaril.Wasm.Wac.StreamPkg.Defs
public import Silmaril.Wasm.Wac.EmitX.Thms
public import Silmaril.Wasm.Component.Streams.Alg.Thms
public import Silmaril.Wasm.Component.Algebra.Pipe.Thms

/-!
# WAC: stream packages read from the bytes, substitution and plugging

With the packages' meanings read from the bytes embedded in a composed binary by the lowering
`lowerXf κ` (`Emit.binPkgs`), in the batch semantics of the streams track (`Streams.Alg.batchSem`):

* `lowerXf_equiv`: two stream packages whose core modules implement codes with the same whole
  output (`TCode.run`) lower to equivalent components (`Streams.Alg.stage_equiv`);
* `composeWasmX_stream_equiv`: **substituting stream packages whose codes have the same whole
  output, in any WAC document, gives equivalent composed binaries**, each read from its own
  bytes (`Emit.composeWasmX_bytes_equiv`); `composeWasmX_map_fusion`: the instance where a
  package doing `map f` then `map g` is replaced by one doing `map (g ∘ f)`;
* `plugX_fusion`: when the graph read from a binary is that of `wac plug` of two packages
  (`Algebra.plugGraph`, a hypothesis: the elaboration of `Emit.plugDoc` is not computed here),
  and its packages lower to stages `a` and `b`, the socket's exports are the fused stage
  `stage (.comp a b)` (`plug_equiv_seq_of_names`, `stage_fusion`);
* `plugX_realizes`: the same graph hypothesis with any compositional stream semantics `Ssem`
  (`Algebra.StreamSem`, of which none is constructed): if the lowered packages realise
  transformers `T` and `U`, the binary realises `T.comp U` (`Algebra.plug_realizes`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.StreamPkg

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Algebra
open Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.BinaryAsync
open Silmaril.Wasm.Component.Streams Silmaril.Wasm.Component.Streams.Alg
open Silmaril.Wasm.Wac.SpliceX Silmaril.Wasm.Wac.Emit

theorem lowerXf_some {κ : Interp} {a : AstX} {c : Comp TCode} (h : lowerXf κ a = some c) :
    ∃ s k, xfShape a = some s ∧ κ s.core = some k ∧ c = stage k := by
  simp only [lowerXf, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨s, hs, k, hk, rfl⟩ := h
  exact ⟨s, k, hs, hk, rfl⟩

/-- The meaning of a stream package read through `lowerXf` (`dflt` when not lowered). -/
theorem pkgMeaning_lowerXf {κ : Interp} {a : AstX} {s : XfShape} {k : TCode}
    (hs : xfShape a = some s) (hk : κ s.core = some k) :
    pkgMeaning (lowerXf κ) dflt (some a) = stage k := by
  simp only [pkgMeaning, Option.bind_some, lowerXf, hs, hk, Option.map_some, Option.getD_some]

/-- **Stream packages whose codes have the same whole output lower to equivalent
components.** -/
theorem lowerXf_equiv {κ : Interp} {a a' : AstX} {s s' : XfShape} {k k' : TCode}
    (hs : xfShape a = some s) (hk : κ s.core = some k) (hs' : xfShape a' = some s')
    (hk' : κ s'.core = some k') (hrun : k.run = k'.run) :
    CompEquiv batchSem (pkgMeaning (lowerXf κ) dflt (some a))
      (pkgMeaning (lowerXf κ) dflt (some a')) := by
  rw [pkgMeaning_lowerXf hs hk, pkgMeaning_lowerXf hs' hk']
  exact stage_equiv hrun

/-- Two tables of stream packages agree up to the codes' whole outputs: the same names, and
each pair of packages either lowers to stages of codes with the same whole output or is the
same AST. -/
def RunAgree (κ : Interp) (tbl tbl' : PkgTableX) : Prop :=
  ∀ n, (tbl.lookup n = tbl'.lookup n) ∨
    ∃ a a' s s' k k', tbl.lookup n = some a ∧ tbl'.lookup n = some a' ∧ xfShape a = some s ∧
      κ s.core = some k ∧ xfShape a' = some s' ∧ κ s'.core = some k' ∧ k.run = k'.run

theorem runAgree_equiv {κ : Interp} {tbl tbl' : PkgTableX} (h : RunAgree κ tbl tbl') (n : String) :
    CompEquiv batchSem (pkgMeaning (lowerXf κ) dflt (tbl.lookup n))
      (pkgMeaning (lowerXf κ) dflt (tbl'.lookup n)) := by
  rcases h n with he | ⟨a, a', s, s', k, k', ha, ha', hs, hk, hs', hk', hrun⟩
  · rw [he]; exact CompEquiv.refl _ _
  · rw [ha, ha']; exact lowerXf_equiv hs hk hs' hk' hrun

/-- **Substituting stream packages with the same whole output gives equivalent composed
binaries**, every package's meaning read from the bytes embedded in each binary. -/
theorem composeWasmX_stream_equiv {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {raw raw' : List (String × ByteArray)} {d : FuncAlias.Document} {b b' : ByteArray}
    {tbl tbl' : PkgTableX}
    (h : composeWasmX env noms raw d = .ok (b, some tbl))
    (h' : composeWasmX env noms raw' d = .ok (b', some tbl'))
    (hnv : ∀ g, Bridge.elabDocXV (tablesOf noms d) env d = .ok g → Bridge.NoValue g)
    (S : Nat → PkgSig) (κ : Interp) (hr : RunAgree κ tbl tbl') :
    ∃ X X', binCompX S (lowerXf κ) dflt b = .ok X ∧ binCompX S (lowerXf κ) dflt b' = .ok X' ∧
      CompEquiv batchSem X X' :=
  composeWasmX_equiv h h' hnv S (lowerXf κ) dflt (runAgree_equiv hr)

/-- **Map fusion through WAC**: replacing, in any document, a stream package whose core module
implements `map f` then `map g` by one implementing `map (g ∘ f)` gives an equivalent composed
binary. -/
theorem composeWasmX_map_fusion {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {raw raw' : List (String × ByteArray)} {d : FuncAlias.Document} {b b' : ByteArray}
    {tbl tbl' : PkgTableX}
    (h : composeWasmX env noms raw d = .ok (b, some tbl))
    (h' : composeWasmX env noms raw' d = .ok (b', some tbl'))
    (hnv : ∀ g, Bridge.elabDocXV (tablesOf noms d) env d = .ok g → Bridge.NoValue g)
    (S : Nat → PkgSig) (κ : Interp) (n : String) {a a' : AstX} {s s' : XfShape}
    {f g : Val → Val} (ha : tbl.lookup n = some a) (ha' : tbl'.lookup n = some a')
    (hs : xfShape a = some s) (hk : κ s.core = some (.comp (.map f) (.map g)))
    (hs' : xfShape a' = some s') (hk' : κ s'.core = some (.map (g ∘ f)))
    (hother : ∀ m, m ≠ n → tbl.lookup m = tbl'.lookup m) :
    ∃ X X', binCompX S (lowerXf κ) dflt b = .ok X ∧ binCompX S (lowerXf κ) dflt b' = .ok X' ∧
      CompEquiv batchSem X X' := by
  refine composeWasmX_stream_equiv h h' hnv S κ fun m => ?_
  by_cases hm : m = n
  · subst hm
    refine .inr ⟨a, a', s, s', _, _, ha, ha', hs, hk, hs', hk', ?_⟩
    funext xs
    show (Tr.map g).run ((Tr.map f).run xs) = (Tr.map (g ∘ f)).run xs
    rw [Tr.run_map, Tr.run_map, Tr.run_map, List.map_map]
  · exact .inl (hother m hm)

/-! ## Plugging -/

/-- The interfaces of the packages read from a binary. -/
def binSigs (κ : Interp) (b : ByteArray) : Nat → PkgSig :=
  fun k => sigOf (binPkgs (lowerXf κ) dflt b k)

theorem binCompX_plug {κ : Interp} {b : ByteArray}
    (hG : binGraphX (binSigs κ b) b = .ok (plugGraph (binSigs κ b))) :
    binCompX (binSigs κ b) (lowerXf κ) dflt b =
      .ok ((plugGraph (binSigs κ b)).toComp (binPkgs (lowerXf κ) dflt b)) := by
  simp only [binCompX, hG, Except.map, Graph.toComp]
  rfl

/-- **`wac plug` of two stream packages, read off the binary, is the fused stage**: if the
graph read from `b` is `plugGraph` and its packages lower to the stages of `a` (the plug) and
`c` (the socket), the socket's export is `stage (.comp a c)`. -/
theorem plugX_fusion {κ : Interp} {b : ByteArray} {a c : TCode}
    (hG : binGraphX (binSigs κ b) b = .ok (plugGraph (binSigs κ b)))
    (h0 : binPkgs (lowerXf κ) dflt b 0 = stage a) (h1 : binPkgs (lowerXf κ) dflt b 1 = stage c) :
    ∃ X, binCompX (binSigs κ b) (lowerXf κ) dflt b = .ok X ∧
      CompEquiv batchSem (select (List.range 1) X) (stage (.comp a c)) := by
  refine ⟨_, binCompX_plug hG, ?_⟩
  have e := plug_equiv_seq_of_names batchSem (binPkgs (lowerXf κ) dflt b)
    (by rw [h0, h1]; rfl) (by rw [h0]; simp [stage, names])
    (by rw [h0]; simp [stage, names, exportIface]) (by rw [h1]; simp [stage, names, exportIface])
  rw [h0, h1] at e
  have hl : (stage c).exports.length = 1 := rfl
  rw [hl] at e
  exact e.trans (stage_fusion a c)

/-- **`wac plug` of two stream packages realises the composite transformer**, for any
compositional stream semantics (a hypothesis; none is constructed), with the plug graph read
off the binary. -/
theorem plugX_realizes {κ : Interp} {b : ByteArray} {C : CoreSem TCode} (Ssem : StreamSem C)
    {σ τ α β γ : Type} {T : Tr σ α β} {U : Tr τ β γ}
    (hG : binGraphX (binSigs κ b) b = .ok (plugGraph (binSigs κ b)))
    (h0 : Realizes Ssem (binPkgs (lowerXf κ) dflt b 0) T)
    (h1 : Realizes Ssem (binPkgs (lowerXf κ) dflt b 1) U)
    (hnames : names (binPkgs (lowerXf κ) dflt b 1).imports =
      names (exportIface (binPkgs (lowerXf κ) dflt b 0)))
    (hn₀ : (names (binPkgs (lowerXf κ) dflt b 0).imports).Nodup)
    (hne : (names (exportIface (binPkgs (lowerXf κ) dflt b 0))).Nodup)
    (hn₁ : (names (exportIface (binPkgs (lowerXf κ) dflt b 1))).Nodup) :
    ∃ X, binCompX (binSigs κ b) (lowerXf κ) dflt b = .ok X ∧
      Realizes Ssem (select (List.range (binPkgs (lowerXf κ) dflt b 1).exports.length) X)
        (T.comp U) :=
  ⟨_, binCompX_plug hG, plug_realizes Ssem _ h0 h1 hnames hn₀ hne hn₁⟩

end Silmaril.Wasm.Wac.StreamPkg
