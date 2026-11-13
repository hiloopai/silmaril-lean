module

public import Silmaril.Wasm.Wac.EndToEnd.Defs
public import Silmaril.Wasm.Wac.EmitX.Thms
public import Silmaril.Wasm.Wac.StreamPkg.Thms
public import Silmaril.Wasm.Wac.Text.Thms

/-!
# `wasm-wac compose --wasm` from WAC text and package bytes: the theorems

The tool runs `EndToEnd.composeText src raw` on the WAC text `src` and the bytes `raw` of the
packages it found, and writes the bytes `b` it returns.

* `readDocX_ok`, `readDocX_print`: the text is read by the verified lexer and parser
  (`Text.parse`); the text the printer writes for a well-formed document is read back as that
  document (`Text.parse_print`);
* `readPkgs_spec`: each package's type and nominal table are those decoded from its own bytes;
* **`composeText_correct`**: when the tool's two checks succeed (canonical package bytes, no
  value nodes), the document elaborates and validates to a graph `g`, the bytes `b` parse back
  (with the async built-ins) to the composition with the packages embedded, it lowers to
  `Bridge.toGraph S g`, and **the component read entirely off `b`** (graph and packages'
  meanings, `binCompX`) **is the algebra term of the document, evaluated at the packages'
  meanings read from their own bytes**;
* **`composeText_equiv`**: the same WAC text with two sets of package bytes, whose packages have
  the same types (as decoded from the bytes) and lower to pairwise equivalent components, gives
  two output binaries that are equivalent, each read from its own bytes: *composing equivalent
  components gives equivalent compositions*, from the text and the bytes;
* **`composeText_stream_equiv`**: the same for stream packages (async built-ins included, read
  from the bytes by `lowerXf κ`) whose codes have the same whole output (`RunAgree`), in the
  batch semantics of streams.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.EndToEnd

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Algebra Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.BinaryAsync Silmaril.Wasm.Wac.Emit Silmaril.Wasm.Wac.SpliceX
open Silmaril.Wasm.Wac.StreamPkg Silmaril.Wasm.Component.Streams.Alg

/-! ## Reading the text -/

theorem readDocX_ok {src : String} {d : FuncAlias.Document} (h : Bridge.readDocX src = .ok d) :
    ∃ td, Text.parse src = some td ∧ Bridge.ofDocX td = .ok d := by
  unfold Bridge.readDocX Tool.parseDoc at h
  cases hl : Text.lex src.toList with
  | none => simp only [hl] at h; exact nomatch h
  | some ts =>
    cases hp : Text.Parse.document ts with
    | none => simp only [hl, hp] at h; exact nomatch h
    | some td =>
      simp only [hl, hp] at h
      exact ⟨td, by simp [Text.parse, hl, hp], h⟩

/-- The text the printer writes for a well-formed document is read back as that document. -/
theorem readDocX_print (td : Text.Document) (h : Text.wf td = true) :
    Bridge.readDocX (Text.print td) = Bridge.ofDocX td := by
  have hp := Text.parse_print td h
  unfold Bridge.readDocX Tool.parseDoc
  unfold Text.parse at hp
  cases hl : Text.lex (Text.print td).toList with
  | none => rw [hl] at hp; cases hp
  | some ts =>
    rw [hl, Option.bind_some] at hp
    simp only [hp]
    rfl

/-! ## Reading the packages -/

/-- **Each package's type and nominal table are decoded from its own bytes.** -/
theorem readPkgs_spec {raw : List (String × ByteArray)} :
    ∀ {ks : List String} {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
      {rs : List (String × ByteArray)}, readPkgs raw ks = .ok (env, noms, rs) →
      env.map Prod.fst = ks ∧ rs.map Prod.fst = ks ∧
      ∀ k ∈ ks, ∃ bytes p n, raw.lookup k = some bytes ∧ TypeOf.decodeAnyX bytes = .ok (p, n) ∧
        env.lookup k = some p ∧ noms.lookup k = some n ∧ rs.lookup k = some bytes
  | [], env, noms, rs, h => by
    simp only [readPkgs, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨rfl, rfl, fun k hk => absurd hk List.not_mem_nil⟩
  | k :: ks, env, noms, rs, h => by
    unfold readPkgs at h
    cases hb : raw.lookup k with
    | none => simp [hb] at h
    | some bytes =>
      cases hd : TypeOf.decodeAnyX bytes with
      | error e => simp [hb, hd] at h
      | ok pn =>
        obtain ⟨p, n⟩ := pn
        cases hr : readPkgs raw ks with
        | error e => simp [hb, hd, hr] at h
        | ok r =>
          obtain ⟨env', noms', rs'⟩ := r
          simp only [hb, hd, hr, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨h₁, h₂, h₃⟩ := readPkgs_spec hr
          refine ⟨by simp [h₁], by simp [h₂], fun k' hk' => ?_⟩
          by_cases he : k' = k
          · subst he
            exact ⟨bytes, p, n, hb, hd, by simp [List.lookup], by simp [List.lookup],
              by simp [List.lookup]⟩
          · have hk'' : k' ∈ ks := by simpa [he] using hk'
            obtain ⟨b', p', n', e₁, e₂, e₃, e₄, e₅⟩ := h₃ k' hk''
            have hne : (k' == k) = false := beq_false_of_ne he
            exact ⟨b', p', n', e₁, e₂, by simp [List.lookup, hne, e₃],
              by simp [List.lookup, hne, e₄], by simp [List.lookup, hne, e₅]⟩

/-- Package bytes with the same decoded types give the same environment. -/
theorem readPkgs_congr {raw raw' : List (String × ByteArray)} :
    ∀ {ks : List String} {env env' : PkgEnv} {noms noms' : List (String × Bridge.NomTable)}
      {rs rs' : List (String × ByteArray)},
      (∀ k ∈ ks, (raw.lookup k).map TypeOf.decodeAnyX = (raw'.lookup k).map TypeOf.decodeAnyX) →
      readPkgs raw ks = .ok (env, noms, rs) → readPkgs raw' ks = .ok (env', noms', rs') →
      env = env' ∧ noms = noms'
  | [], _, _, _, _, _, _, _, h, h' => by
    simp only [readPkgs, Except.ok.injEq, Prod.mk.injEq] at h h'
    obtain ⟨rfl, rfl, -⟩ := h
    obtain ⟨rfl, rfl, -⟩ := h'
    exact ⟨rfl, rfl⟩
  | k :: ks, env, env', noms, noms', rs, rs', hT, h, h' => by
    obtain ⟨-, -, hs⟩ := readPkgs_spec h
    obtain ⟨-, -, hs'⟩ := readPkgs_spec h'
    have hT' : ∀ k ∈ ks, (raw.lookup k).map TypeOf.decodeAnyX =
        (raw'.lookup k).map TypeOf.decodeAnyX := fun k hk => hT k (List.mem_cons_of_mem _ hk)
    unfold readPkgs at h h'
    cases hb : raw.lookup k with
    | none => simp [hb] at h
    | some bytes =>
    cases hb' : raw'.lookup k with
    | none => simp [hb'] at h'
    | some bytes' =>
    have hk := hT k List.mem_cons_self
    rw [hb, hb', Option.map_some, Option.map_some, Option.some.injEq] at hk
    cases hd : TypeOf.decodeAnyX bytes with
    | error e => simp [hb, hd] at h
    | ok pn =>
    have hd' : TypeOf.decodeAnyX bytes' = .ok pn := hk ▸ hd
    cases hr : readPkgs raw ks with
    | error e => simp [hb, hd, hr] at h
    | ok r =>
    cases hr' : readPkgs raw' ks with
    | error e => simp [hb', hd', hr'] at h'
    | ok r' =>
    obtain ⟨e₁, n₁, s₁⟩ := r
    obtain ⟨e₂, n₂, s₂⟩ := r'
    simp only [hb, hd, hr, Except.ok.injEq, Prod.mk.injEq] at h
    simp only [hb', hd', hr', Except.ok.injEq, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, -⟩ := h
    obtain ⟨rfl, rfl, -⟩ := h'
    obtain ⟨rfl, rfl⟩ := readPkgs_congr hT' hr hr'
    exact ⟨rfl, rfl⟩

/-! ## The value check -/

theorem noValues_true {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {d : FuncAlias.Document} (h : noValues env noms d = true) :
    ∀ g, Bridge.elabDocXV (tablesOf noms d) env d = .ok g → Bridge.NoValue g := by
  intro g hg nd hnd
  simp only [noValues, hg, List.all_eq_true, bne_iff_ne, ne_eq] at h
  exact h nd hnd

/-! ## The pipeline -/

theorem composeText_ok {src : String} {raw : List (String × ByteArray)} {b : ByteArray}
    {t : Option PkgTableX} {nv : Bool} (h : composeText src raw = .ok (b, t, nv)) :
    ∃ d env noms rs, Bridge.readDocX src = .ok d ∧
      readPkgs raw (Bridge.pkgKeysX d) = .ok (env, noms, rs) ∧
      composeWasmX env noms rs d = .ok (b, t) ∧ noValues env noms d = nv := by
  cases hd : Bridge.readDocX src with
  | error e => simp [composeText, hd] at h
  | ok d =>
    cases hr : readPkgs raw (Bridge.pkgKeysX d) with
    | error e => simp [composeText, hd, hr] at h
    | ok r =>
      obtain ⟨env, noms, rs⟩ := r
      cases hc : composeWasmX env noms rs d with
      | error e => simp [composeText, hd, hr, hc] at h
      | ok bt =>
        obtain ⟨b', t'⟩ := bt
        simp only [composeText, hd, hr, hc, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨d, env, noms, rs, rfl, hr, hc, rfl⟩

/-- **Correctness of `wasm-wac compose --wasm`, from the WAC text and the package bytes.** -/
theorem composeText_correct {src : String} {raw : List (String × ByteArray)} {b : ByteArray}
    {tbl : PkgTableX} (h : composeText src raw = .ok (b, some tbl, true)) :
    ∃ td d env noms rs g c,
      Text.parse src = some td ∧ Bridge.ofDocX td = .ok d ∧
      readPkgs raw (Bridge.pkgKeysX d) = .ok (env, noms, rs) ∧
      Bridge.elabDocXV (tablesOf noms d) env d = .ok g ∧ Bridge.NoValue g ∧
      Bridge.encode (nomOf noms d) g = .ok c ∧ AgreesX tbl (Splice.table rs) ∧
      parseX b = .ok (embedX tbl c) ∧ Profile (embedX tbl c).erase ∧
      (∀ S, Lower.graph S (embedX tbl c).erase = .ok (Bridge.toGraph S g)) ∧
      pkgsOf (embedX tbl c) = (pkgSrcs c).map (PkgSrc.resolve tbl) ∧
      ∀ {M : Type} (S : Nat → PkgSig) (rd : AstX → Option (Comp M)) (dflt : Comp M),
        binCompX S rd dflt b = .ok (((Bridge.toGraph S g).term S).eval
          fun k => pkgMeaning rd dflt (((pkgSrcs c)[k]?).bind (PkgSrc.resolve tbl))) := by
  obtain ⟨d, env, noms, rs, hd, hr, hc, hn⟩ := composeText_ok h
  obtain ⟨td, hp, ho⟩ := readDocX_ok hd
  have hnv := noValues_true hn
  obtain ⟨hraw, -⟩ := composeWasmX_ok hc
  obtain ⟨g, c, hg, he, ha, hpx, hpr, hl, hpk⟩ := composeWasmX_correct hc
  refine ⟨td, d, env, noms, rs, g, c, hp, ho, hr, hg, hnv g hg, he, ha, hpx, hpr,
    fun S => hl (hnv g hg) S, hpk, fun S rd dflt => ?_⟩
  obtain ⟨g', c', hg', he', -, -, hX⟩ := composeWasmRaw_binCompX hraw hnv ha S rd dflt
  rw [hg] at hg'
  cases hg'
  rw [he] at he'
  cases he'
  exact hX

/-- **Composing equivalent components gives equivalent compositions, from the text and the
bytes.** The same WAC text, with two sets of package bytes whose packages decode to the same
types and lower (`rd`) to pairwise equivalent components, gives two binaries whose components,
each read entirely off its own bytes, are equivalent. -/
theorem composeText_equiv {M : Type} [CoreModule M] {src : String}
    {raw raw' : List (String × ByteArray)} {b b' : ByteArray} {tbl tbl' : PkgTableX}
    (h : composeText src raw = .ok (b, some tbl, true))
    (h' : composeText src raw' = .ok (b', some tbl', true))
    (hT : ∀ k, (raw.lookup k).map TypeOf.decodeAnyX = (raw'.lookup k).map TypeOf.decodeAnyX)
    (S : Nat → PkgSig) {C : CoreSem M} (rd : AstX → Option (Comp M)) (dflt : Comp M)
    (hP : ∀ n, CompEquiv C (pkgMeaning rd dflt (tbl.lookup n)) (pkgMeaning rd dflt (tbl'.lookup n))) :
    ∃ X X', binCompX S rd dflt b = .ok X ∧ binCompX S rd dflt b' = .ok X' ∧ CompEquiv C X X' := by
  obtain ⟨d, env, noms, rs, hd, hr, hc, hn⟩ := composeText_ok h
  obtain ⟨d', env', noms', rs', hd', hr', hc', -⟩ := composeText_ok h'
  have hdd : d' = d := by rw [hd] at hd'; cases hd'; rfl
  subst hdd
  obtain ⟨rfl, rfl⟩ := readPkgs_congr (fun k _ => hT k) hr hr'
  exact composeWasmX_equiv hc hc' (noValues_true hn) S rd dflt hP

/-- **Stream packages with the same whole output give equivalent compositions, from the text
and the bytes**: the packages are read from the bytes embedded in each binary, async built-ins
included, by `lowerXf κ`. -/
theorem composeText_stream_equiv {src : String} {raw raw' : List (String × ByteArray)}
    {b b' : ByteArray} {tbl tbl' : PkgTableX}
    (h : composeText src raw = .ok (b, some tbl, true))
    (h' : composeText src raw' = .ok (b', some tbl', true))
    (hT : ∀ k, (raw.lookup k).map TypeOf.decodeAnyX = (raw'.lookup k).map TypeOf.decodeAnyX)
    (S : Nat → PkgSig) (κ : Interp) (hr : RunAgree κ tbl tbl') :
    ∃ X X', binCompX S (lowerXf κ) dflt b = .ok X ∧ binCompX S (lowerXf κ) dflt b' = .ok X' ∧
      CompEquiv batchSem X X' :=
  composeText_equiv h h' hT S (lowerXf κ) dflt (runAgree_equiv hr)

end Silmaril.Wasm.Wac.EndToEnd
