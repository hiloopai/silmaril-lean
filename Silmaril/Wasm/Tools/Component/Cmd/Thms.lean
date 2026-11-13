module

public import Silmaril.Wasm.Tools.Component.Cmd.Defs
public import Silmaril.Wasm.Tools.Component.DummyFast.Thms
public import Silmaril.Wasm.Component.Binary.Thms
public import Silmaril.Wasm.Tools.Component.WitFast.Thms
public import Silmaril.Wasm.Tools.Component.WitText.Thms
public import Silmaril.Wasm.Wit.Tool.Source.Thms
public import Silmaril.Wasm.Wac.TargetsT.Thms
public import Silmaril.Wasm.JcoTool.NewCore.Thms
public import Silmaril.Wasm.JcoTool.Front.Thms
public import Silmaril.Wasm.JcoTool.AdaptLayout.Thms

/-!
# Specification of `wasm-tools component new / embed / wit / targets`

Stated against the formal objects of the existing verified cores:

* `selectWorld_mem`: the selected world is a world of the main package.
* `retag_size`, `retag_prefix`: the producers retag changes at most the last seven bytes.
* `postPayload_world`, `postPackage_decode`: the checked post-processing (`retag` and
  `AsyncNames.fixBytes`) keeps what a payload or package binary decodes to.
* `embed_module_eq`: what `component embed` writes is the module followed by one custom
  section `component-type` holding the payload of the selected world (`embedPayload`), as
  written (`postPayload`); `embed_sound`: for a package valid in the environment its binary
  shows, that written payload decodes (`decodeWorldType`) to the selected world of the package,
  in normal form, with the string encoding asked for (`Wit.Tool.embedBytes_sound`,
  `postPayload_world`); `embedDummy_eq`: `embed --dummy` is `embed` into the dummy module of the
  payload; `witWasmOfSrc_decode`: `wit --wasm` writes bytes that decode (strictly, or with
  plain async names read as async: `packageViewLax`) to the encoder's package.
* `targets_ok`: `component targets` succeeds exactly when the component's type is a subtype of
  the world's (`TargetsT.fitsB_iff`: WIT subtyping `Sub` of the two component kinds).
* `new_cases`: `component new` writes either the certified thin-wrapper layout of
  `NewCore.newMainC` (wasm-jco's custom sections appended) or the general layout of
  `AdaptLayout.newAdaptL`; `new_general_valid`: in the second case the bytes parse to a
  component whose reading is the planned layout and which the reference validator accepts
  (`AdaptLayout.newAdaptL_layout`); `new_thin_valid`: in the first case the bytes start with
  those of a component the reference validator accepts (`Front.newValid_valid`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Cmd

open Silmaril.Wasm.Wit

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-! ## Worlds -/

theorem any_fst_mem {ws : List (String × Binary.World)} {n : String}
    (h : ws.any (·.1 == n) = true) : n ∈ ws.map (·.1) := by
  obtain ⟨⟨m, w⟩, hm, he⟩ := List.any_eq_true.mp h
  have hmn : m = n := by simpa using he
  exact List.mem_map.mpr ⟨(m, w), hm, hmn⟩

theorem checkWorld_mem {p : Binary.Package} {q : Option String} {n m : String}
    (h : checkWorld p q n = .ok m) : m ∈ p.worlds.map (·.1) := by
  have key : p.worlds.any (·.1 == n) = true ∧ m = n := by
    unfold checkWorld at h
    dsimp only at h
    split at h <;> (repeat' split at h) <;> cases h <;> exact ⟨by assumption, rfl⟩
  rw [key.2]
  exact any_fst_mem key.1

/-- The selected world is a world of the main package. -/
theorem selectWorld_mem {p : Binary.Package} {w : Option String} {n : String}
    (h : selectWorld p w = .ok n) : n ∈ p.worlds.map (·.1) := by
  unfold selectWorld at h
  split at h
  · split at h
    · rename_i m wd hw
      cases h
      rw [hw]
      exact List.mem_singleton.mpr rfl
    · cases h
    · cases h
  · exact checkWorld_mem h

/-! ## Producers retag -/

theorem retag_cond {b : ByteArray}
    (h : (decide (b.size ≥ 22) && (b.extract (b.size - 22) b.size).toList == wcName ++ verOurs) = true) :
    b.size ≥ 22 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem tail_size : (⟨(verUpstream.drop 1).toArray⟩ : ByteArray).size = 7 := rfl

theorem retag_size (b : ByteArray) : (retag b).size = b.size := by
  unfold retag
  split
  · rename_i h
    have hn : b.size ≥ 22 := retag_cond h
    rw [ByteArray.size_append, ByteArray.size_extract, tail_size]
    omega
  · rfl

/-- Only the last seven bytes may change. -/
theorem retag_prefix (b : ByteArray) :
    (retag b).extract 0 (b.size - 7) = b.extract 0 (b.size - 7) := by
  unfold retag
  split
  · rename_i h
    have hn : b.size ≥ 22 := retag_cond h
    have hs : (b.extract 0 (b.size - 7)).size = b.size - 7 := by
      rw [ByteArray.size_extract]
      omega
    rw [ByteArray.extract_append_eq_left hs.symm]
  · rfl

/-! ## Checked post-processing -/

/-- **`retag` and `fixBytes` keep the decoded world**: the payload as written is the encoder's
payload, or bytes that decode (plain async names allowed) to the world the encoder's payload
decodes to. -/
theorem postPayload_world {pl : ByteArray} {x}
    (h : Binary.decodeWorldType pl = .ok x) :
    Binary.decodeWorldTypeLax (postPayload pl) = .ok x ∨ postPayload pl = pl := by
  unfold postPayload
  dsimp only
  split
  · rename_i he
    left
    unfold payloadWorld payloadWorldLax at he
    rw [h] at he
    cases hq : Binary.decodeWorldTypeLax (retag (Wac.AsyncNames.fixBytes pl)) with
    | error e => rw [hq] at he; cases he
    | ok y =>
      rw [hq] at he
      cases he
      rfl
  · exact Or.inr rfl

/-- **`retag` and `fixBytes` keep the decoded package**: the package binary as written is the
encoder's bytes, or bytes that decode, with plain async names read as async
(`packageViewLax`), to the package and environment the encoder's bytes decode to. -/
theorem postPackage_decode {pb : ByteArray} {d : Tool.Decoded}
    (h : Tool.decode pb = .ok d) :
    postPackage pb = pb ∨ packageViewLax (postPackage pb) = some (d.pkg, d.env) := by
  unfold postPackage
  dsimp only
  split
  · rename_i he
    refine Or.inr ?_
    rw [he]
    unfold packageView
    rw [h]
    rfl
  · exact Or.inl rfl

/-! ## `component embed` -/

/-- **What `embed` writes**: the module, then the `component-type` section of the selected world's
payload as written (`postPayload`). -/
theorem embed_module_eq {src : WitSrc} {w : Option String} {se : Binary.StringEncoding}
    {m out : ByteArray} (h : embed src w se (.module m) = .ok out) :
    ∃ pb d n pl s, pkgBytes src = .ok pb ∧ Tool.decode pb = .ok d ∧ selectWorld d.pkg w = .ok n ∧
      Tool.embedBytes pb n se = .ok pl ∧
      Binary.customSection Binary.componentTypeSection (postPayload pl) = some s ∧
      out = m ++ s := by
  unfold embed at h
  obtain ⟨pb, hpb, h⟩ := bind_ok h
  obtain ⟨d, hd, h⟩ := bind_ok h
  obtain ⟨n, hn, h⟩ := bind_ok h
  obtain ⟨pl, hpl, h⟩ := bind_ok h
  have hm : Binary.embedPayload m (postPayload pl) = .ok out := h
  unfold Binary.embedPayload at hm
  obtain ⟨cs, _, hm⟩ := bind_ok hm
  cases hs : Binary.customSection Binary.componentTypeSection (postPayload pl) with
  | none => rw [hs] at hm; cases hm
  | some s =>
    rw [hs] at hm
    cases hm
    exact ⟨pb, d, n, pl, s, hpb, hd, hn, hpl, hs, rfl⟩

/-- **Soundness of `embed`**: for a package valid in the environment its binary shows, the
payload of the selected world decodes to it, and the payload appended (async names fixed,
retagged: `postPayload`) is that payload or bytes that decode to the same world. -/
theorem embed_sound {src : WitSrc} {w : Option String} {se : Binary.StringEncoding}
    {m out : ByteArray} (h : embed src w se (.module m) = .ok out)
    (hv : ∀ pb d, pkgBytes src = .ok pb → Tool.decode pb = .ok d → d.pkg.Valid d.env) :
    ∃ pb d n pl s wd, pkgBytes src = .ok pb ∧ Tool.decode pb = .ok d ∧
      selectWorld d.pkg w = .ok n ∧ (n, wd) ∈ d.pkg.worlds ∧
      Binary.decodeWorldType pl = .ok (d.pkg.name, n, wd.normalize, se) ∧
      (Binary.decodeWorldTypeLax (postPayload pl) = .ok (d.pkg.name, n, wd.normalize, se) ∨
        postPayload pl = pl) ∧
      Binary.customSection Binary.componentTypeSection (postPayload pl) = some s ∧
      out = m ++ s := by
  obtain ⟨pb, d, n, pl, s, hpb, hd, hn, hpl, hs, ho⟩ := embed_module_eq h
  obtain ⟨wd, hmem, hdec⟩ := Tool.embedBytes_sound hd (hv pb d hpb hd) hpl
  exact ⟨pb, d, n, pl, s, wd, hpb, hd, hn, hmem, hdec, postPayload_world hdec, hs, ho⟩

/-- **`embed --dummy`** is `embed` into the dummy module of the selected world's payload
(computed with bounded flattening; it is `Dummy.dummyOfPayload`'s module wherever that one is
defined: `embedDummy_spec`). -/
theorem embedDummy_eq {src : WitSrc} {w : Option String} {se : Binary.StringEncoding}
    {mg : Dummy.Mangling} {out : ByteArray} (h : embedDummy src w se mg = .ok out) :
    ∃ pb d n pl core, pkgBytes src = .ok pb ∧ Tool.decode pb = .ok d ∧
      selectWorld d.pkg w = .ok n ∧ Tool.embedBytes pb n se = .ok pl ∧
      DummyFast.dummyOfPayloadFast pl mg = .ok core ∧
      embed src w se (.module core) = .ok out := by
  unfold embedDummy at h
  obtain ⟨pb, hpb, h⟩ := bind_ok h
  obtain ⟨d, hd, h⟩ := bind_ok h
  obtain ⟨n, hn, h⟩ := bind_ok h
  obtain ⟨pl, hpl, h⟩ := bind_ok h
  obtain ⟨core, hcore, h⟩ := bind_ok h
  refine ⟨pb, d, n, pl, core, hpb, hd, hn, hpl, hcore, ?_⟩
  unfold embed
  rw [hpb]
  change (Tool.decode pb >>= _) = _
  rw [hd]
  change (selectWorld d.pkg w >>= _) = _
  rw [hn]
  change (Tool.embedBytes pb n se >>= _) = _
  rw [hpl]
  exact h

/-- **`embed --dummy` against the specification**: when `Dummy.dummyOfPayload` (full
flattening) gives the dummy module `core` of the payload, `embed --dummy` embeds into exactly
that module. -/
theorem embedDummy_spec {src : WitSrc} {w : Option String} {se : Binary.StringEncoding}
    {mg : Dummy.Mangling} {out : ByteArray} (h : embedDummy src w se mg = .ok out)
    {pb pl core : ByteArray} {d : Tool.Decoded} {n : String} (hpb : pkgBytes src = .ok pb)
    (hd : Tool.decode pb = .ok d) (hn : selectWorld d.pkg w = .ok n)
    (hpl : Tool.embedBytes pb n se = .ok pl) (hcore : Dummy.dummyOfPayload pl mg = .ok core) :
    embed src w se (.module core) = .ok out := by
  obtain ⟨pb', d', n', pl', core', hpb', hd', hn', hpl', hcore', ho⟩ := embedDummy_eq h
  have e1 : pb' = pb := Except.ok.inj (hpb'.symm.trans hpb)
  have e2 : d' = d := Except.ok.inj (hd'.symm.trans (e1 ▸ hd))
  have e3 : n' = n := Except.ok.inj (hn'.symm.trans (e2 ▸ hn))
  have e4 : pl' = pl := Except.ok.inj (hpl'.symm.trans (e1 ▸ e3 ▸ hpl))
  have hfast : DummyFast.dummyOfPayloadFast pl mg = .ok core :=
    DummyFast.dummyOfPayloadFast_eq hcore
  have e5 : core' = core := Except.ok.inj (hcore'.symm.trans (e4 ▸ hfast))
  rw [← e5]
  exact ho

/-- **The lax package bytes** (`WitText.laxPackageBytes`, the fallback of `component wit` on a
WIT package binary that the strict decoder refuses) are read by the strict decoder exactly as
the original bytes are read with plain async names allowed (`packageViewLax`): the normalized
sections round-trip through the component encoder (`Component.Binary.parse_encode`). -/
theorem laxPackageBytes_view {b b' : ByteArray} (h : WitText.laxPackageBytes b = some b') :
    packageView b' = packageViewLax b := by
  unfold WitText.laxPackageBytes at h
  unfold packageViewLax
  split at h
  · rename_i ss hp
    have hp' : Silmaril.Wasm.Component.Binary.parse b' = .ok (.mk (Binary.normSections ss)) :=
      Silmaril.Wasm.Component.Binary.parse_encode h
    rw [hp]
    show ((Tool.decode b').toOption.map fun d => (d.pkg, d.env)) = _
    unfold Tool.decode Binary.decodePackage Binary.decodeEnv
    rw [hp']
    dsimp only
    cases Binary.decodeSections (Binary.normSections ss) <;>
      cases Binary.itemViews (Binary.splitCustom (Binary.normSections ss)).1 <;> rfl
  · cases h

/-- **`component wit` of a WIT package binary**: the text printed is that of the bytes, or,
when the strict decoder refuses them, that of the lax package bytes, which the strict decoder
reads as `packageViewLax` reads the input (`laxPackageBytes_view`). -/
theorem componentWit_package {b : ByteArray} {t : String} (hp : JcoTool.WitOf.isWitPackage b)
    (h : WitText.componentWit b = .ok t) :
    Tool.witAll b = .ok t ∨
      ∃ b', WitText.laxPackageBytes b = some b' ∧ Tool.witAll b' = .ok t ∧
        packageView b' = packageViewLax b := by
  unfold WitText.componentWit at h
  rw [ite_eq_left hp] at h
  split at h
  · rename_i t' ht
    exact Or.inl (ht.trans h)
  · split at h
    · rename_i b' hb
      refine Or.inr ⟨b', hb, ?_, laxPackageBytes_view hb⟩
      cases hw : Tool.witAll b' with
      | ok t'' => rw [hw] at h; exact h
      | error e' => rw [hw] at h; cases h
    · cases h

/-- **`wit --wasm` of WIT text**: the package binary as written decodes to the package and
environment of the verified encoder's bytes. -/
theorem witWasmOfSrc_decode {src : WitSrc} {pb b : ByteArray} {d : Tool.Decoded}
    (hpb : pkgBytes src = .ok pb) (hd : Tool.decode pb = .ok d)
    (h : witWasmOfSrc src = .ok b) :
    Tool.decode b = .ok d ∨ packageViewLax b = some (d.pkg, d.env) := by
  unfold witWasmOfSrc at h
  rw [hpb] at h
  cases h
  rcases postPackage_decode hd with he | he
  · exact Or.inl (by rw [show postPackage pb = pb from he]; exact hd)
  · exact Or.inr he

/-! ## Features -/

/-- Without features, `pkgBytesF` is `pkgBytes`. -/
theorem pkgBytesF_nil (src : WitSrc) : pkgBytesF [] src = pkgBytes src := by
  cases src <;>
    simp only [pkgBytesF, pkgBytes, WitFast.encodeTextXFast_eq, WitText.encodeTextXF_nil]

/-! ## `component targets` -/

/-- **`targets` succeeds exactly on a fit**: the component's kind is a WIT subtype of the
selected world's. -/
theorem targets_ok {src : WitSrc} {w : Option String} {comp : ByteArray}
    (h : targets src w comp = .ok ()) :
    ∃ pb d n mis, pkgBytes src = .ok pb ∧ Tool.decode pb = .ok d ∧ selectWorld d.pkg w = .ok n ∧
      Wac.TargetsT.check comp pb (some n) = .ok (true, mis) := by
  unfold targets at h
  obtain ⟨pb, hpb, h⟩ := bind_ok h
  obtain ⟨d, hd, h⟩ := bind_ok h
  obtain ⟨n, hn, h⟩ := bind_ok h
  obtain ⟨⟨fits, mis⟩, hc, h⟩ := bind_ok h
  cases fits with
  | false => cases h
  | true => exact ⟨pb, d, n, mis, hpb, hd, hn, hc⟩

/-- The verdict of `check` is WIT subtyping of the component's and the world's kinds. -/
theorem check_true_sub {comp pb : ByteArray} {w : Option String} {mis : List String}
    (h : Wac.TargetsT.check comp pb w = .ok (true, mis)) :
    ∃ p q wi we, (Wac.TypeOf.decodeAny comp).map Prod.fst = .ok p ∧
      (Wac.Bridge.decodePkg pb).map Prod.fst = .ok q ∧ Wac.TargetsT.worldOf q.defs w = .ok (wi, we) ∧
      Wac.Sub (.comp none p.imports p.exports)
        (.comp none (Wac.TargetsT.promoteEx wi) (Wac.TargetsT.promoteEx we)) := by
  unfold Wac.TargetsT.check at h
  obtain ⟨⟨p, x⟩, hp, h⟩ := bind_ok h
  obtain ⟨⟨q, y⟩, hq, h⟩ := bind_ok h
  obtain ⟨⟨wi, we⟩, hw, h⟩ := bind_ok h
  have hf : Wac.TargetsT.fitsB p.imports p.exports wi we = true :=
    (Prod.mk.inj (Except.ok.inj h)).1
  refine ⟨p, q, wi, we, ?_, ?_, hw, (Wac.TargetsT.fitsB_iff _ _ _ _).mp hf⟩
  · rw [hp]; rfl
  · rw [hq]; rfl

/-! ## `component new` -/

/-- What `newWith` writes, in one of the two layouts. -/
def NewOut (bytes : ByteArray) (ads : List (String × ByteArray)) (g : Bool) (b : ByteArray) : Prop :=
  (ads = [] ∧ ∃ o, JcoTool.NewCore.newMainC bytes none = .ok (some o) ∧
      b = (JcoTool.Adapt.withMeta o (JcoTool.Adapt.certifiedNames o.cores.length)).bytes) ∨
    ∃ ads' ls, (ads' = ads ∨ ads' = []) ∧ JcoTool.AdaptLayout.newAdaptL bytes none ads' g = .ok (b, ls)

theorem map_fst_ok {ε α β : Type} {x : Except ε (α × β)} {a : α} (h : (Prod.fst <$> x) = .ok a) :
    ∃ c, x = .ok (a, c) := by
  cases x with
  | error e => cases h
  | ok r => cases h; exact ⟨r.2, rfl⟩

/-- Without adapters: the thin wrapper, else the general layout. -/
theorem newWith_empty {bytes b : ByteArray} {g : Bool} (h : newWith bytes [] g = .ok b) :
    NewOut bytes [] g b := by
  unfold newWith at h
  have hm : (match JcoTool.NewCore.newMainC bytes none with
      | .ok (some o) =>
        Except.ok (JcoTool.Adapt.withMeta o (JcoTool.Adapt.certifiedNames o.cores.length)).bytes
      | r => match JcoTool.AdaptLayout.newAdaptL bytes none [] g with
        | .ok (b, _) => .ok b
        | .error e2 => .error (newErr r e2)) = Except.ok b := h
  split at hm
  · rename_i o hn
    cases hm
    exact Or.inl ⟨rfl, o, hn, rfl⟩
  · split at hm
    · rename_i b' ls hl
      cases hm
      exact Or.inr ⟨[], ls, Or.inr rfl, hl⟩
    · cases hm

/-- With adapters: the general layout with them. -/
theorem newWith_adapters {bytes b : ByteArray} {ads : List (String × ByteArray)} {g : Bool}
    (hne : ads ≠ []) (h : newWith bytes ads g = .ok b) : NewOut bytes ads g b := by
  have hn : (!ads.isEmpty) = true := by simpa using hne
  have hl : (Prod.fst <$> JcoTool.AdaptLayout.newAdaptL bytes none ads g) = .ok b := by
    simpa [newWith, hn] using h
  obtain ⟨ls, hls⟩ := map_fst_ok hl
  exact Or.inr ⟨ads, ls, Or.inl rfl, hls⟩

/-- **The two layouts of `new`.** -/
theorem new_cases {core : ByteArray} {ads : List (String × ByteArray)} {g : Bool} {b : ByteArray}
    (h : new core ads g = .ok b) :
    ∃ bytes, JcoTool.Cm32.prepare core = .ok bytes ∧ NewOut bytes ads g b := by
  have hc : isComponent core = false := by
    cases hic : isComponent core
    · rfl
    · simp [new, hic] at h
  have hb : ((JcoTool.Cm32.prepare core).bind fun bytes => newWith bytes ads g) = .ok b := by
    simpa [new, hc] using h
  obtain ⟨bytes, hp, hw⟩ := bind_ok hb
  refine ⟨bytes, hp, ?_⟩
  cases ads with
  | nil => exact newWith_empty hw
  | cons a as => exact newWith_adapters (List.cons_ne_nil a as) hw

/-- **The general layout's certificate**, for outputs of `new` in that layout. -/
theorem new_general_valid {bytes b : ByteArray} {ads : List (String × ByteArray)} {g : Bool}
    {ls : List String} (h : JcoTool.AdaptLayout.newAdaptL bytes none ads g = .ok (b, ls)) :
    ∃ p x c ct, JcoTool.Adapt.plan bytes none ads g = .ok p ∧ JcoTool.xparse b = .ok x ∧
      JcoTool.AdaptLayout.readA (JcoTool.AdaptLayout.namesOf p) x =
        some (JcoTool.AdaptLayout.expectedA p) ∧
      JcoTool.LayoutRefX.toRefX Silmaril.Wasm.Binary.Core.decode? x = some c ∧
      Silmaril.Wasm.Component.Reference.Valid Silmaril.Wasm.Component.Features.all c ct :=
  JcoTool.AdaptLayout.newAdaptL_layout h

/-- **The thin-wrapper layout's certificate**: the bytes written start with those of a component
the reference validator accepts (wasm-jco's custom sections follow). -/
theorem new_thin_valid {bytes : ByteArray} {o : JcoTool.Tool.Out}
    (h : JcoTool.NewCore.newMainC bytes none = .ok (some o)) :
    ∃ x c ct m, JcoTool.xparse o.bytes = .ok x ∧
      JcoTool.LayoutRefX.toRefX Silmaril.Wasm.Binary.Core.decode? x = some c ∧
      Silmaril.Wasm.Component.Reference.Valid Silmaril.Wasm.Component.Features.all c ct ∧
      (JcoTool.Adapt.withMeta o (JcoTool.Adapt.certifiedNames o.cores.length)).bytes = o.bytes ++ m := by
  rw [JcoTool.NewCore.newMainC_eq] at h
  split at h
  · cases h
  · obtain ⟨r, hr, h⟩ := bind_ok h
    have hr' : Silmaril.Wasm.Perf.JcoMain.newDefaultC bytes none = .ok o := by
      cases h
      exact hr
    rw [Silmaril.Wasm.Perf.JcoMain.newDefaultC_eq] at hr'
    obtain ⟨wf, _, hr'⟩ := bind_ok hr'
    obtain ⟨o', ho', hr'⟩ := bind_ok hr'
    have hoo : o = Silmaril.Wasm.Perf.JcoMain.fixSummary o' := by
      cases hr'
      rfl
    obtain ⟨_, x, c, ct, _, _, hx, hc, hv⟩ := JcoTool.Front.newValid_valid ho'
    obtain ⟨m, hm⟩ := JcoTool.Adapt.withMeta_bytes o (JcoTool.Adapt.certifiedNames o.cores.length)
    have hb : o.bytes = o'.bytes := by rw [hoo]; rfl
    exact ⟨x, c, ct, m, hb ▸ hx, hc, hv, hm⟩

end Silmaril.Wasm.Tools.Component.Cmd
