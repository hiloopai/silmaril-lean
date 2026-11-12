module

public import Silmaril.X86.BinInstitution.Defs
public import Silmaril.X86.Exact.Thms
import Silmaril.Proofs.X86.BinInstitution.Rely

/-!
# The x86 institution over arbitrary binaries: what is proved

The institution `inst V : Sign ⥤ Room` (`classic V`, `bundled V`), the comorphism from the
per-binary institution `embedCoHom` and the corridor `pin` are defined in `Defs`. Here:

**Institution.**

* `satisfaction`, `classic_sat_iff`: the satisfaction condition (the listing of a `fn`
  sentence is renamed, its placement and contract kept);
* `wf_map`: translation keeps well-formed sentences well formed (a renamed listing is read by
  the target decoder);
* `sat_of_le`, `sat_of_top`: satisfaction moves down along refinement, for every sentence
  (`dyn` and `proc` included, because their imports' contracts are linked into the model,
  `le_withImports`), so a sentence of the top holds in every model.

**Effects and the rely.**

* `resultX_ofSpec_iff`, `mustTotal_ofSpec_iff`: a plain spec as a contract with the `silent`
  effect is silmaril's (`ResultV`, `Spec.MustTotal`);
* `le_withImports`: linking the imports' contracts in is monotone;
* `must_of_withImports`: **the rely discharged**: when the model meets every bound import's
  contract, a run property of the linked model holds of the model; `DynSen.mustTotal_of_imports`
  and `ProcSen.must_of_imports` are its two uses.

**The loose machine of a decoder.**

* `loose_ofTable`, `top_ofSig`: on a per-binary table it *is* silmaril's
  `X86Loose.rel` (`rfl`), so the per-binary institution is the restriction to finite
  decoders;
* `loose_antitone`: a bigger decoder gives a smaller top;
* `le_loose_of_singletons`: a machine is below the top of a decoder when it is below the
  per-binary top of each one-entry table of it;
* `le_table`: **a model of `A` is below the per-binary top of every table that `A`
  decodes**, the image-by-image reading of a model;
* `sat_family_of_table`, `sat_fn_of_table`: a sentence proved on the per-binary top of an
  image's table holds in every model of the ISA (the transfer `pin` packages).

**The machines as models** (through silmaril's `Exact`).

* `le_ofIsa`, `exactModel`: **a machine is a model of its exact ISA signature**
  `Sign.ofIsa I` (its decoder, its exact forms), for every `I : SegVC.Isa σ`;
* the signatures `sOpen` (`Ext8`, `Open.isa`), `sOpen9` (`Ext9`, `Open9.isa`), `sStr9`
  (`Str9.isa`), and `sSv1`, `sSv1₉` (silmaril's loose `Σ v1` over the `Str9` and the
  `Open9` decoder);
* the morphisms `openOpen9 : sOpen ⟶ sOpen9` (renaming `.ext8`), `open9Str9 : sOpen9 ⟶ sStr9`
  (renaming `.ext9`): **ISA inclusion `Ext8 ⊆ Ext9 ⊆ Str9`**; `sv1Str9 : sSv1 ⟶ sStr9` and
  `sv1Open9 : sSv1₉ ⟶ sOpen9`: **`Σ v1 ⟶ Σexact`** (silmaril's `Exact.sv1Tight`);
  `sv1₉Sv1 : sSv1₉ ⟶ sSv1` (renaming `.ext9`), and the square commutes (`square`);
* `open9Model`, `str9Model`, `openModel`: `Open9`, `Str9`, `Open` as models of their exact
  signatures; by reduct, `Str9` is a model of `sOpen9` and every one is a model of `Σ v1`.

**Deterministic machines.** `mustTotal_ofIsa_of_total`: on `ofIsa I`, `Spec.Total` gives
`Spec.MustTotal` (the converse of silmaril's `Problems.total_of_mustTotal_ofIsa`), so an
angelic proof on a deterministic machine is a satisfaction in the institution.

The worked example (`ilog2_u32` as a sentence of `Ext9`, proved in the models `Open9` and,
after translation to `Str9`, `Str9`) is `Silmaril/Proofs/X86/BinInstitution/Ilog2.lean`.
-/

@[expose] public section

namespace Silmaril.X86.BinInstitution

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.X86 (Word Byte RelIsa MState)
open Silmaril.X86.RelIsa (Views Le Progress ofIsa)
open Silmaril.X86.Loose (DEntry DTable FormSpec)
open Silmaril.X86.FnContract (Spec)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Project.Shapes (Placement)

variable {Φ σ : Type} {V : Views σ}

/-! ## The institution -/

/-- **The satisfaction condition**: a model of `B` satisfies the translation of a sentence of
`A` iff its reduct satisfies the sentence. -/
theorem satisfaction {A B : Sign} (f : Sign.Hom A B) (M : Model V B) (φ : Sen A.Φ σ) :
    Sat V M.1 (φ.map f.ρ) ↔ Sat V (M.reduct f).1 φ :=
  (corridor V f).sat M φ

/-- The satisfaction condition of `classic V` is that of `inst V`. -/
theorem classic_sat_iff {A B : Sign} (f : Sign.Hom A B) (M : (room V B).Mod) (φ : Sen A.Φ σ) :
    (room V B).Sat M ((corridor V f).sen φ) ↔ (room V A).Sat ((corridor V f).mod.obj M) φ :=
  (corridor V f).sat M φ

/-- Translation renames the listing and keeps the code. -/
theorem Sen.listed_map {Ψ : Type} (ρ : Φ → Ψ) (φ : Sen Φ σ) :
    (φ.map ρ).listed = φ.listed.map fun cL => (cL.1, cL.2.map ρ) := by
  cases φ <;> rfl

/-- **Translation keeps sentences well formed.** -/
theorem wf_map {A B : Sign} (f : Sign.Hom A B) {φ : Sen A.Φ σ} (h : φ.WF A.sig) :
    (φ.map f.ρ).WF B.sig := by
  intro code L hL it hit
  rw [Sen.listed_map] at hL
  obtain ⟨⟨c, L₀⟩, h₀, he⟩ := Option.map_eq_some_iff.1 hL
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  simp only [Listing.map, List.mem_map] at hit
  obtain ⟨it', hit', rfl⟩ := hit
  exact ⟨(h _ _ h₀ it' hit').1, f.dec _ (h _ _ h₀ it' hit').2⟩

/-- Satisfaction moves down along refinement. -/
theorem sat_of_le' {C D : RelIsa σ} (hle : Le C D) {φ : Sen Φ σ} (h : Sat V D φ) :
    Sat V C φ := by
  cases φ with
  | fn p L S => exact Silmaril.X86.FnContract.Spec.MustTotalIn.of_le hle h
  | elf Ld exe p L S => exact ⟨h.1, Silmaril.X86.FnContract.Spec.MustTotalIn.of_le hle h.2⟩
  | dyn d =>
    intro r hr hres
    obtain ⟨b, hb, hm⟩ := h r hr hres
    exact ⟨b, hb, Silmaril.X86.FnContract.Spec.MustTotalIn.of_le
      (Silmaril.Proofs.X86.BinInstitution.le_withImports hle r _) hm⟩
  | proc P =>
    intro r s hs hl hres
    exact RelIsa.Must.of_le (Silmaril.Proofs.X86.BinInstitution.le_withImports hle r _) hl
      (h r s hs ((RelIsa.Le.live_iff hle) ▸ hl) hres)
  | family φ => exact Silmaril.X86.Institution.sat_of_le' hle h

/-- Satisfaction is closed downwards along the model order. -/
theorem sat_of_le {A : Sign} {M M' : Model V A} (hle : M ≤ M') {φ : Sen A.Φ σ}
    (h : Sat V M'.1 φ) : Sat V M.1 φ :=
  sat_of_le' hle h

/-- **A sentence of the top holds in every model.** -/
theorem sat_of_top {A : Sign} {φ : Sen A.Φ σ} (h : Sat V (A.sig.top V) φ) (M : Model V A) :
    Sat V M.1 φ :=
  sat_of_le' M.2.1 h

/-! ## The loose machine of a decoder -/

/-- On a per-binary table, the loose machine of a decoder is silmaril's. -/
theorem loose_ofTable (D : DTable Φ) (S : Silmaril.X86.Loose.Sigma Φ) :
    loose (Decoder.ofTable D) S V = Silmaril.X86.Loose.X86Loose.rel D S V := rfl

/-- The top of a per-binary signature, read as an ISA signature, is its top. -/
theorem top_ofSig (G : Silmaril.X86.Institution.Sig Φ) :
    (ISig.ofSig G).top V = G.top V := rfl

/-- **A bigger decoder gives a smaller top.** -/
theorem loose_antitone {d d' : Decoder Φ} (h : d ⊆ d') (S : Silmaril.X86.Loose.Sigma Φ) :
    Le (loose d' S V) (loose d S V) :=
  Sign.Hom.topLe (A := ⟨Φ, ⟨d, S, {}⟩⟩) (B := ⟨Φ, ⟨d', S, {}⟩⟩) V
    ⟨id, fun _ he => h he, fun _ F hF => ⟨F, hF, FormSpec.Tightens.refl F⟩⟩

/-- **Below every one-entry top, below the top**: a machine with the views `V` that refines
the per-binary top of each one-entry table of `d` refines the top of `d`. -/
theorem le_loose_of_singletons {C : RelIsa σ} {d : Decoder Φ} {S : Silmaril.X86.Loose.Sigma Φ}
    (hv : C.toViews = V) (h : ∀ e ∈ d, Le C (Silmaril.X86.Loose.X86Loose.rel [e] S V)) :
    Le C (loose d S V) := by
  subst hv
  exact ⟨rfl, fun {s r} hl hs => ⟨fun e he hat F hF =>
    ((h e he).step hl hs).1 e (List.mem_singleton_self e) hat F hF,
    fun t ht => C.live_step hl (ht ▸ hs)⟩⟩

/-- **A model of `A` is below the per-binary top of every table that `A` decodes**: one
machine refines, image by image, the loose machine of each image's code. -/
theorem le_table {A : Sign} (M : Model V A) (D : DTable A.Φ) (hD : ∀ e ∈ D, e ∈ A.sig.dec) :
    Le M.1 ((pinSig A D).top V) :=
  M.2.1.trans (Sign.Hom.topLe V (pinHom A D hD))

/-- **Per-binary proofs transfer**: a contract family proved on the per-binary top of a table
that `A` decodes holds in every model of `A`. -/
theorem sat_family_of_table {A : Sign} (D : DTable A.Φ) (hD : ∀ e ∈ D, e ∈ A.sig.dec)
    {φ : Word → Spec σ} (h : Silmaril.X86.Institution.Sat ((pinSig A D).top V) φ)
    (M : Model V A) : Sat V M.1 (Sen.family (Φ := A.Φ) φ) :=
  Silmaril.X86.Institution.sat_of_le' (le_table M D hD) h

/-- A `fn` sentence whose placed contract holds on the per-binary top of a table that `A`
decodes holds in every model of `A`. -/
theorem sat_fn_of_table {A : Sign} (D : DTable A.Φ) (hD : ∀ e ∈ D, e ∈ A.sig.dec)
    {p : Placement} {L : Listing A.Φ} {S : Spec σ}
    (h : (Spec.at V p S).MustTotal ((pinSig A D).top V)) (M : Model V A) :
    Sat V M.1 (Sen.fn p L S) :=
  Silmaril.X86.FnContract.Spec.MustTotalIn.of_le (le_table M D hD) h

/-! ## ELF level -/

/-- **`Places` with the x86-64 loader is silmaril's `Pinned.LoadedAt`** of the code at the
placement's base. -/
theorem places_x86_iff (exe : Silmaril.X86.Link.Blob) (p : Placement) :
    Places ELoader.x86 exe p ↔ Silmaril.X86.Ladder.Pinned.LoadedAt exe "rx" p.base.toNat p.code := by
  constructor
  · rintro ⟨img, h, seg, hs, hp, hsl⟩
    obtain ⟨recs, hr, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨recs, hr, seg, hs, hp, hsl⟩
  · rintro ⟨recs, hr, seg, hs, hp, hsl⟩
    exact ⟨_, by simp [ELoader.x86, ELoader.lps, hr], seg, hs, hp, hsl⟩

/-- An `elf` sentence is its `Places` fact and the `fn` sentence of its placement. -/
theorem sat_elf_iff {C : RelIsa σ} {Ld : ELoader} {exe : Silmaril.X86.Link.Blob} {p : Placement}
    {L : Listing Φ} {S : Spec σ} :
    Sat V C (Sen.elf Ld exe p L S) ↔ Places Ld exe p ∧ Sat V C (Sen.fn p L S) := Iff.rfl

/-! ## Effects and the rely -/

/-- A plain spec as a contract with the `silent` effect: its result is silmaril's. -/
theorem resultX_ofSpec_iff {S : Spec σ} {s t : σ} :
    (XSpec.ofSpec V S).ResultX V s t ↔ S.ResultV V s t :=
  ⟨fun h => ⟨h.effect, h.abi, h.frame, h.post⟩, fun h => ⟨h.silent, h.abi, h.frame, h.post⟩⟩

/-- A plain spec as a contract with the `silent` effect: total correctness is silmaril's. -/
theorem mustTotal_ofSpec_iff {A : RelIsa σ} {S : Spec σ} :
    (XSpec.ofSpec A.toViews S).MustTotal A ↔ S.MustTotal A := by
  have : ∀ s, (XSpec.ofSpec A.toViews S).ResultX A.toViews s = S.ResultV A.toViews s :=
    fun s => funext fun t => propext resultX_ofSpec_iff
  simp only [XSpec.MustTotal, Silmaril.X86.FnContract.Spec.MustTotalIn, this]
  rfl

/-- **Linking the imports' contracts in is monotone.** -/
theorem le_withImports {C₀ C : RelIsa σ} (h : Le C₀ C) (r : DynLoad) (Γ : Imports σ) :
    Le (withImports C₀ r Γ) (withImports C r Γ) :=
  Silmaril.Proofs.X86.BinInstitution.le_withImports h r Γ

/-- **The rely discharged**: when `C` meets the contract of every bound import, a run property
of the model with the contracts linked in holds of `C`. -/
theorem must_of_withImports {C : RelIsa σ} {r : DynLoad} {Γ : Imports σ}
    (hΓ : ∀ im ∈ Γ, ∀ a, r.resolve im.1 = some a → (im.2 a).MustTotal C) {Q : σ → Prop}
    {s : σ} (h : RelIsa.Must (withImports C r Γ) (fun _ => True) Q s) (hl : C.live s) :
    RelIsa.Must C (fun _ => True) Q s :=
  Silmaril.Proofs.X86.BinInstitution.must_of_withImports hΓ h hl

/-- A dynamic sentence's contract holds on the model itself when the model meets the imports'
contracts at the bindings of a load. -/
theorem DynSen.mustTotal_of_imports {C : RelIsa σ} {d : DynSen Φ σ} {r : DynLoad} {b : Word}
    (hΓ : ∀ im ∈ d.imports, ∀ a, r.resolve im.1 = some a → (im.2 a).MustTotal C)
    (h : (Spec.at V (d.place b) (d.spec r)).MustTotal (withImports C r d.imports)) :
    (Spec.at V (d.place b) (d.spec r)).MustTotal C :=
  fun s hl ha he => must_of_withImports hΓ (h s hl ha he) hl

/-- A process sentence's conclusion holds on the model itself when the model meets the
imports' contracts at the bindings of the load. -/
theorem ProcSen.must_of_imports {C : RelIsa σ} {P : ProcSen σ} (hP : P.Sat C) {r : DynLoad}
    {s : σ} (hs : P.loader.Starts P.exe P.libs P.env r s) (hl : C.live s)
    (hres : r.Resolves P.imports)
    (hΓ : ∀ im ∈ P.imports, ∀ a, r.resolve im.1 = some a → (im.2 a).MustTotal C) :
    RelIsa.Must C (fun _ => True) (P.obs.Done P.post) s :=
  must_of_withImports hΓ (hP r s hs hl hres) hl

/-! ## Deterministic machines -/

/-- **On a deterministic machine, `Spec.Total` is `Spec.MustTotal`.** -/
theorem mustTotal_ofIsa_of_total {I : Isa σ} {S : Spec σ} (h : S.Total I) :
    S.MustTotal (ofIsa I) := by
  intro s hl ha he
  obtain ⟨t, ⟨n, hn⟩, hr⟩ := h s hl ha he
  refine RelIsa.must_ofIsa_iff.2 ⟨t, ?_, ⟨hr.silent, hr.abi, hr.frame, hr.post⟩⟩
  clear hl ha he hr
  induction n generalizing s with
  | zero => cases Option.some.inj hn; exact .refl _
  | succ n ih =>
    simp only [Silmaril.Machine.Execution.run_succ] at hn
    cases hs : I.step s with
    | none => simp [hs] at hn
    | some s' =>
      simp only [hs, Option.bind_some] at hn
      exact .step trivial hs (ih s' hn)

/-! ## The machines as models -/

/-- The exact ISA signature of a machine, bundled. -/
def Sign.ofIsa (I : Isa σ) : Sign := ⟨I.Instr, ISig.ofIsa I⟩

/-- **A machine is below the top of its exact ISA signature.** -/
theorem le_ofIsa (I : Isa σ) :
    Le (ofIsa I) ((Sign.ofIsa I).sig.top (Views.ofIsa I)) :=
  le_loose_of_singletons rfl fun e he =>
    Silmaril.X86.Exact.le_exact I [e] fun e' he' => by
      rw [List.mem_singleton.1 he']; exact he

/-- **A machine is a model of its exact ISA signature.** -/
def exactModel (I : Isa σ) : Model (Views.ofIsa I) (Sign.ofIsa I) :=
  ⟨ofIsa I, le_ofIsa I, RelIsa.progress_ofIsa⟩

/-- `Ext8` (`Open.isa`). -/
abbrev sOpen : Sign := Sign.ofIsa Silmaril.X86.Open.isa
/-- `Ext9` (`Open9.isa`). -/
abbrev sOpen9 : Sign := Sign.ofIsa Silmaril.X86.Open9.isa
/-- `Ext9` with the string forms (`Str9.isa`): `Σexact` over the whole `Str9` decoder. -/
abbrev sStr9 : Sign := Sign.ofIsa Silmaril.X86.Str9.isa

/-- **`Σ v1`** over the whole `Str9` decoder. -/
def sSv1 : Sign := ⟨Silmaril.X86.Str9.Instr, ⟨Decoder.ofFn Silmaril.X86.Str9.decode,
  Silmaril.X86.Loose.Sv1, {}⟩⟩

/-- **`Σ v1`** restricted to `Ext9`, over the `Open9` decoder. -/
def sSv1₉ : Sign := ⟨Silmaril.X86.Ext9.Instr, ⟨Decoder.ofFn Silmaril.X86.Open9.decode,
  fun i => Silmaril.X86.Loose.Sv1 (.ext9 i), {}⟩⟩

/-- `Str9.decode` reads what `Open9.decode` reads. -/
theorem str9_decode_of_open9 {bs : List Byte} {i : Silmaril.X86.Ext9.Instr} {n : Nat}
    (h : Silmaril.X86.Open9.decode bs = some (i, n)) :
    Silmaril.X86.Str9.decode bs = some (.ext9 i, n) := by
  simp [Silmaril.X86.Str9.decode, h]

/-- `Open9.decode` reads what `Open.decode` reads. -/
theorem open9_decode_of_open {bs : List Byte} {i : Silmaril.X86.Ext8.Instr} {n : Nat}
    (h : Silmaril.X86.Open.decode bs = some (i, n)) :
    Silmaril.X86.Open9.decode bs = some (.ext8 i, n) := by
  simp [Silmaril.X86.Open9.decode, h]

/-- **ISA inclusion `Ext8 ⊆ Ext9`**: the renaming `.ext8`; the executors agree. -/
def openOpen9 : Sign.Hom sOpen sOpen9 :=
  ⟨.ext8, fun _ he => open9_decode_of_open he,
    fun _ F hF => ⟨_, rfl, by cases hF; exact fun _ _ _ _ h => h⟩⟩

/-- **ISA inclusion `Ext9 ⊆ Str9`**: the renaming `.ext9`; the executors agree. -/
def open9Str9 : Sign.Hom sOpen9 sStr9 :=
  ⟨.ext9, fun _ he => str9_decode_of_open9 he,
    fun _ F hF => ⟨_, rfl, by cases hF; exact fun _ _ _ _ h => h⟩⟩

/-- **`Σ v1 ⟶ Σexact`** over the `Str9` decoder (silmaril's `Exact.sv1Tight`). -/
def sv1Str9 : Sign.Hom sSv1 sStr9 :=
  ⟨id, fun _ he => he, fun i F hF => ⟨_, rfl, Silmaril.X86.Exact.sv1Tight i F hF⟩⟩

/-- **`Σ v1 ⟶ Σexact`** over the `Open9` decoder. -/
def sv1Open9 : Sign.Hom sSv1₉ sOpen9 :=
  ⟨id, fun _ he => he, fun i F hF => ⟨_, rfl, Silmaril.X86.Exact.sv1Tight (.ext9 i) F hF⟩⟩

/-- `Σ v1` over `Open9` into `Σ v1` over `Str9`: the renaming `.ext9`. -/
def sv1₉Sv1 : Sign.Hom sSv1₉ sSv1 :=
  ⟨.ext9, fun _ he => str9_decode_of_open9 he,
    fun _ F hF => ⟨F, hF, FormSpec.Tightens.refl F⟩⟩

/-- The square `Σ v1₉ → Σ v1 → Str9 = Σ v1₉ → Open9 → Str9` commutes. -/
theorem square : sv1₉Sv1.comp sv1Str9 = sv1Open9.comp open9Str9 := Sign.Hom.ext rfl

/-- `Open` as a model of `Ext8`. -/
def openModel : Model Views.mstate sOpen := exactModel Silmaril.X86.Open.isa
/-- **`Open9` as a model of `Ext9`.** -/
def open9Model : Model Views.mstate sOpen9 := exactModel Silmaril.X86.Open9.isa
/-- **`Str9` as a model of `Str9`** (`Σexact`). -/
def str9Model : Model Views.mstate sStr9 := exactModel Silmaril.X86.Str9.isa

/-- `Open9` as a model of `Σ v1` over its decoder (reduct). -/
def open9Sv1Model : Model Views.mstate sSv1₉ := open9Model.reduct sv1Open9
/-- `Str9` as a model of `Σ v1` (reduct). -/
def str9Sv1Model : Model Views.mstate sSv1 := str9Model.reduct sv1Str9
/-- `Str9` as a model of `Ext9` (reduct along the inclusion). -/
def str9Open9Model : Model Views.mstate sOpen9 := str9Model.reduct open9Str9

end Silmaril.X86.BinInstitution
