module

public import Silmaril.Wasm.Wac.SpliceX.Defs
public import Silmaril.Wasm.Wac.Splice.Thms
public import Silmaril.Wasm.Component.BinaryAsync.Thms

/-!
# WAC: splicing package bytes with the async built-ins is embedding their extended ASTs

* `splice_eq_embedX`: under `AgreesX tbl raw`, the spliced bytes are `encodeX (embedX tbl c)`;
* `parseX_splice`: they parse back (`parseX`) to `embedX tbl c`;
* `embedX_ofAst`, `agreesX_ofAst`: on base packages this is `Embed.embed` and `Splice.Agrees`;
* `erase_embedX`: erasing the built-ins of the result is `Embed.embed` of the erased packages;
  `graph_embedX`, `isProfile_embedX`: it lowers to the graph of `c`, in the profile when `c` is;
* `canonTable_agrees`: the tool's check `canonTable` establishes `AgreesX`;
* `pkgsOf_embedX`: the components of the result, in index order, are the packages of `c`'s
  package imports looked up in `tbl` (and `c`'s own definitions).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.SpliceX

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.BinaryAsync

/-! ## Splicing -/

theorem rawX_none {tbl : PkgTableX} {raw : Splice.RawTable} (h : AgreesX tbl raw) {n : String}
    (ht : tbl.lookup n = none) : raw.lookup n = none := by
  have hs := (h n).2
  rw [ht] at hs
  cases hr : raw.lookup n with
  | none => rfl
  | some r => rw [hr] at hs; simp at hs

theorem rawX_some {tbl : PkgTableX} {raw : Splice.RawTable} (h : AgreesX tbl raw) {n : String}
    {a : AstX} (ht : tbl.lookup n = some a) :
    ∃ r, raw.lookup n = some r ∧ EncodeX.ast a = some r.data.toList := by
  have ⟨he, hs⟩ := h n
  rw [ht] at he hs
  cases hr : raw.lookup n with
  | none => rw [hr] at hs; simp at hs
  | some r => rw [hr] at he; exact ⟨r, rfl, he⟩

theorem rawSec_impX {tbl : PkgTableX} {raw : Splice.RawTable} (h : AgreesX tbl raw)
    (n : ExternName) (t : Nat) : Splice.rawSec raw (.imports [⟨n, .component t⟩]) =
      EncodeX.section_ (embedSecX tbl (.imports [⟨n, .component t⟩])) := by
  simp only [Splice.rawSec, embedSecX]
  cases ht : tbl.lookup n.name with
  | none => simp only [rawX_none h ht, encodeX_section_ofSection]
  | some a =>
    obtain ⟨r, hr, he⟩ := rawX_some h ht
    simp only [hr, EncodeX.section_, he]
    rfl

/-- A section that is not a single component import. -/
def NotPkgImport (s : Section) : Prop := ¬ ∃ n t, s = .imports [⟨n, .component t⟩]

theorem rawSec_other {raw : Splice.RawTable} {s : Section} (hi : NotPkgImport s) :
    Splice.rawSec raw s = Encode.section_ s := by
  unfold Splice.rawSec
  split
  · exact absurd ⟨_, _, rfl⟩ hi
  · rfl

theorem embedSecX_other {tbl : PkgTableX} {s : Section} (hi : NotPkgImport s) :
    embedSecX tbl s = SectionX.ofSection s := by
  unfold embedSecX
  split
  · exact absurd ⟨_, _, rfl⟩ hi
  · rfl

theorem rawSec_eqX {tbl : PkgTableX} {raw : Splice.RawTable} (h : AgreesX tbl raw) (s : Section) :
    Splice.rawSec raw s = EncodeX.section_ (embedSecX tbl s) := by
  by_cases hi : ∃ n t, s = .imports [⟨n, .component t⟩]
  · obtain ⟨n, t, rfl⟩ := hi
    exact rawSec_impX h n t
  · rw [rawSec_other hi, embedSecX_other hi, encodeX_section_ofSection]

theorem rawSecs_eqX {tbl : PkgTableX} {raw : Splice.RawTable} (h : AgreesX tbl raw) :
    ∀ ss : List Section, Splice.rawSecs raw ss = EncodeX.sections (ss.map (embedSecX tbl))
  | [] => rfl
  | s :: ss => by
    simp only [Splice.rawSecs, List.map_cons, EncodeX.sections, rawSec_eqX h, rawSecs_eqX h ss]

/-- **Splicing the bytes is encoding the embedded extended composition.** -/
theorem splice_eq_embedX {tbl : PkgTableX} {raw : Splice.RawTable} (h : AgreesX tbl raw)
    (c : Ast) : Splice.splice raw c = encodeX (embedX tbl c) := by
  cases c with
  | mk ss =>
    simp only [Splice.splice, encodeX, embedX, Ast.sections, EncodeX.ast, rawSecs_eqX h]
    cases EncodeX.sections (ss.map (embedSecX tbl)) <;> rfl

/-- **The spliced bytes parse back** (with the async built-ins) to the embedded composition. -/
theorem parseX_splice {tbl : PkgTableX} {raw : Splice.RawTable} (h : AgreesX tbl raw) {c : Ast}
    {b : ByteArray} (hb : Splice.splice raw c = some b) : parseX b = .ok (embedX tbl c) :=
  parseX_encodeX (by rw [← splice_eq_embedX h]; exact hb)

/-! ## Base packages -/

theorem lookup_map_snd {α β : Type} (f : α → β) (n : String) :
    ∀ l : List (String × α), (l.map fun p => (p.1, f p.2)).lookup n = (l.lookup n).map f
  | [] => rfl
  | (k, a) :: l => by
    simp only [List.map_cons, List.lookup_cons]
    cases n == k
    · exact lookup_map_snd f n l
    · rfl

/-- A table of base packages as extended ones. -/
def ofTable (tbl : Embed.PkgTable) : PkgTableX := tbl.map fun p => (p.1, AstX.ofAst p.2)

theorem embedSecX_ofTable (tbl : Embed.PkgTable) (s : Section) :
    embedSecX (ofTable tbl) s = SectionX.ofSection (Embed.embedSec tbl s) := by
  by_cases hi : ∃ n t, s = .imports [⟨n, .component t⟩]
  · obtain ⟨n, t, rfl⟩ := hi
    simp only [embedSecX, Embed.embedSec, ofTable, lookup_map_snd]
    cases tbl.lookup n.name with
    | none => rfl
    | some d => simp only [Option.map_some, SectionX.ofSection]
  · rw [embedSecX_other hi]
    congr 1
    unfold Embed.embedSec
    split
    · exact absurd ⟨_, _, rfl⟩ hi
    · rfl

theorem ofSections_map : ∀ ss : List Section, SectionX.ofSections ss = ss.map SectionX.ofSection
  | [] => by simp only [SectionX.ofSections, List.map_nil]
  | s :: ss => by simp only [SectionX.ofSections, List.map_cons, ofSections_map ss]

/-- On base packages, extended embedding is base embedding. -/
theorem embedX_ofTable (tbl : Embed.PkgTable) (c : Ast) :
    embedX (ofTable tbl) c = AstX.ofAst (Embed.embed tbl c) := by
  cases c with
  | mk ss =>
    simp only [embedX, Embed.embed, Ast.sections, AstX.ofAst, ofSections_map, List.map_map]
    congr 1
    exact List.map_congr_left fun s _ => embedSecX_ofTable tbl s

/-- On base packages, `AgreesX` is `Splice.Agrees`. -/
theorem agreesX_ofTable {tbl : Embed.PkgTable} {raw : Splice.RawTable} (h : Splice.Agrees tbl raw) :
    AgreesX (ofTable tbl) raw := by
  intro n
  have ⟨he, hs⟩ := h n
  simp only [ofTable, lookup_map_snd, Option.isSome_map]
  refine ⟨?_, hs⟩
  rw [← he]
  cases tbl.lookup n with
  | none => rfl
  | some a => simp only [Option.map_some, Option.bind_some, encodeXAst_ofAst]

/-! ## Erasure, profile and graph -/

/-- The packages with their built-ins erased. -/
def eraseTable (tbl : PkgTableX) : Embed.PkgTable := tbl.map fun p => (p.1, p.2.erase)

theorem eraseAll_map : ∀ ss : List SectionX, SectionX.eraseAll ss = ss.map SectionX.erase
  | [] => by simp only [SectionX.eraseAll, List.map_nil]
  | s :: ss => by simp only [SectionX.eraseAll, List.map_cons, eraseAll_map ss]

theorem erase_embedSecX (tbl : PkgTableX) (s : Section) :
    (embedSecX tbl s).erase = Embed.embedSec (eraseTable tbl) s := by
  by_cases hi : ∃ n t, s = .imports [⟨n, .component t⟩]
  · obtain ⟨n, t, rfl⟩ := hi
    simp only [embedSecX, Embed.embedSec, eraseTable, lookup_map_snd]
    cases tbl.lookup n.name with
    | none => simp only [Option.map_none, eraseSec_ofSection]
    | some d => simp only [Option.map_some, SectionX.erase]
  · rw [embedSecX_other hi, eraseSec_ofSection]
    unfold Embed.embedSec
    split
    · exact absurd ⟨_, _, rfl⟩ hi
    · rfl

/-- **Erasing the built-ins** of the embedded composition is base embedding of the erased
packages. -/
theorem erase_embedX (tbl : PkgTableX) (c : Ast) :
    (embedX tbl c).erase = Embed.embed (eraseTable tbl) c := by
  cases c with
  | mk ss =>
    simp only [embedX, Embed.embed, Ast.sections, AstX.erase, eraseAll_map, List.map_map]
    congr 1
    exact List.map_congr_left fun s _ => erase_embedSecX tbl s

/-- The embedded composition is in the profile (after erasure) exactly when `c` is. -/
theorem isProfile_embedX (tbl : PkgTableX) (c : Ast) :
    isProfile (embedX tbl c).erase = isProfile c := by
  rw [erase_embedX, Embed.isProfile_embed]

/-- **The embedded composition lowers to the graph of `c`.** -/
theorem graph_embedX (S : Nat → PkgSig) (tbl : PkgTableX) (c : Ast) :
    Wac.Lower.graph S (embedX tbl c).erase = Wac.Lower.graph S c := by
  rw [erase_embedX, Embed.graph_embed]

/-! ## The tool's check -/

theorem canonPkg_some {p : String × ByteArray} {q : String × AstX} (h : canonPkg p = some q) :
    q.1 = p.1 ∧ EncodeX.ast q.2 = some p.2.data.toList := by
  unfold canonPkg at h
  split at h
  · rename_i a _
    split at h
    · rename_i he; cases h; exact ⟨rfl, he⟩
    · cases h
  · cases h

theorem forall₂_of_mapM :
    ∀ {raw : Splice.RawTable} {tbl : PkgTableX}, raw.mapM canonPkg = some tbl →
      List.Forall₂ (fun p q => q.1 = p.1 ∧ EncodeX.ast q.2 = some p.2.data.toList) raw tbl
  | [], tbl, h => by
    simp only [List.mapM_nil] at h
    cases h; exact .nil
  | p :: raw, tbl, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, qs, hqs, he⟩ := h
    cases he
    exact .cons (canonPkg_some hq) (forall₂_of_mapM hqs)

theorem agreesX_of_forall₂ {n : String} :
    ∀ {raw : Splice.RawTable} {tbl : PkgTableX},
      List.Forall₂ (fun p q => q.1 = p.1 ∧ EncodeX.ast q.2 = some p.2.data.toList) raw tbl →
      (tbl.lookup n).bind EncodeX.ast = (raw.lookup n).map (·.data.toList) ∧
        ((tbl.lookup n).isSome ↔ (raw.lookup n).isSome)
  | [], [], .nil => by simp
  | (k, r) :: raw, (k', a) :: tbl, .cons ⟨hk, he⟩ hr => by
    have hk' : k' = k := hk
    subst hk'
    simp only [List.lookup_cons]
    cases n == k'
    · exact agreesX_of_forall₂ hr
    · exact ⟨by simpa using he, by simp⟩

/-- **The tool's check establishes the hypothesis of `parseX_splice`.** -/
theorem canonTable_agrees {raw : Splice.RawTable} {tbl : PkgTableX} (h : canonTable raw = some tbl) :
    AgreesX tbl raw :=
  fun _ => agreesX_of_forall₂ (forall₂_of_mapM h)

/-! ## The components of the embedded composition -/

theorem secPkgsX_ofSection (tbl : PkgTableX) (s : Section) :
    secPkgsX (SectionX.ofSection s) = (otherSrcs s).map (PkgSrc.resolve tbl) := by
  cases s with
  | component d => simp only [SectionX.ofSection, secPkgsX, otherSrcs, List.map_cons,
      List.map_nil, PkgSrc.resolve]
  | imports xs =>
    simp only [SectionX.ofSection, secPkgsX, otherSrcs, List.map_filterMap]
    congr 1
    funext i
    cases i.desc <;> rfl
  | aliases xs =>
    simp only [SectionX.ofSection, secPkgsX, otherSrcs, List.map_filterMap]
    congr 1
    funext a
    split <;> rfl
  | _ => simp only [SectionX.ofSection, secPkgsX, otherSrcs, List.map_nil]

theorem secPkgsX_embedSecX (tbl : PkgTableX) (s : Section) :
    secPkgsX (embedSecX tbl s) = (secSrcs s).map (PkgSrc.resolve tbl) := by
  by_cases hi : ∃ n t, s = .imports [⟨n, .component t⟩]
  · obtain ⟨n, t, rfl⟩ := hi
    simp only [embedSecX, secSrcs, List.map_cons, List.map_nil, PkgSrc.resolve]
    cases tbl.lookup n.name with
    | none => rfl
    | some d => rfl
  · have hs : secSrcs s = otherSrcs s := by
      unfold secSrcs
      split
      · exact absurd ⟨_, _, rfl⟩ hi
      · rfl
    rw [embedSecX_other hi, hs, secPkgsX_ofSection]

/-- **The components of the embedded composition**, in index order: the package of each
package import of `c` (looked up in `tbl`), and `c`'s own definitions. -/
theorem pkgsOf_embedX (tbl : PkgTableX) (c : Ast) :
    pkgsOf (embedX tbl c) = (pkgSrcs c).map (PkgSrc.resolve tbl) := by
  cases c with
  | mk ss =>
    simp only [pkgsOf, embedX, AstX.sections, pkgSrcs, Ast.sections, List.flatMap_map,
      List.map_flatMap]
    exact List.flatMap_congr fun s _ => secPkgsX_embedSecX tbl s

end Silmaril.Wasm.Wac.SpliceX
