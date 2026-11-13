module

public import Silmaril.Wasm.Wit.Tool.Source.Defs
public import Silmaril.Wasm.Wit.Tool.Thms
public import Silmaril.Wasm.Wit.Elab.Thms
public import Silmaril.Wasm.Wit.Text.Thms
public import Silmaril.Wasm.Wit.Binary.Thms
public import Silmaril.Wasm.Wit.Project.Ext.Thms

/-!
# The core of `wasm-wit` on WIT source: theorems

The text path `wasm-wit encode PKG.wit --deps DIR` is `encodeText`: parse
(`Text.parse`), elaborate (`Elab.elaborate`, which decides `Wit.Valid` through
`check_iff`), encode (`Binary.encodePackage`). Its guarantees are composed from
`Text.parse_print`, `Elab.elaborate_sound`, `Elab.elaborate_decode`,
`Elab.elaborate_reencode` and `Elab.elaborate_world_projects`:

* `parseText_print`, `encodeText_print`, `elabText_print`: a printable surface
  document, printed as WIT text, is read back as its normal form, so the tool on
  the text computes exactly what it computes on `Text.Document.norm d`;
* `encodeText_sound`: bytes the text path writes come from a valid (gated)
  universe of the parsed documents; the elaborated package is valid with distinct
  names and is named after the main package; the bytes decode to `P.canon`
  (decode ∘ encode = canon);
* `encodeText_reencode`: when `P` is in wit-component's function order, encode ∘
  decode gives the bytes back;
* `encodeText_world_projects`: each world of the package projects back from the
  bytes (`Project.project`, `Bridge.wrappedWorld`);
* `encodeText_print_sound`: the composition of the three for printed documents;
* `checkText_eq`: `check` on a WIT source is `check` on the bytes of `encodeText`.

Worlds in core modules (`embed`):

* `embedPkg_sound`, `embedText_sound`, `embedBytes_sound`: the payload decodes
  (`decodeWorldType`) to the package name, the world name, the normal form of
  the world and the string encoding (`decodeWorldType_encodeWorldType`).

Projection (`project`, now `projectX`):

* `projectBytesX_of_projectBytes`, `projectWatX_of_projectWat`: `projectX` is
  conservative over `project` (`projectX_of_project`); on WAT, when `readIds`
  agrees with `read` (no `$identifiers`, `readIds_of_noIds`).

Not proved: anything about `witAll` (the WIT printer is unverified),
`Binary.embedPayload`/`extractPayload` (core-module framing, tested), and
completeness of the text path (`elaborate_complete` covers the elaborator only).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Tool

open Silmaril.Wasm.Component
open Silmaril.Wasm.Wit.Binary (Env decodePackage decodeEnv encodePackage StringEncoding)

/-- A successful `Except` bind. -/
theorem bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact absurd h (fun h' => by cases h')
  | ok a => exact ⟨a, rfl, h⟩

/-! ## The text path -/

theorem parseText_print {d : Document} (h : Text.printable d = true) (l : String) :
    parseText l (Text.print d) = .ok (Text.Document.norm d) := by
  simp [parseText, Text.parse_print d h]

theorem elabText_print {d : Document} (h : Text.printable d = true) (l : String)
    (deps : List (String × String)) (fs : List Name) :
    elabText (l, Text.print d) deps fs = (parseDeps deps >>= fun ds => elabDocs (Text.Document.norm d) ds fs) := by
  simp only [elabText, parseSource, parseText_print h]
  cases parseDeps deps <;> rfl

theorem encodeText_print {d : Document} (h : Text.printable d = true) (l : String)
    (deps : List (String × String)) (fs : List Name) :
    encodeText (l, Text.print d) deps fs = (parseDeps deps >>= fun ds => encodeDocs (Text.Document.norm d) ds fs) := by
  simp only [encodeText, parseSource, parseText_print h]
  cases parseDeps deps <;> rfl

theorem encodeText_parts {main : String × String} {deps : List (String × String)} {fs : List Name}
    {b : ByteArray} (h : encodeText main deps fs = .ok b) :
    ∃ d ds P env, parseSource main deps = .ok (d, ds) ∧
      Elab.elaborate (sourceUniverse d ds) d.main.name fs = .ok (P, env) ∧
      encodePackage env P = .ok b := by
  obtain ⟨⟨d, ds⟩, hs, h⟩ := bind_eq_ok h
  obtain ⟨⟨P, env⟩, he, hb⟩ := bind_eq_ok h
  exact ⟨d, ds, P, env, hs, he, hb⟩

/-- **The text path is sound**: the bytes `wasm-wit encode PKG.wit` writes are the
encoding of an elaborated package of a valid universe, with distinct names, and
decode to its canonical form. -/
theorem encodeText_sound {main : String × String} {deps : List (String × String)} {fs : List Name}
    {b : ByteArray} (h : encodeText main deps fs = .ok b) :
    ∃ d ds P env, parseSource main deps = .ok (d, ds) ∧
      Elab.elaborate (sourceUniverse d ds) d.main.name fs = .ok (P, env) ∧
      encodePackage env P = .ok b ∧
      Valid (Universe.gate fs (sourceUniverse d ds)) ∧ P.Valid env ∧ P.NamesUnique ∧
      P.name = Elab.pkgName d.main.name ∧ decodePackage b = .ok P.canon := by
  obtain ⟨d, ds, P, env, hs, he, hb⟩ := encodeText_parts h
  have hv := Elab.elaborate_sound he
  exact ⟨d, ds, P, env, hs, he, hb, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, Elab.elaborate_decode he hb⟩

/-- encode ∘ decode is the identity on the bytes of the text path, when the
elaborated package is in wit-component's function order. -/
theorem encodeText_reencode {main : String × String} {deps : List (String × String)} {fs : List Name}
    {b : ByteArray} (h : encodeText main deps fs = .ok b) :
    ∃ d ds P env, parseSource main deps = .ok (d, ds) ∧
      Elab.elaborate (sourceUniverse d ds) d.main.name fs = .ok (P, env) ∧
      (P.canon = P → ∀ q, decodePackage b = .ok q → encodePackage env q = .ok b) := by
  obtain ⟨d, ds, P, env, hs, he, hb⟩ := encodeText_parts h
  exact ⟨d, ds, P, env, hs, he, fun hc _ hq => Elab.elaborate_reencode he hc hb hq⟩

/-- Each world of a WIT source projects back from the bytes of the text path. -/
theorem encodeText_world_projects {main : String × String} {deps : List (String × String)}
    {fs : List Name} {b : ByteArray} (h : encodeText main deps fs = .ok b) :
    ∃ d ds P env, parseSource main deps = .ok (d, ds) ∧
      Elab.elaborate (sourceUniverse d ds) d.main.name fs = .ok (P, env) ∧
      ∃ c its, Binary.parse b = .ok c ∧ (Project.project c).bind (Project.packageItems 0) = some its ∧
        ∀ nw ∈ P.worlds, ∃ ds' d', Binary.encodeWorld (P.env env) nw.2 = .ok ds' ∧ (nw.1, d') ∈ its ∧
          Bridge.wrappedWorld d' = some ds' ∧ Binary.decWorld ds' = .ok nw.2.normalize := by
  obtain ⟨d, ds, P, env, hs, he, hb⟩ := encodeText_parts h
  exact ⟨d, ds, P, env, hs, he, Elab.elaborate_world_projects he hb⟩

/-- For a printed surface document: the text path elaborates its normal form, the
gated universe is valid, and the bytes decode to the canonical elaborated package. -/
theorem encodeText_print_sound {d : Document} (hp : Text.printable d = true) (l : String)
    {deps : List (String × String)} {fs : List Name} {b : ByteArray}
    (h : encodeText (l, Text.print d) deps fs = .ok b) :
    ∃ ds P env, parseDeps deps = .ok ds ∧
      Elab.elaborate (sourceUniverse (Text.Document.norm d) ds) (Text.Document.norm d).main.name fs = .ok (P, env) ∧
      Valid (Universe.gate fs (sourceUniverse (Text.Document.norm d) ds)) ∧
      P.Valid env ∧ P.NamesUnique ∧ decodePackage b = .ok P.canon := by
  obtain ⟨d', ds, P, env, hs, he, -, hv, hP, hu, -, hdec⟩ := encodeText_sound h
  obtain ⟨d'', hd'', hs⟩ := bind_eq_ok hs
  rw [parseText_print hp] at hd''
  cases hd''
  obtain ⟨ds', hds, hs⟩ := bind_eq_ok hs
  cases hs
  exact ⟨_, P, env, hds, he, hv, hP, hu, hdec⟩

/-- `check` on a WIT source is `check` on the bytes of the text path. -/
theorem checkText_eq {main : String × String} {deps : List (String × String)} {fs : List Name}
    {b : ByteArray} {r : Report} (h : checkText main deps fs = .ok (b, r)) :
    encodeText main deps fs = .ok b ∧ check b = .ok r := by
  obtain ⟨b', hb, h⟩ := bind_eq_ok h
  obtain ⟨r', hr, h⟩ := bind_eq_ok h
  cases h
  exact ⟨hb, hr⟩

/-! ## Worlds in core modules -/

theorem findWorld_mem {P : Binary.Package} {n : String} {w : Binary.World}
    (h : findWorld P n = .ok w) : (n, w) ∈ P.worlds := by
  unfold findWorld at h
  split at h
  · rename_i n' w' hf
    cases h
    have hm := List.mem_of_find?_eq_some hf
    have he := List.find?_some hf
    simp only [beq_iff_eq] at he
    subst he
    exact hm
  · cases h

/-- The payload `embed` writes for a valid package decodes to the package name,
the world name, the world's normal form and the string encoding. -/
theorem embedPkg_sound {P : Binary.Package} {env : Env} (hv : P.Valid env) {n : String}
    {se : StringEncoding} {b : ByteArray} (h : embedPkg P env n se = .ok b) :
    ∃ w, (n, w) ∈ P.worlds ∧ Binary.decodeWorldType b = .ok (P.name, n, w.normalize, se) := by
  obtain ⟨w, hw, h⟩ := bind_eq_ok h
  have hm := findWorld_mem hw
  exact ⟨w, hm, Binary.decodeWorldType_encodeWorldType hv.2.2.2.1 (hv.2.2.1 _ hm)
    (hv.2.2.2.2 _ hm) h⟩

/-- `embed PKG.wit --world W`: the payload decodes to world `W` of the elaborated
package of a valid universe. -/
theorem embedText_sound {main : String × String} {deps : List (String × String)} {fs : List Name}
    {n : String} {se : StringEncoding} {b : ByteArray} (h : embedText main deps fs n se = .ok b) :
    ∃ P env w, elabText main deps fs = .ok (P, env) ∧ (n, w) ∈ P.worlds ∧
      Binary.decodeWorldType b = .ok (P.name, n, w.normalize, se) := by
  obtain ⟨⟨P, env⟩, he, h⟩ := bind_eq_ok h
  obtain ⟨_, -, he'⟩ := bind_eq_ok he
  have hv : P.Valid env := (Elab.elaborate_sound he').2.1
  obtain ⟨w, hm, hd⟩ := embedPkg_sound hv h
  exact ⟨P, env, w, he, hm, hd⟩

/-- `embed PKG.wasm --world W` on a binary whose package is valid in the
environment it shows (what `check` reports as `valid`). -/
theorem embedBytes_sound {b : ByteArray} {d : Decoded} (hd : decode b = .ok d)
    (hv : d.pkg.Valid d.env) {n : String} {se : StringEncoding} {pl : ByteArray}
    (h : embedBytes b n se = .ok pl) :
    ∃ w, (n, w) ∈ d.pkg.worlds ∧ Binary.decodeWorldType pl = .ok (d.pkg.name, n, w.normalize, se) := by
  obtain ⟨d', hd', h⟩ := bind_eq_ok h
  rw [hd] at hd'
  cases hd'
  exact embedPkg_sound hv h

/-! ## Projection -/

theorem projectBytesX_of_projectBytes {b : ByteArray} {w : Project.WorldType}
    (h : projectBytes b = .ok w) : projectBytesX b = .ok w := by
  unfold projectBytes at h
  unfold projectBytesX
  cases hc : Binary.parse b with
  | error e => simp only [hc] at h; cases h
  | ok c =>
    cases hp : Project.project c with
    | none => simp only [hc, hp] at h; cases h
    | some w' =>
      simp only [hc, hp] at h
      cases h
      simp only [Project.projectX_of_project hp]

theorem projectWatX_of_projectWat {t : String} (hr : Wat.readIds t = Wat.read t)
    {w : Project.WorldType} (h : projectWat t = .ok w) : projectWatX t = .ok w := by
  unfold projectWat at h
  unfold projectWatX
  rw [hr]
  cases hc : Wat.read t with
  | none => simp only [hc] at h; cases h
  | some c =>
    cases hp : Project.project c with
    | none => simp only [hc, hp] at h; cases h
    | some w' =>
      simp only [hc, hp] at h
      cases h
      simp only [Project.projectX_of_project hp]

end Silmaril.Wasm.Wit.Tool
