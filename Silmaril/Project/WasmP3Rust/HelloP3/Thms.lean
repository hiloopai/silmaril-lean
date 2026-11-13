module

public import Silmaril.Project.WasmP3Rust.HelloP3.Defs
public import Silmaril.Project.WasmP3Rust.Hello.Component.Thms
public import Silmaril.Project.WasmP3Rust.Hello.File.Thms
public import Silmaril.Wasm.Component.BinaryP3.Thms
public import Silmaril.Wasm.Component.Chunked.Thms
public import Silmaril.Project.WasmP3Rust.TasksP3.Defs

/-!
# `hello.wasm` parses under the async-aware grammar

**PROVED** (kernel): `parse_eq : BinaryP3.parse (arrOf Hello.File.bytes) = .ok ast`. The encoder writes each
section from its AST (`sec_N`: the old sections through `RoundTrip.section_ofV0` and the
certificates `Hello.secN_eq`; the core modules by their framing; the `canon` sections with
async built-ins by new certificates), the encodings of consecutive sections concatenate to
the file (`Chunked.slice_append`), and the round trip `BinaryP3.parse_encode` turns the
encoding into the parse.

A Silmaril addition.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Silmaril.Project.WasmP3Rust.HelloP3

open Silmaril.Wasm.Component.BinaryP3 (Section Ast Canon)
open Silmaril.Wasm.Component.Chunked

/-- A core module section is the framing of its bytes. -/
theorem section_coreModule (l : List UInt8) :
    Silmaril.Wasm.Component.BinaryP3.Encode.section_ (.coreModule (arr l)) = frameEnc (1, l) := by
  rw [Silmaril.Wasm.Component.BinaryP3.Encode.section_]
  show (Silmaril.Parse.ByteParse.Enc.sized l).bind (fun s => some (0x01 :: s)) =
    (fun x => 1 :: x) <$> Silmaril.Parse.ByteParse.Enc.sized l
  cases Silmaril.Parse.ByteParse.Enc.sized l <;> rfl

theorem sec_8 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec8) =
    some (slice Hello.File.bytes 8 62) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec8_eq

theorem sec_62 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec62) =
    some (slice Hello.File.bytes 62 89) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec62_eq

theorem sec_89 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec89) =
    some (slice Hello.File.bytes 89 106) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec89_eq

theorem sec_106 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec106) =
    some (slice Hello.File.bytes 106 132) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec106_eq

theorem sec_132 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec132) =
    some (slice Hello.File.bytes 132 159) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec132_eq

theorem sec_159 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec159) =
    some (slice Hello.File.bytes 159 176) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec159_eq

theorem sec_176 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec176) =
    some (slice Hello.File.bytes 176 247) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec176_eq

theorem sec_247 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec247) =
    some (slice Hello.File.bytes 247 275) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec247_eq

theorem sec_275 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (.coreModule (arr (slice Hello.File.bytes 279 39729))) =
    some (slice Hello.File.bytes 275 39729) :=
  (section_coreModule _).trans <|
  frameEnc_of Hello.File.bytes (id := 1) (s := 275) (x := 279) (e := 39729) (by simp only [Hello.File.bytes, slice_decode]; decide +kernel)
    (by simp only [Hello.File.bytes, slice_decode]; decide +kernel) (by decide) (by decide)
    (le_length Hello.File.bytes_length (by decide))

theorem sec_39729 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (.coreModule (arr (slice Hello.File.bytes 39732 39921))) =
    some (slice Hello.File.bytes 39729 39921) :=
  (section_coreModule _).trans <|
  frameEnc_of Hello.File.bytes (id := 1) (s := 39729) (x := 39732) (e := 39921) (by simp only [Hello.File.bytes, slice_decode]; decide +kernel)
    (by simp only [Hello.File.bytes, slice_decode]; decide +kernel) (by decide) (by decide)
    (le_length Hello.File.bytes_length (by decide))

theorem sec_39921 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (.coreModule (arr (slice Hello.File.bytes 39924 40053))) =
    some (slice Hello.File.bytes 39921 40053) :=
  (section_coreModule _).trans <|
  frameEnc_of Hello.File.bytes (id := 1) (s := 39921) (x := 39924) (e := 40053) (by simp only [Hello.File.bytes, slice_decode]; decide +kernel)
    (by simp only [Hello.File.bytes, slice_decode]; decide +kernel) (by decide) (by decide)
    (le_length Hello.File.bytes_length (by decide))

theorem sec_40053 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec40053) =
    some (slice Hello.File.bytes 40053 40059) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec40053_eq

theorem sec_40059 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ c40059 = some (slice Hello.File.bytes 40059 40071) := by
  simp only [c40059, Hello.File.bytes, slice_decode]; decide +kernel

theorem sec_40071 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec40071) =
    some (slice Hello.File.bytes 40071 40080) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec40071_eq

theorem sec_40080 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec40080) =
    some (slice Hello.File.bytes 40080 40204) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec40080_eq

theorem sec_40204 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ c40204 = some (slice Hello.File.bytes 40204 40208) := by
  simp only [c40204, Hello.File.bytes, slice_decode]; decide +kernel

theorem sec_40208 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec40208) =
    some (slice Hello.File.bytes 40208 40229) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec40208_eq

theorem sec_40229 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec40229) =
    some (slice Hello.File.bytes 40229 40235) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec40229_eq

theorem sec_40235 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ c40235 = some (slice Hello.File.bytes 40235 40240) := by
  simp only [c40235, Hello.File.bytes, slice_decode]; decide +kernel

theorem sec_40240 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec40240) =
    some (slice Hello.File.bytes 40240 40269) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec40240_eq

theorem sec_40269 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec40269) =
    some (slice Hello.File.bytes 40269 40279) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec40269_eq

theorem sec_40279 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ c40279 = some (slice Hello.File.bytes 40279 40294) := by
  simp only [c40279, Hello.File.bytes, slice_decode]; decide +kernel

theorem sec_40294 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec40294) =
    some (slice Hello.File.bytes 40294 40309) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec40294_eq

theorem sec_40309 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ c40309 = some (slice Hello.File.bytes 40309 40322) := by
  simp only [c40309, Hello.File.bytes, slice_decode]; decide +kernel

theorem sec_40322 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec40322) =
    some (slice Hello.File.bytes 40322 40908) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec40322_eq

theorem sec_40908 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec40908) =
    some (slice Hello.File.bytes 40908 40931) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec40908_eq

theorem sec_40931 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec40931) =
    some (slice Hello.File.bytes 40931 40938) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec40931_eq

theorem sec_40938 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec40938) =
    some (slice Hello.File.bytes 40938 40962) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec40938_eq

theorem sec_40962 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec40962) =
    some (slice Hello.File.bytes 40962 40968) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec40962_eq

theorem sec_40968 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ c40968 = some (slice Hello.File.bytes 40968 40975) := by
  simp only [c40968, Hello.File.bytes, slice_decode]; decide +kernel

theorem sec_40975 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec40975) =
    some (slice Hello.File.bytes 40975 41102) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec40975_eq

theorem sec_41102 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec41102) =
    some (slice Hello.File.bytes 41102 41129) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec41102_eq

theorem sec_41129 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ c41129 = some (slice Hello.File.bytes 41129 41135) := by
  simp only [c41129, Hello.File.bytes, slice_decode]; decide +kernel

theorem sec_41135 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec41135) =
    some (slice Hello.File.bytes 41135 41155) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec41135_eq

theorem sec_41155 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ c41155 = some (slice Hello.File.bytes 41155 41182) := by
  simp only [c41155, Hello.File.bytes, slice_decode]; decide +kernel

theorem sec_41182 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec41182) =
    some (slice Hello.File.bytes 41182 41224) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec41182_eq

theorem sec_41224 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec41224) =
    some (slice Hello.File.bytes 41224 41231) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec41224_eq

theorem sec_41231 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec41231) =
    some (slice Hello.File.bytes 41231 41322) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec41231_eq

theorem sec_41322 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec41322) =
    some (slice Hello.File.bytes 41322 41333) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec41322_eq

theorem sec_41333 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec41333) =
    some (slice Hello.File.bytes 41333 41398) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec41333_eq

theorem sec_41398 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec41398) =
    some (slice Hello.File.bytes 41398 41422) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec41398_eq

theorem sec_41422 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec41422) =
    some (slice Hello.File.bytes 41422 41448) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec41422_eq

theorem sec_41448 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec41448) =
    some (slice Hello.File.bytes 41448 42865) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec41448_eq

theorem sec_42865 : Silmaril.Wasm.Component.BinaryP3.Encode.section_ (Section.ofV0 Hello.sec42865) =
    some (slice Hello.File.bytes 42865 42914) := by
  rw [Silmaril.Wasm.Component.BinaryP3.RoundTrip.section_ofV0]; exact Hello.sec42865_eq

/-- Consecutive section encodings concatenate. -/
theorem sections_cons {sec : Section} {ss : List Section} {a b c : Nat}
    (h₁ : Silmaril.Wasm.Component.BinaryP3.Encode.section_ sec = some (slice Hello.File.bytes a b))
    (h₂ : Silmaril.Wasm.Component.BinaryP3.Encode.sections ss = some (slice Hello.File.bytes b c))
    (hab : a ≤ b) (hbc : b ≤ c) :
    Silmaril.Wasm.Component.BinaryP3.Encode.sections (sec :: ss) = some (slice Hello.File.bytes a c) := by
  simp only [Silmaril.Wasm.Component.BinaryP3.Encode.sections, h₁, h₂, Option.bind_eq_bind,
    Option.bind_some, ← slice_append Hello.File.bytes hab hbc]
  rfl

theorem sections_nil :
    Silmaril.Wasm.Component.BinaryP3.Encode.sections [] = some (slice Hello.File.bytes 42914 42914) := by
  rw [slice_self]; rfl

/-- **The sections encode to the file after the preamble.** -/
theorem sections_eq :
    Silmaril.Wasm.Component.BinaryP3.Encode.sections sections = some (slice Hello.File.bytes 8 42914) := by
  unfold sections
  exact (sections_cons sec_8 (sections_cons sec_62 (sections_cons sec_89 (sections_cons sec_106 (sections_cons sec_132 (sections_cons sec_159 (sections_cons sec_176 (sections_cons sec_247 (sections_cons sec_275 (sections_cons sec_39729 (sections_cons sec_39921 (sections_cons sec_40053 (sections_cons sec_40059 (sections_cons sec_40071 (sections_cons sec_40080 (sections_cons sec_40204 (sections_cons sec_40208 (sections_cons sec_40229 (sections_cons sec_40235 (sections_cons sec_40240 (sections_cons sec_40269 (sections_cons sec_40279 (sections_cons sec_40294 (sections_cons sec_40309 (sections_cons sec_40322 (sections_cons sec_40908 (sections_cons sec_40931 (sections_cons sec_40938 (sections_cons sec_40962 (sections_cons sec_40968 (sections_cons sec_40975 (sections_cons sec_41102 (sections_cons sec_41129 (sections_cons sec_41135 (sections_cons sec_41155 (sections_cons sec_41182 (sections_cons sec_41224 (sections_cons sec_41231 (sections_cons sec_41322 (sections_cons sec_41333 (sections_cons sec_41398 (sections_cons sec_41422 (sections_cons sec_41448 (sections_cons sec_42865 sections_nil (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide))

theorem preamble_eq : slice Hello.File.bytes 0 8 = Silmaril.Wasm.Component.Binary.preambleBytes := by
  simp only [Hello.File.bytes, slice_decode]; decide +kernel

/-- **The encoder writes the file.** -/
theorem encode_eq : Silmaril.Wasm.Component.BinaryP3.encode ast = some (arrOf Hello.File.bytes) := by
  have hb : slice Hello.File.bytes 0 8 ++ slice Hello.File.bytes 8 42914 = Hello.File.bytes := by
    rw [slice_append Hello.File.bytes (by decide) (by decide)]
    simp only [slice, List.drop_zero, Nat.sub_zero, ← Hello.File.bytes_length, List.take_length]
  have he : Silmaril.Wasm.Component.BinaryP3.Encode.ast ast = some Hello.File.bytes := by
    simp only [ast, Silmaril.Wasm.Component.BinaryP3.Encode.ast, sections_eq, ← preamble_eq,
      Option.bind_eq_bind, Option.bind_some, hb]
    rfl
  simp only [Silmaril.Wasm.Component.BinaryP3.encode, he, Option.map_some, arrOf,
    Option.some.injEq, ByteArray.mk.injEq]

/-- **`hello.wasm` parses** under the async-aware grammar, to `ast`. -/
theorem parse_eq : Silmaril.Wasm.Component.BinaryP3.parse (arrOf Hello.File.bytes) = .ok ast :=
  Silmaril.Wasm.Component.BinaryP3.parse_encode encode_eq

/-- `Task.parsesP3` for `hello.wasm`. -/
theorem parses : Task.parsesP3 Hello.File.bytes := ⟨ast, parse_eq⟩

end Silmaril.Project.WasmP3Rust.HelloP3

end
