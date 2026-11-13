module

public import Silmaril.Wasm.JcoTool.KCoreEmit.Defs
public import Silmaril.Wasm.JcoTool.KCore.Thms
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound
public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntaxSound
public import Silmaril.Wasm.Binary.Core.Modules
public import Silmaril.Wasm.Text.Core.Modules

/-!
# The generated stream modules: the bytes and the text denote `toModule`

* `wasmOf_encodes`: the bytes `wasm-jco kcore … -o` writes encode `toModule P name` in the
  Core 3.0 binary grammar (silmaril's `encodeModule?_sound`).
* `watOf_encodes`: silmaril's checked printer's text denotes `toModule P name` in the Core
  3.0 text grammar (`moduleSyntax?_sound`, `renderWatDocument?_sound`).
* `watChecked_encodes`: an accepted text of the original printer (`Prog.wat`) denotes
  `toModule P name` in the text grammar (silmaril's sound parser, the encoder's soundness
  and the functionality of the binary grammar).
* `wasm_wat_same`: the text and the bytes denote one module: whatever module the text
  denotes, the bytes encode it.
* `kcore_new`: `wasm-jco new` on the bytes of `wasm-jco kcore … -o`: the core module it wraps
  (decoded by silmaril's verified decoder) is `toModule (gen k N) name`, and
  `KCore.kcore_stream_semantics` holds (the stream semantics in the model of the fragment).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KCoreEmit

open Silmaril.Wasm
open Silmaril.Wasm.JcoTool.KCore

/-- **The bytes encode the generated module.** -/
theorem wasmOf_encodes {P : Prog} {name : String} {b : ByteArray}
    (h : wasmOf P name = .ok b) : Binary.Core.Encodes b.data.toList (toModule P name) := by
  unfold wasmOf at h
  cases he : Silmaril.Wasm.Binaryen.Exe.encodeModule? (toModule P name) with
  | error e => simp [he] at h
  | ok bs =>
    simp only [he, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    simpa using Silmaril.Wasm.Binaryen.Exe.encodeModule?_sound he

/-- **The checked printer's text denotes the generated module.** -/
theorem watOf_encodes {P : Prog} {name : String} {t : String}
    (h : watOf P name = .ok t) : Text.Core.Encodes t (toModule P name) := by
  unfold watOf at h
  cases hd : Silmaril.Wasm.Binaryen.Toolkit.Wat.moduleSyntax? (toModule P name) with
  | none => simp [hd] at h
  | some x =>
    cases hr : Silmaril.Wasm.Binaryen.Toolkit.renderWatDocument? x with
    | none => simp [hd, hr] at h
    | some t' =>
      simp only [hd, hr, Except.ok.injEq] at h
      subst h
      exact ⟨x, Silmaril.Wasm.Binaryen.Toolkit.renderWatDocument?_sound hr,
        Silmaril.Wasm.Binaryen.Toolkit.Wat.moduleSyntax?_sound hd⟩

/-- Silmaril's parser is sound for the text grammar. -/
theorem parseWat_sound {t : String} {m : Module} (h : parseWat t = some m) :
    Text.Core.Encodes t m := by
  unfold parseWat at h
  cases hx : Silmaril.Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 t with
  | none => simp [hx] at h
  | some x =>
    simp only [hx, Option.bind_eq_bind, Option.bind_some] at h
    exact ⟨x, Silmaril.Formats.SExpEncoding.Wat.sexpWat_of_fullExec hx,
      Silmaril.Wasm.Binaryen.Toolkit.Wat.parseSupported?_sound h⟩

/-- What an accepted check consists of. -/
theorem watChecked_inv {P : Prog} {name : String} {t : String}
    (h : watChecked P name = .ok t) :
    ∃ b m bs, wasmOf P name = .ok b ∧ parseWat (P.wat name) = some m ∧
      Silmaril.Wasm.Binaryen.Exe.encodeModule? m = .ok bs ∧ bs = b.data.toList ∧
      t = P.wat name := by
  unfold watChecked at h
  cases hb : wasmOf P name with
  | error e => simp [hb, bind, Except.bind] at h
  | ok b =>
    cases hp : parseWat (P.wat name) with
    | none => simp [hb, hp, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    | some m =>
      cases he : Silmaril.Wasm.Binaryen.Exe.encodeModule? m with
      | error e => simp [hb, hp, he, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      | ok bs =>
        by_cases hq : (bs == b.data.toList) = true
        · simp only [hb, hp, he, hq, bind, Except.bind, ite_true, pure, Except.pure,
            Except.ok.injEq] at h
          exact ⟨b, m, bs, rfl, rfl, he, eq_of_beq hq, h.symm⟩
        · simp [hb, hp, he, hq, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- **The original printer, checked**: an accepted text is `Prog.wat P name` and denotes the
generated module in the Core 3.0 text grammar. -/
theorem watChecked_encodes {P : Prog} {name : String} {t : String}
    (h : watChecked P name = .ok t) : t = P.wat name ∧ Text.Core.Encodes t (toModule P name) := by
  obtain ⟨b, m, bs, hb, hp, he, hbs, ht⟩ := watChecked_inv h
  have h1 : Binary.Core.Encodes b.data.toList m :=
    hbs ▸ Silmaril.Wasm.Binaryen.Exe.encodeModule?_sound he
  have h2 : Binary.Core.Encodes b.data.toList (toModule P name) := wasmOf_encodes hb
  have hm : m = toModule P name := Binary.Core.functional h1 h2
  have hw : Text.Core.Encodes (P.wat name) m := parseWat_sound hp
  exact ⟨ht, ht ▸ hm ▸ hw⟩

/-- **The text and the bytes denote one module**: the module `toModule P name`, which the
bytes encode and the text (either printer's) denotes. -/
theorem wasm_wat_same {P : Prog} {name : String} {b : ByteArray} {t : String}
    (hb : wasmOf P name = .ok b) (ht : watOf P name = .ok t ∨ watChecked P name = .ok t) :
    ∃ m, Binary.Core.Encodes b.data.toList m ∧ Text.Core.Encodes t m ∧ m = toModule P name := by
  refine ⟨toModule P name, wasmOf_encodes hb, ?_, rfl⟩
  rcases ht with ht | ht
  · exact watOf_encodes ht
  · exact (watChecked_encodes ht).2

/-- **The tool's bytes, for the generator**: `wasm-jco kcore NAME KERNEL N -o OUT` writes the
encoding of `toModule (gen k N) NAME`, the generated program `gen k N` as a Core module. -/
theorem kcore_bytes {k : Silmaril.Wasm.Component.Streams.Kernel.KM} {N : Nat} {name : String}
    {b : ByteArray} (h : wasmOf (gen k N) name = .ok b) :
    Binary.Core.Encodes b.data.toList (toModule (gen k N) name) :=
  wasmOf_encodes h

/-- Whatever silmaril's decoder reads from the bytes is the generated module. -/
theorem wasmOf_decode {P : Prog} {name : String} {b : ByteArray} (h : wasmOf P name = .ok b)
    {m : Module} (hd : Binary.Core.decode? b = some m) : m = toModule P name :=
  Binary.Core.functional (Binary.Core.decode?_sound hd) (wasmOf_encodes h)

/-- **`wasm-jco new` on the generated bytes**: the core module it wraps is the generated
module, and the stream semantics of `KCore.kcore_stream_semantics` holds for the output. -/
theorem kcore_new {k : Silmaril.Wasm.Component.Streams.Kernel.KM} {N : Nat} (hN : N ≤ 256)
    {name : String} {core : ByteArray} (hb : wasmOf (gen k N) name = .ok core)
    {w : Silmaril.Wasm.Wit.Binary.World} {o : Tool.Out} (h : Tool.newWith core w = .ok o) (x : String)
    (hs : ∀ p, New.plan core w = .ok p → StreamSem.xfShape p x = true) :
    Binary.Core.Encodes core.data.toList (toModule (gen k N) name) ∧
      (∀ m, Binary.Core.decode? core = some m → m = toModule (gen k N) name) ∧
      (∃ p c, New.plan core w = .ok p ∧ New.emit p = .ok c ∧ xparse o.bytes = .ok c.norm ∧
        StreamSem.xfShape p x = true) ∧
      ∀ (cs : List (List Silmaril.Wasm.Component.Val)) (s : StreamSem.SysM (kimpl k N hN).M),
        StreamSem.ReachM (kimpl k N hN) cs s → s.p = .fin → s.m.mode = .exited →
          ∀ acc, s.c = .fin acc → acc = (k.tr.run (cs.flatten.map byteOf)).map u8v :=
  ⟨wasmOf_encodes hb, fun _ hd => wasmOf_decode hb hd, kcore_stream_semantics h x hs k N hN⟩

end Silmaril.Wasm.JcoTool.KCoreEmit
