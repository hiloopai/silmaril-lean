module

public import Silmaril.Wasm.JcoTool.KDropEmit.Defs
public import Silmaril.Wasm.JcoTool.KCoreEmit.Thms
public import Silmaril.Wasm.JcoTool.KDrop.Thms

/-!
# The bytes and text of `wasm-jco kcore` are the drop-aware generated module

`wasm-jco kcore NAME KERNEL N` emits `KDropEmit.toolGen false k N = KDrop.genD k N`:

* `kdrop_bytes`: the bytes of `-o OUT.wasm` encode `KCoreEmit.toModule (genD k N) NAME` in the
  Core 3.0 binary grammar (silmaril's verified encoder), and silmaril's verified decoder reads
  back exactly that module (`kdrop_decode`);
* `kdrop_wat`: the default output (the `Prog.wat` printer, checked) and `--canonical` (silmaril's
  checked printer) denote the same module in the Core 3.0 text grammar;
* `kdrop_tool_correct`: and the program behind them is the one of `KDrop.Thms`: for chains of
  such modules between a source and a sink, `kchain_correct` holds.

The `KCoreEmit` theorems are stated for every program; this module instantiates them at the
tool's generator. Not covered: the link from `toModule (genD k N)` to the fragment semantics
`KDrop.dexec` (the realise part's `KCoreCore` covers expressions, `local.set`, `global.set`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KDropEmit

open Silmaril.Wasm.JcoTool.KCoreEmit
open Silmaril.Wasm.Component.Streams.Kernel (KM)
open Silmaril.Wasm.Component (Val)

theorem toolGen_false (k : KM) (N : Nat) : toolGen false k N = KDrop.genD k N := rfl

theorem toolGen_true (k : KM) (N : Nat) : toolGen true k N = KCore.gen k N := rfl

/-- **The bytes `wasm-jco kcore … -o` writes** encode the drop-aware generated module. -/
theorem kdrop_bytes {k : KM} {N : Nat} {name : String} {b : ByteArray}
    (h : wasmOf (toolGen false k N) name = .ok b) :
    Silmaril.Wasm.Binary.Core.Encodes b.data.toList (toModule (KDrop.genD k N) name) :=
  wasmOf_encodes h

/-- Silmaril's verified decoder reads back the drop-aware generated module from those bytes. -/
theorem kdrop_decode {k : KM} {N : Nat} {name : String} {b : ByteArray}
    (h : wasmOf (toolGen false k N) name = .ok b) {m : Silmaril.Wasm.Module}
    (hd : Silmaril.Wasm.Binary.Core.decode? b = some m) : m = toModule (KDrop.genD k N) name :=
  wasmOf_decode h hd

/-- **The text `wasm-jco kcore` prints** (by default, checked; or `--canonical`) denotes the
drop-aware generated module. -/
theorem kdrop_wat {k : KM} {N : Nat} {name : String} {t : String}
    (h : watChecked (toolGen false k N) name = .ok t ∨ watOf (toolGen false k N) name = .ok t) :
    Silmaril.Wasm.Text.Core.Encodes t (toModule (KDrop.genD k N) name) := by
  rcases h with h | h
  · exact (watChecked_encodes h).2
  · exact watOf_encodes h

/-- **The tool's program is the proved one**: the module of `wasm-jco kcore` encodes
`toModule (genD k N)`, and chains of `genD` modules between a source and a sink are correct under
the drop semantics (`KDrop.kchain_correct`). -/
theorem kdrop_tool_correct {k : KM} {N : Nat} {name : String} {b : ByteArray}
    (h : wasmOf (toolGen false k N) name = .ok b) :
    Silmaril.Wasm.Binary.Core.Encodes b.data.toList (toModule (KDrop.genD k N) name) ∧
      ∀ {xs : List Val} {ks : List KM} {Nb : Nat → Nat}, (∀ i, 0 < Nb i ∧ Nb i ≤ 256) →
        ks.length < 2 ^ 26 → ∀ {c : KDrop.KSys ks.length}, KDrop.KReach xs ks Nb c →
        ∀ {bb : Bool}, c.snk.rd = .gone bb → c.snk.got = KDrop.runs ks xs :=
  ⟨kdrop_bytes h, fun hN hws _ hR _ hb => KDrop.kchain_correct hN hws hR hb⟩

end Silmaril.Wasm.JcoTool.KDropEmit
