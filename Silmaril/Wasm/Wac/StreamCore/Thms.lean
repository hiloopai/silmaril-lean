module

public import Silmaril.Wasm.Wac.StreamCore.Defs
public import Silmaril.Wasm.Wac.StreamFn.Thms
public import Silmaril.Wasm.JcoTool.KRead.Thms
public import Silmaril.Wasm.JcoTool.KCoreEmit.Thms

/-!
# WAC: the `κ` of the generated stream modules, on Core 3.0

* `kappa_sound`, `kappa_decode`: `kappa gs b = some t` only when some module `g` of the table
  writes the bytes `b` and `t` is its code; whatever silmaril's verified decoder reads from `b`
  is the generated module `toModule (genD g.k g.N) g.name` (`KCoreEmit.wasmOf_decode`).
* **`kappa_core`** (for injective `hb`): then
  every finished run on Core 3.0 of that module (from a store holding it, `KRead.Inst0`), as
  the pipe `source xs → module → sink`, outputs `t.run xs`. So the answer `callSem` gives a call
  of the package (`t.run` of the stream) is the Core runtime's whole output.
  **`kappa_core_reads`** (adding `FlushNil`): the Core runtime
  reads as `trV g.k`, whose whole output is `t.run`, and its game reading is
  `StreamGame.den (trV g.k)`.
* **`composeText_gen_equiv`**: `StreamFn.composeText_fn_equiv` with this `κ`: the same WAC text
  with two sets of package bytes, whose stream packages are generated modules of kernels with
  equal whole outputs (`runAgree_of_kernels`), gives equivalent compositions (`callSem`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.StreamCore

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Algebra
open Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.BinaryAsync
open Silmaril.Wasm.Component.Streams.Alg (TCode)
open Silmaril.Wasm.Wac.StreamPkg (Interp XfShape)
open Silmaril.Wasm.Wac.StreamFn
open Silmaril.Wasm.Wac.SpliceX Silmaril.Wasm.Wac.Emit Silmaril.Wasm.Wac.EndToEnd
open Silmaril.Wasm.JcoTool.KCore (trV BI)
open Silmaril.Wasm.JcoTool.KDrop (genD)
open Silmaril.Wasm.JcoTool.KRead (coreObs Inst0 FlushNil)
open Silmaril.Wasm.Numerics (Profile GrowKind)

theorem okIs_iff {x : Except String ByteArray} {b : ByteArray} : okIs x b = true ↔ x = .ok b := by
  cases x with
  | error e => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | ok b' =>
    show (b'.data == b.data) = true ↔ _
    rw [beq_iff_eq]
    constructor
    · intro h
      exact congrArg Except.ok (ByteArray.ext h)
    · intro h
      cases h
      rfl

theorem writes_iff {g : Gen} {b : ByteArray} : g.writes b = true ↔ g.bytes = .ok b :=
  okIs_iff

/-- **What `kappa` returns is the code of a module that writes the bytes.** -/
theorem kappa_sound {gs : List Gen} {b : ByteArray} {t : TCode} (h : kappa gs b = some t) :
    ∃ g ∈ gs, g.bytes = .ok b ∧ g.code = t := by
  unfold kappa at h
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 h
  have hw : g.writes b = true := List.find?_some (p := fun x : Gen => x.writes b) hg
  exact ⟨g, List.mem_of_find?_eq_some hg, writes_iff.1 hw, rfl⟩

/-- Whatever the verified decoder reads from the bytes is the generated module. -/
theorem kappa_decode {gs : List Gen} {b : ByteArray} {t : TCode} (h : kappa gs b = some t) :
    ∃ g ∈ gs, g.code = t ∧ ∀ m, Silmaril.Wasm.Binary.Core.decode? b = some m →
      m = Silmaril.Wasm.JcoTool.KCoreEmit.toModule (genD g.k g.N) g.name := by
  obtain ⟨g, hg, hb, ht⟩ := kappa_sound h
  exact ⟨g, hg, ht, fun _ hd => Silmaril.Wasm.JcoTool.KCoreEmit.wasmOf_decode hb hd⟩

/-- **The code `kappa` gives is the Core runtime's whole output.** -/
theorem kappa_core {gs : List Gen}
    (hg : GensOK gs) {b : ByteArray} {t : TCode} (h : kappa gs b = some t) :
    ∃ g ∈ gs, g.code = t ∧ g.bytes = .ok b ∧
      (∀ m, Silmaril.Wasm.Binary.Core.decode? b = some m →
        m = Silmaril.Wasm.JcoTool.KCoreEmit.toModule (genD g.k g.N) g.name) ∧
      ∀ (o : GrowKind → Nat → Nat → Nat → Bool) {H : Type} (hb : BI → H), Function.Injective hb →
        ∀ (ma a : Nat) (mi : Silmaril.Wasm.Execution.Core.ModuleInst)
          (cs₀ : Silmaril.Wasm.Execution.Core.Store H), Inst0 hb ma a g.k g.N mi cs₀ →
          ∀ xs ys, (coreObs (Profile.deterministic o) hb ma a g.k cs₀).whole xs ys → ys = t.run xs := by
  obtain ⟨g, hmem, hb, ht⟩ := kappa_sound h
  obtain ⟨hN₁, hN₂, hrun, hfit⟩ := hg g hmem
  refine ⟨g, hmem, ht, hb, fun _ hd => Silmaril.Wasm.JcoTool.KCoreEmit.wasmOf_decode hb hd, ?_⟩
  intro o H hb' hinj ma a mi cs₀ h0 xs ys hw
  rw [← ht, hrun]
  exact Silmaril.Wasm.JcoTool.KRead.core_whole_correct hinj o ⟨hN₁, hN₂⟩ hfit h0 hw

/-- With liveness, **the Core runtime of the module reads as its kernel**, whose whole output is
the code `kappa` gives; its game reading is the kernel's stream game. -/
theorem kappa_core_reads {gs : List Gen} (hg : GensOK gs) {b : ByteArray} {t : TCode} (h : kappa gs b = some t) :
    ∃ g ∈ gs, g.code = t ∧ g.bytes = .ok b ∧ t.run = (trV g.k).run ∧
      ∀ (o : GrowKind → Nat → Nat → Nat → Bool) {H : Type} (hb : BI → H), Function.Injective hb →
        ∀ (ma a : Nat) (mi : Silmaril.Wasm.Execution.Core.ModuleInst)
          (cs₀ : Silmaril.Wasm.Execution.Core.Store H), Inst0 hb ma a g.k g.N mi cs₀ → FlushNil g.k →
          (coreObs (Profile.deterministic o) hb ma a g.k cs₀).Reads (trV g.k) ∧
          (coreObs (Profile.deterministic o) hb ma a g.k cs₀).game =
            Silmaril.Wasm.Component.Algebra.StreamGame.den (trV g.k) := by
  obtain ⟨g, hmem, hb, ht⟩ := kappa_sound h
  obtain ⟨hN₁, hN₂, hrun, hfit⟩ := hg g hmem
  refine ⟨g, hmem, ht, hb, ht ▸ hrun, ?_⟩
  intro o H hb' hinj ma a mi cs₀ h0 hk
  exact ⟨Silmaril.Wasm.JcoTool.KRead.core_reads hinj o ⟨hN₁, hN₂⟩ hfit h0 hk,
    Silmaril.Wasm.JcoTool.KRead.core_game hinj o ⟨hN₁, hN₂⟩ hfit h0 hk⟩

/-- **Package tables agree when their stream packages are generated modules of kernels with equal
whole outputs** (the first module of the table that writes each package's core bytes). -/
theorem runAgree_of_kernels {gs : List Gen} (hg : GensOK gs) {tbl tbl' : PkgTableX}
    (h : ∀ n, tbl.lookup n = tbl'.lookup n ∨
      ∃ a a' s s' g g', tbl.lookup n = some a ∧ tbl'.lookup n = some a' ∧ fnShape a = some s ∧
        fnShape a' = some s' ∧ gs.find? (·.writes s.core) = some g ∧
        gs.find? (·.writes s'.core) = some g' ∧ s.name = s'.name ∧
        (trV g.k).run = (trV g'.k).run) :
    RunAgreeF (kappa gs) tbl tbl' := by
  intro n
  rcases h n with he | ⟨a, a', s, s', g, g', ha, ha', hs, hs', hf, hf', hn, hk⟩
  · exact .inl he
  · refine .inr ⟨a, a', s, s', g.code, g'.code, ha, ha', hs, ?_, hs', ?_, hn, ?_⟩
    · simp [kappa, hf]
    · simp [kappa, hf']
    · rw [(hg g (List.mem_of_find?_eq_some hf)).2.2.1, (hg g' (List.mem_of_find?_eq_some hf')).2.2.1, hk]

/-- **Generated stream packages of kernels with equal whole outputs compose to equivalent
components**, from the WAC text and the bytes, read with the `κ` of the generated modules. -/
theorem composeText_gen_equiv {src : String} {raw raw' : List (String × ByteArray)}
    {b b' : ByteArray} {tbl tbl' : PkgTableX}
    (h : composeText src raw = .ok (b, some tbl, true))
    (h' : composeText src raw' = .ok (b', some tbl', true))
    (hT : ∀ k, (raw.lookup k).map TypeOf.decodeAnyX = (raw'.lookup k).map TypeOf.decodeAnyX)
    (S : Nat → PkgSig) (gs : List Gen) (other : AstX → Option (Comp FCode)) (dflt : Comp FCode)
    (hr : RunAgreeF (kappa gs) tbl tbl') :
    ∃ X X', binCompX S (readFn (kappa gs) other) dflt b = .ok X ∧
      binCompX S (readFn (kappa gs) other) dflt b' = .ok X' ∧ CompEquiv callSem X X' :=
  composeText_fn_equiv h h' hT S (kappa gs) other dflt hr

end Silmaril.Wasm.Wac.StreamCore
