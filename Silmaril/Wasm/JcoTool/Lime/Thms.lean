module

public import Silmaril.Wasm.JcoTool.Lime.Defs
public import Silmaril.Wasm.JcoTool.Tool.Thms
public import Silmaril.Wasm.JcoTool.Adaptor.Thms
public import Silmaril.Wasm.LimeCompile.Direct.Thms
public import Silmaril.Wasm.Perf.CoreDecode.Thms

/-!
# The correctness theorem of `wasm-jco new --lime`

**`newLime_correct`**: if `newLime core w ad = .ok o`, then

1. the input decodes (silmaril's `decode?`, sound for the Core grammar) to a module `m` that the
   direct 3.0 → Lime compiler maps to a Lime1 module `l`, and the module put into the component
   is the verified encoding of `l.toCore`; for valid `m`, `m` and `l.toCore` are exactly
   export-equivalent at every profile and code-parametric host
   (`LimeCompile.Direct.compile_correct`);
2. the component is the thin wrapper (`ad = none`) or the adaptor-mode component
   (`ad = some alloc`) of those bytes, with the same output bytes, so `Tool.newWith_correct`
   and `Adaptor.newAdaptor_correct` apply to it;
3. every core module of the output decodes and compiles to Lime1.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.Lime

open Silmaril.Wasm.Wit.Binary (World)
open Silmaril.Wasm (Module)
open Silmaril.Wasm.Execution.Core (HostSemantics)
open Silmaril.Wasm.LimeCompile.Direct (compile)
open New (bind_ok require_ok)

theorem isLime_ok {b : ByteArray} (h : isLime b = true) :
    ∃ m l, Silmaril.Wasm.Binary.Core.decode? b = some m ∧ compile m = some l := by
  unfold isLime at h
  rw [Silmaril.Wasm.Perf.CoreDecode.decodeF_eq] at h
  split at h
  · rename_i m hm
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp h
    exact ⟨m, l, hm, hl⟩
  · cases h

theorem toLime_ok {core core' : ByteArray} (h : toLime core = .ok core') :
    ∃ m l, Silmaril.Wasm.Binary.Core.decode? core = some m ∧ compile m = some l ∧
      Silmaril.Wasm.Binary.Core.Encodes core'.data.toList l.toCore := by
  unfold toLime at h
  rw [Silmaril.Wasm.Perf.CoreDecode.decodeF_eq] at h
  split at h
  · cases h
  · rename_i m hm
    split at h
    · cases h
    · rename_i l hl
      cases he : Silmaril.Wasm.Binaryen.Exe.encodeModule? l.toCore with
      | error e => rw [he] at h; cases h
      | ok bs =>
        rw [he] at h
        cases h
        have e : (⟨bs.toArray⟩ : ByteArray).data.toList = bs := List.toList_toArray
        exact ⟨m, l, hm, hl, e ▸ Silmaril.Wasm.Binaryen.Exe.encodeModule?_sound he⟩

theorem toolAdaptor_ok {core : ByteArray} {w : World} {alloc : String} {o : Tool.Out}
    (h : Tool.newAdaptor core w alloc = .ok o) :
    ∃ o', Adaptor.newAdaptor core w alloc = .ok o' ∧ o.bytes = o'.bytes ∧ o.ast = o'.ast := by
  obtain ⟨o', ho, h₁⟩ := bind_ok h
  cases h₁
  exact ⟨o', ho, rfl, rfl⟩

/-- **The correctness theorem of `wasm-jco new --lime`.** -/
theorem newLime_correct {core : ByteArray} {w : World} {ad : Option String} {o : Tool.Out}
    (h : newLime core w ad = .ok o) :
    ∃ (core' : ByteArray) (m : Module) (l : Silmaril.Wasm.Lime1.Module),
      Silmaril.Wasm.Binary.Core.decode? core = some m ∧ compile m = some l ∧
      Silmaril.Wasm.Binary.Core.Encodes core'.data.toList l.toCore ∧
      (∀ {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H),
        Silmaril.Wasm.Execution.Core.Sim.HostParametric host →
        (∃ mt, Silmaril.Wasm.Validation.ModuleOk m mt) →
        Silmaril.Wasm.Binaryen.ExportEquiv (· = ·) P host m l.toCore) ∧
      (ad = none → ∃ o', Tool.newWith core' w = .ok o' ∧ o.bytes = o'.bytes ∧ o.ast = o'.ast ∧ o.ir = o'.ir) ∧
      (∀ alloc, ad = some alloc →
        ∃ o', Adaptor.newAdaptor core' w alloc = .ok o' ∧ o.bytes = o'.bytes ∧ o.ast = o'.ast) ∧
      (∀ b ∈ o.cores, ∃ m' l', Silmaril.Wasm.Binary.Core.decode? b = some m' ∧ compile m' = some l') := by
  obtain ⟨core', hl, h₁⟩ := bind_ok h
  obtain ⟨m, l, hm, hc, he⟩ := toLime_ok hl
  obtain ⟨o', ho', h₂⟩ := bind_ok h₁
  obtain ⟨_, hq, h₃⟩ := bind_ok h₂
  cases h₃
  have hall : ∀ b ∈ o'.cores, isLime b = true := List.all_eq_true.mp (require_ok hq)
  refine ⟨core', m, l, hm, hc, he,
    fun P host hh hv => Silmaril.Wasm.LimeCompile.Direct.compile_correct (P := P) hh hc hv,
    fun hn => ?_, fun alloc ha => ?_, fun b hb => isLime_ok (hall b hb)⟩
  · subst hn
    exact ⟨o', ho', rfl, rfl, rfl⟩
  · subst ha
    obtain ⟨o'', h'', hb, hast⟩ := toolAdaptor_ok ho'
    exact ⟨o'', h'', hb, hast⟩

end Silmaril.Wasm.JcoTool.Lime
