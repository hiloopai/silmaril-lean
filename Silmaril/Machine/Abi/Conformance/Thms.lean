module

public import Silmaril.Machine.Abi.Conformance.Defs
import Silmaril.Proofs.Machine.Abi.Conformance.Basic

/-! # ABI conformance: theorems

PROVED (standard axioms), proofs in `Silmaril.Proofs.Machine.Abi.Conformance.Basic`:

* **The modelled/carried split is a very well-behaved lens**: `overwrite_self`,
  `overwrite_agree`, `overwrite_overwrite`; fields outside the split are carried
  (`overwrite_carried`). For a machine: `Mach.store_store` (put-put), `Mach.store_fills`
  (storing a completion of `s` gives `s`), `Mach.store_carried` (**a field `M` does not model
  is never written**), `Mach.store_modelled`, `Mach.machine_store`, `Mach.fills_core`,
  `Mach.fills_mem`; on a call, `callModelOf_carried_of`;
* `conforms_of_strict`: **the bridge from function contracts**: a first-return contract
  (`FnContract.Spec.Strict`) of the code on `M`, whose entry every completion of every admitted
  call meets and whose results are conforming returns, gives a `Conforms` row in either mode (a
  first return also rules out stuck states, `noStuck_of_firstReturn`);
* `Conforms.steps`: **stuck code does not conform**, in either mode: every completion of an
  admitted call of a conforming function takes a step at its entry;
* `Conforms.onRef`: **a row on `M` holds on every reference machine `M` is faithful to**
  (`Faithful`): the reference machine's first returns are conforming returns, and in total
  mode there is one. A row is a statement about real x86 only through this, with `Faithful`
  as its assumption;
* `Conforms.exists_good`, `Conforms.toSafe`: a total row has an admitted call with a conforming
  return; a total row is a safe row;
* **integer machines (`Mach.ofInt`) keep the stage-1 meaning**: `ofInt_models` (it models
  `.machine` and nothing else), `ofInt_fills` (its one completion is `s.machine`), and the
  definitions read on `s.machine`: `mem_callModelOf_ofInt`, `progress_ofInt_iff`,
  `noStuck_ofInt_iff`, `live_ofInt_iff`, `faithful_ofInt_iff` (a deterministic reference),
  `faithful_ofInt_iff_rel` (a reference relation);
* `callModelOf_carried`: on an integer machine, the call relation carries the state the machine
  lacks (vectors, x87, direction flag, MXCSR, x87 control word, the FFI copy of the thread
  pointer). The return obligations about that state hold by the model; `Faithful` is what makes
  them true of real x86;
* `not_headerSatPartial_nil`, `HeaderSatAvailable.total`: **coverage cannot be hidden**: nothing
  claimed is not partial header satisfaction, and a claimed function in `.safe` mode rules out
  available (hence complete) satisfaction;
* `HeaderSatPartial.conforms`: partial header satisfaction gives each claimed function's row;
* `sysvInt_lower_examples`: what the INTEGER fragment lowers and refuses, and that a coverage's
  `unsupported` exclusions are checked against the lowering.

The negative for the laundering lens of the #994 review, and a machine with hidden state read by
a step that has a faithful reference, are in `Conformance.Lens.Thms`.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance

open Silmaril.Machine.SystemV.Abi
open Silmaril.X86 (MState)
open Silmaril.X86.FnContract (Spec AbiEntry FirstReturn Returned RunsIn)

variable {A : AbiDef} {M : Mach} {mode : Mode} {hdr : HeaderSrc} {f : String} {p : A.V.Proto}
  {c : Code} {frame : Nat} {S : CallSpec A.V p}

/-! ## The modelled/carried split -/

theorem overwrite_self (F : FfiField → Bool) (s : Ffi.State) : overwrite F s s = s :=
  Silmaril.Proofs.Machine.Abi.Conformance.overwrite_self F s

theorem overwrite_agree {F : FfiField → Bool} {f : FfiField} (h : F f = true) (s u : Ffi.State) :
    f.Agree (overwrite F s u) u :=
  Silmaril.Proofs.Machine.Abi.Conformance.overwrite_agree h s u

theorem overwrite_overwrite (F : FfiField → Bool) (s u w : Ffi.State) :
    overwrite F (overwrite F s u) w = overwrite F s w :=
  Silmaril.Proofs.Machine.Abi.Conformance.overwrite_overwrite F s u w

theorem overwrite_carried {F : FfiField → Bool} {f : FfiField} (h : F f = false)
    (s u : Ffi.State) : f.Agree (overwrite F s u) s :=
  Silmaril.Proofs.Machine.Abi.Conformance.overwrite_carried h s u

theorem Mach.store_store (M : Mach) (s : Ffi.State) (x y : M.σ) :
    M.store (M.store s x) y = M.store s y :=
  Silmaril.Proofs.Machine.Abi.Conformance.Mach.store_store M s x y

theorem Mach.store_fills {s : Ffi.State} {x : M.σ} (h : M.Fills s x) : M.store s x = s :=
  Silmaril.Proofs.Machine.Abi.Conformance.Mach.store_fills h

theorem Mach.store_carried {f : FfiField} (h : M.models f = false) (s : Ffi.State) (y : M.σ) :
    f.Agree (M.store s y) s :=
  Silmaril.Proofs.Machine.Abi.Conformance.Mach.store_carried h s y

theorem Mach.store_modelled {f : FfiField} (h : M.models f = true) (s : Ffi.State) (y : M.σ) :
    f.Agree (M.store s y) (M.view y) :=
  Silmaril.Proofs.Machine.Abi.Conformance.Mach.store_modelled h s y

theorem Mach.machine_store (M : Mach) (s : Ffi.State) (y : M.σ) :
    (M.store s y).machine = ⟨M.isa.core y, M.isa.mem y⟩ :=
  Silmaril.Proofs.Machine.Abi.Conformance.Mach.machine_store M s y

theorem Mach.fills_core {s : Ffi.State} {x : M.σ} (h : M.Fills s x) :
    M.isa.core x = s.machine.core :=
  Silmaril.Proofs.Machine.Abi.Conformance.Mach.fills_core h

theorem Mach.fills_mem {s : Ffi.State} {x : M.σ} (h : M.Fills s x) :
    M.isa.mem x = s.machine.memory :=
  Silmaril.Proofs.Machine.Abi.Conformance.Mach.fills_mem h

theorem callModelOf_carried_of {f : FfiField} (hf : M.models f = false) {s t : Ffi.State}
    (h : t ∈ callModelOf M s) : f.Agree t s :=
  Silmaril.Proofs.Machine.Abi.Conformance.callModelOf_carried_of hf h

/-! ## The statement -/

theorem conforms_of_strict {S' : Spec M.σ} (hs : S'.Strict M.isa)
    (hdecl : Declares A hdr f p) (hext : c.off + c.len ≤ c.bytes.length)
    (hnv : ∃ a s, Admit A M p c frame S a s ∧ S.pre a s.machine.memory)
    (hen : ∀ a mem, S.pre a mem → (∀ x, S.objects a mem x → c.Outside x) →
      ∃ s, Admit A M p c frame S a s ∧ S.pre a s.machine.memory ∧
        (∀ x, S.objects a s.machine.memory x ↔ S.objects a mem x) ∧
        ∀ x, S.objects a mem x → s.machine.memory.bytes[x]? = mem.bytes[x]?)
    (habi : ∀ a s, Admit A M p c frame S a s → AbiEntry s.machine.core s.machine.memory)
    (hentry : ∀ a s x, Admit A M p c frame S a s → S.pre a s.machine.memory → M.Fills s x →
      S'.entry x)
    (hgood : ∀ a s x t, Admit A M p c frame S a s → S.pre a s.machine.memory → M.Fills s x →
      FirstReturn M.isa x t → S'.Result M.isa x t → Good A p frame S a s (M.store s t)) :
    Conforms A M mode hdr f p c frame S :=
  Silmaril.Proofs.Machine.Abi.Conformance.conforms_of_strict hs hdecl hext hnv hen habi hentry hgood

theorem Conforms.steps (h : Conforms A M mode hdr f p c frame S) (hlen : 0 < c.len)
    {a : A.V.Args p} {s : Ffi.State} (ad : Admit A M p c frame S a s)
    (pre : S.pre a s.machine.memory) {x : M.σ} (hx : M.Fills s x) : (M.isa.step x).isSome :=
  Silmaril.Proofs.Machine.Abi.Conformance.Conforms.steps h hlen ad pre hx

theorem Conforms.onRef {R : Ref} (hf : Faithful R M) (h : Conforms A M mode hdr f p c frame S)
    {a : A.V.Args p} {s : Ffi.State} (ad : Admit A M p c frame S a s)
    (pre : S.pre a s.machine.memory) :
    (∀ t ∈ R.callModel s, Good A p frame S a s t) ∧
      (mode = .total → (R.callModel s).Nonempty) :=
  Silmaril.Proofs.Machine.Abi.Conformance.Conforms.onRef hf h ad pre

theorem not_headerSatPartial_nil {hdr : HeaderSrc} {cov : Coverage}
    {impl : String → Option (Impl A)} (h : cov.claimed = []) : ¬ HeaderSatPartial A M hdr cov impl :=
  fun hs => hs.1 h

theorem HeaderSatAvailable.total {hdr : HeaderSrc} {cov : Coverage}
    {impl : String → Option (Impl A)} (h : HeaderSatAvailable A M hdr cov impl) {f : String}
    (hf : f ∈ cov.claimed) {i : Impl A} (hi : impl f = some i) : i.mode = .total :=
  let ⟨_, hj, hm⟩ := h.2.2 f hf; Option.some.inj (hi.symm.trans hj) ▸ hm

theorem Conforms.exists_good (h : Conforms A M .total hdr f p c frame S) :
    ∃ a s t, Admit A M p c frame S a s ∧ t ∈ callModelOf M s ∧ Good A p frame S a s t :=
  Silmaril.Proofs.Machine.Abi.Conformance.Conforms.exists_good h

theorem Conforms.toSafe (h : Conforms A M .total hdr f p c frame S) :
    Conforms A M .safe hdr f p c frame S :=
  Silmaril.Proofs.Machine.Abi.Conformance.Conforms.toSafe h

/-! ## Integer machines: the definitions read on `s.machine` -/

/-- **What `Mach.ofInt` models**: the machine field, and nothing else. -/
theorem ofInt_models {I : Silmaril.X86.SegVC.Isa MState} {hc : ∀ m, I.core m = m.core}
    {hm : ∀ m, I.mem m = m.memory} {f : FfiField} :
    (Mach.ofInt I hc hm).models f = true ↔ f = .machine :=
  Silmaril.Proofs.Machine.Abi.Conformance.ofInt_models

/-- The one completion of `s` on an integer machine is `s.machine`. -/
theorem ofInt_fills {I : Silmaril.X86.SegVC.Isa MState} {hc : ∀ m, I.core m = m.core}
    {hm : ∀ m, I.mem m = m.memory} {s : Ffi.State} {x : MState} :
    (Mach.ofInt I hc hm).Fills s x ↔ x = s.machine := Iff.rfl

/-- An integer machine's completions are all the states that fit. -/
theorem ofInt_fillsAll {I : Silmaril.X86.SegVC.Isa MState} {hc : ∀ m, I.core m = m.core}
    {hm : ∀ m, I.mem m = m.memory} : (Mach.ofInt I hc hm).FillsAll :=
  fun _ _ h => h .machine rfl

theorem mem_callModelOf_ofInt {I : Silmaril.X86.SegVC.Isa MState} {hc : ∀ m, I.core m = m.core}
    {hm : ∀ m, I.mem m = m.memory} {s t : Ffi.State} :
    t ∈ callModelOf (Mach.ofInt I hc hm) s ↔
      FirstReturn I s.machine t.machine ∧ t = { s with machine := t.machine } :=
  Silmaril.Proofs.Machine.Abi.Conformance.mem_callModelOf_ofInt

theorem progress_ofInt_iff {I : Silmaril.X86.SegVC.Isa MState} {hc : ∀ m, I.core m = m.core}
    {hm : ∀ m, I.mem m = m.memory} {s : Ffi.State} :
    (∀ x, (Mach.ofInt I hc hm).Fills s x → (callFrom (Mach.ofInt I hc hm) s x).Nonempty) ↔
      (callModelOf (Mach.ofInt I hc hm) s).Nonempty :=
  Silmaril.Proofs.Machine.Abi.Conformance.progress_ofInt_iff

theorem noStuck_ofInt_iff {I : Silmaril.X86.SegVC.Isa MState} {hc : ∀ m, I.core m = m.core}
    {hm : ∀ m, I.mem m = m.memory} {s : Ffi.State} :
    NoStuck (Mach.ofInt I hc hm) s ↔
      ∀ y, RunsIn I (fun z => ¬ Returned I s.machine z) s.machine y →
        ¬ Returned I s.machine y → (I.step y).isSome :=
  Silmaril.Proofs.Machine.Abi.Conformance.noStuck_ofInt_iff

theorem live_ofInt_iff {I : Silmaril.X86.SegVC.Isa MState} {hc : ∀ m, I.core m = m.core}
    {hm : ∀ m, I.mem m = m.memory} {s : Ffi.State} :
    (∀ x, (Mach.ofInt I hc hm).Fills s x → I.live x) ↔ I.live s.machine :=
  Silmaril.Proofs.Machine.Abi.Conformance.live_ofInt_iff

theorem callModelOf_carried {I : Silmaril.X86.SegVC.Isa MState} {hc : ∀ m, I.core m = m.core}
    {hm : ∀ m, I.mem m = m.memory} {s t : Ffi.State}
    (h : t ∈ callModelOf (Mach.ofInt I hc hm) s) :
    t.vectors = s.vectors ∧ t.x87 = s.x87 ∧ t.direction = s.direction ∧ t.x87Mode = s.x87Mode ∧
      t.mxcsr = s.mxcsr ∧ t.x87Control = s.x87Control ∧ t.fsBase = s.fsBase :=
  Silmaril.Proofs.Machine.Abi.Conformance.callModelOf_carried h

theorem faithful_ofInt_iff {r : Ffi.State → Option Ffi.State} {I : Silmaril.X86.SegVC.Isa MState}
    {hc : ∀ m, I.core m = m.core} {hm : ∀ m, I.mem m = m.memory} :
    Faithful (Ref.ofFun r) (Mach.ofInt I hc hm) ↔
      ∀ s m', I.step s.machine = some m' → r s = some { s with machine := m' } :=
  Silmaril.Proofs.Machine.Abi.Conformance.faithful_ofInt_iff

theorem faithful_ofInt_iff_rel {R : Ref} {I : Silmaril.X86.SegVC.Isa MState}
    {hc : ∀ m, I.core m = m.core} {hm : ∀ m, I.mem m = m.memory} :
    Faithful R (Mach.ofInt I hc hm) ↔
      ∀ s m', I.step s.machine = some m' → ∀ t, R.Step s t ↔ t = { s with machine := m' } :=
  Silmaril.Proofs.Machine.Abi.Conformance.faithful_ofInt_iff_rel

theorem HeaderSatPartial.conforms {cov : Coverage} {impl : String → Option (Impl A)}
    (h : HeaderSatPartial A M hdr cov impl) {f : String} (hf : f ∈ cov.claimed) :
    ∃ i, impl f = some i ∧ Conforms A M i.mode hdr f i.proto i.code i.frame i.spec :=
  h.2.2 f hf

/-! ## The INTEGER fragment's lowering, on examples -/

/-- What `sysvInt` lowers and refuses, and a coverage with an `unsupported` exclusion. -/
theorem sysvInt_lower_examples :
    (sysvInt.lower [] ⟨.int .long .unsigned, [.ptr .void, .int .int .signed], false⟩).toOption.map
        (·.signature) = some ⟨[.pointer, .int32], some .uint64⟩ ∧
    (sysvInt.lower [] ⟨.void, [.int .size .unsigned], false⟩).toOption.map (·.signature) =
      some ⟨[.uint64], none⟩ ∧
    (sysvInt.lower [] ⟨.float .double, [.float .double], false⟩).toOption.isNone = true ∧
    (sysvInt.lower [] ⟨.int .int .signed, [.struct "s"], false⟩).toOption.isNone = true ∧
    (sysvInt.lower [] ⟨.int .int .signed, [.int .short .signed], false⟩).toOption.isNone = true ∧
    (sysvInt.lower [] ⟨.int .int .signed, [.ptr (.int .char .plain)], true⟩).toOption.isNone = true ∧
    Coverage.check sysvInt ⟨[("h.h", "double f(double); int g(int); int printf(const char *, ...);")], "h.h"⟩
      ⟨[], [("f", .unsupported "SSE"), ("g", .unclaimed "example"),
        ("printf", .unsupported "varargs")]⟩ = true ∧
    Coverage.check sysvInt ⟨[("h.h", "double f(double); int g(int);")], "h.h"⟩
      ⟨[], [("f", .unsupported "SSE"), ("g", .unsupported "wrong")]⟩ = false := by
  decide +kernel

end Silmaril.Machine.Abi.Conformance

end
