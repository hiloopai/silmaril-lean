module

public import Silmaril.Machine.Abi.Conformance.Defs
import Silmaril.Proofs.Machine.Abi.Conformance.Basic

/-! # ABI conformance: theorems

PROVED (standard axioms), proofs in `Silmaril.Proofs.Machine.Abi.Conformance.Basic`:

* `conforms_of_strict`: **the bridge from function contracts**: a first-return contract
  (`FnContract.Spec.Strict`) of the code on `M`, whose entry every admitted call meets and whose
  results are conforming returns, gives a `Conforms` row in either mode (a first return also
  rules out stuck states, `noStuck_of_firstReturn`);
* `Conforms.steps`: **stuck code does not conform**, in either mode: an admitted call of a
  conforming function takes a step at its entry;
* `Conforms.onRef`: **a row on `M` holds on every reference machine `M` is faithful to**
  (`Faithful`): the reference machine's first returns are conforming returns, and in total
  mode there is one. A row is a statement about real x86 only through this, with `Faithful`
  as its assumption;
* `Conforms.exists_good`, `Conforms.toSafe`: a total row has an admitted call with a conforming
  return; a total row is a safe row;
* `callModelOf_carried`: the call relation carries the state the integer machine lacks (vectors,
  x87, direction flag, MXCSR, x87 control word, the FFI copy of the thread pointer). The return
  obligations about that state hold by the model; `Faithful` is what makes them true of real x86;
* `not_headerSatPartial_nil`, `HeaderSatAvailable.total`: **coverage cannot be hidden**: nothing
  claimed is not partial header satisfaction, and a claimed function in `.safe` mode rules out
  available (hence complete) satisfaction;
* `HeaderSatPartial.conforms`: partial header satisfaction gives each claimed function's row;
* `sysvInt_lower_examples`: what the INTEGER fragment lowers and refuses, and that a coverage's
  `unsupported` exclusions are checked against the lowering.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance

open Silmaril.Machine.SystemV.Abi
open Silmaril.X86 (MState)
open Silmaril.X86.FnContract (Spec AbiEntry FirstReturn)

variable {A : AbiDef} {M : Mach} {mode : Mode} {hdr : HeaderSrc} {f : String} {p : A.V.Proto}
  {c : Code} {frame : Nat} {S : CallSpec A.V p}

theorem conforms_of_strict {S' : Spec MState} (hs : S'.Strict M)
    (hdecl : Declares A hdr f p) (hext : c.off + c.len ≤ c.bytes.length)
    (hnv : ∃ a s, Admit A M p c frame S a s ∧ S.pre a s.machine.memory)
    (hen : ∀ a mem, S.pre a mem → (∀ x, S.objects a mem x → c.Outside x) →
      ∃ s, Admit A M p c frame S a s ∧ S.pre a s.machine.memory ∧
        (∀ x, S.objects a s.machine.memory x ↔ S.objects a mem x) ∧
        ∀ x, S.objects a mem x → s.machine.memory.bytes[x]? = mem.bytes[x]?)
    (habi : ∀ a s, Admit A M p c frame S a s → AbiEntry (M.core s.machine) (M.mem s.machine))
    (hentry : ∀ a s, Admit A M p c frame S a s → S.pre a s.machine.memory → S'.entry s.machine)
    (hgood : ∀ a s t, Admit A M p c frame S a s → S.pre a s.machine.memory →
      FirstReturn M s.machine t → S'.Result M s.machine t →
      Good A p frame S a s { s with machine := t }) :
    Conforms A M mode hdr f p c frame S :=
  Silmaril.Proofs.Machine.Abi.Conformance.conforms_of_strict hs hdecl hext hnv hen habi hentry hgood

theorem Conforms.steps (h : Conforms A M mode hdr f p c frame S) (hc : ∀ m, M.core m = m.core)
    (hm : ∀ m, M.mem m = m.memory) (hlen : 0 < c.len) {a : A.V.Args p} {s : Ffi.State}
    (ad : Admit A M p c frame S a s) (pre : S.pre a s.machine.memory) :
    (M.step s.machine).isSome :=
  Silmaril.Proofs.Machine.Abi.Conformance.Conforms.steps h hc hm hlen ad pre

theorem Conforms.onRef {R : Ref} (hf : Faithful R M) (h : Conforms A M mode hdr f p c frame S)
    {a : A.V.Args p} {s : Ffi.State} (ad : Admit A M p c frame S a s)
    (pre : S.pre a s.machine.memory) :
    (∀ t ∈ R.callModel M s, Good A p frame S a s t) ∧
      (mode = .total → (R.callModel M s).Nonempty) :=
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

theorem callModelOf_carried {s t : Ffi.State} (h : t ∈ callModelOf M s) :
    t.vectors = s.vectors ∧ t.x87 = s.x87 ∧ t.direction = s.direction ∧ t.x87Mode = s.x87Mode ∧
      t.mxcsr = s.mxcsr ∧ t.x87Control = s.x87Control ∧ t.fsBase = s.fsBase := by
  rw [h.2]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem HeaderSatPartial.conforms {cov : Coverage} {impl : String → Option (Impl A)}
    (h : HeaderSatPartial A M hdr cov impl) {f : String} (hf : f ∈ cov.claimed) :
    ∃ i, impl f = some i ∧ Conforms A M i.mode hdr f i.proto i.code i.frame i.spec :=
  h.2.2 f hf

/-! ## The INTEGER fragment's lowering, on examples -/

/-- What `sysvInt` lowers and refuses, and a coverage with an `unsupported` exclusion. -/
theorem sysvInt_lower_examples :
    (sysvInt.lower ⟨.int .long .unsigned, [.ptr .void, .int .int .signed], false⟩).toOption.map
        (·.signature) = some ⟨[.pointer, .int32], some .uint64⟩ ∧
    (sysvInt.lower ⟨.void, [.int .size .unsigned], false⟩).toOption.map (·.signature) =
      some ⟨[.uint64], none⟩ ∧
    (sysvInt.lower ⟨.float .double, [.float .double], false⟩).toOption.isNone = true ∧
    (sysvInt.lower ⟨.int .int .signed, [.struct "s"], false⟩).toOption.isNone = true ∧
    (sysvInt.lower ⟨.int .int .signed, [.int .short .signed], false⟩).toOption.isNone = true ∧
    (sysvInt.lower ⟨.int .int .signed, [.ptr (.int .char .plain)], true⟩).toOption.isNone = true ∧
    Coverage.check sysvInt ⟨[("h.h", "double f(double); int g(int); int printf(const char *, ...);")], "h.h"⟩
      ⟨[], [("f", .unsupported "SSE"), ("g", .unclaimed "example"),
        ("printf", .unsupported "varargs")]⟩ = true ∧
    Coverage.check sysvInt ⟨[("h.h", "double f(double); int g(int);")], "h.h"⟩
      ⟨[], [("f", .unsupported "SSE"), ("g", .unsupported "wrong")]⟩ = false := by
  decide +kernel

end Silmaril.Machine.Abi.Conformance

end
