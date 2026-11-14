module

public import Silmaril.Machine.X86.Cert.Defs
public import Silmaril.Machine.X86.FnContract.Thms
import Silmaril.Proofs.Machine.X86.Cert.Assemble

/-!
# One generic block certificate: assembly and combinators

PROVED once, for every machine `I` and block kind `K` (standard axioms only):

* `Cert.totalIn`: a checked certificate whose VC holds for the run predicate `R` (and whose
  kind admits `R`) gives `Spec.TotalIn I R`: the run takes every step inside `R`;
* `Cert.total`: the `R = True` case, `Spec.Total I` (the old per-kind `total`s);
* `Cert.strict`: with `R` "not yet returned", **`Spec.Strict I`** (first return);
* `Cert.strict_of_local`: for a kind whose run predicates are those containing the code
  region, a certificate's VC gives the strict spec on entries whose return address lies
  outside the code (`Spec.restrict … RetOutside`), with no extra obligation;
* `Cert.contract`, `Cert.strictContract`: the `FnContract` / `FnContract.Strict`.

Combinators (block kinds built from block kinds):

* `BlockKind.sum K₁ K₂`: blocks of either kind (kinds become mixable: a certificate may
  combine Ext9 listings, writing listings, call blocks and jump nodes over one machine);
* `BlockKind.call K`: a `K`-block (the `call` instruction) followed by a callee, discharged
  against the callee's `TotalIn` contract (`Callee`); `Callee.ofContract` takes a plain total
  `FnContract`, so total-correctness callers need nothing more than before.
-/

@[expose] public section

namespace Silmaril.Machine.X86

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Ext (Loaded)
open FnContract (RunsIn InCode AbiEntry Spec Returned RetOutside)

namespace Cert

variable {σ : Type} {I : Isa σ} {K : BlockKind I}

theorem checked_mem {F : Cert I K} (hc : F.checked = true) {b : CBlock K} (hb : b ∈ F.blocks) :
    K.check F.code b.off b.blk = true :=
  Silmaril.Proofs.Machine.X86.Cert.checked_mem hc hb

/-- Arriving at an annotated block with a smaller measure, the code still loaded. -/
theorem next_of {F : Cert I K} {Q : σ → σ → Prop} {s0 m' : σ} {μ : Nat} (b : CBlock K)
    (hb : b ∈ F.blocks) (hrip : (I.core m').rip = F.base + BitVec.ofNat 64 b.off)
    (hl : Loaded (I.mem m') F.base F.code) (ha : F.ann b.off s0 m')
    (hμ : F.measure b.off s0 m' < μ) : F.Next Q s0 μ m' :=
  .inr ⟨b, hb, hrip, hl, ha, hμ⟩

/-- From every annotated block, the machine runs inside `R s0` to the exit condition. -/
theorem from_block {F : Cert I K} {R Q : σ → σ → Prop} (hc : F.checked = true)
    (hvc : F.VCIn R Q) {s0 : σ} (hadm : K.Admits F.base F.code.length (R s0)) {b : CBlock K}
    {m : σ} (hb : b ∈ F.blocks) (ha : F.ann b.off s0 m) (hlv : I.live m)
    (hrip : (I.core m).rip = F.base + BitVec.ofNat 64 b.off) (hl : Loaded (I.mem m) F.base F.code) :
    ∃ t, RunsIn I (R s0) m t ∧ Q s0 t :=
  Silmaril.Proofs.Machine.X86.Cert.from_block hc hvc s0 hadm _ b m rfl hb ha hlv hrip hl

/-- **`TotalIn` from a certificate, once for every kind.** -/
theorem totalIn {F : Cert I K} (S : Spec σ) {R : σ → σ → Prop} {entry : CBlock K}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VCIn R fun s0 t => S.Result I s0 t)
    (hadm : ∀ s, I.live s → AbiEntry (I.core s) (I.mem s) → S.entry s →
      K.Admits F.base F.code.length (R s))
    (hpre : ∀ s, AbiEntry (I.core s) (I.mem s) → S.entry s →
      Loaded (I.mem s) F.base F.code ∧ (I.core s).rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off s s) :
    S.TotalIn I R :=
  Silmaril.Proofs.Machine.X86.Cert.totalIn S hentry hc hvc hadm hpre

/-- **Total correctness from a certificate, once for every kind.** -/
theorem total {F : Cert I K} (S : Spec σ) {entry : CBlock K} (hentry : entry ∈ F.blocks)
    (hc : F.checked = true) (hvc : F.VC fun s0 t => S.Result I s0 t)
    (hpre : ∀ s, AbiEntry (I.core s) (I.mem s) → S.entry s →
      Loaded (I.mem s) F.base F.code ∧ (I.core s).rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off s s) :
    S.Total I :=
  (totalIn S hentry hc hvc (fun _ _ _ _ => K.admits_top _ _) hpre).total

/-- **Strict (first-return) correctness from a certificate, once for every kind.** The VC
is stated for the run predicate "the entry has not returned". -/
theorem strict {F : Cert I K} (S : Spec σ) {entry : CBlock K} (hentry : entry ∈ F.blocks)
    (hc : F.checked = true)
    (hvc : F.VCIn (fun s0 m => ¬ Returned I s0 m) fun s0 t => S.Result I s0 t)
    (hadm : ∀ s, I.live s → AbiEntry (I.core s) (I.mem s) → S.entry s →
      K.Admits F.base F.code.length fun m => ¬ Returned I s m)
    (hpre : ∀ s, AbiEntry (I.core s) (I.mem s) → S.entry s →
      Loaded (I.mem s) F.base F.code ∧ (I.core s).rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off s s) :
    S.Strict I :=
  totalIn S hentry hc hvc hadm hpre

/-- A VC whose kind's WP ignores the run predicate holds for every run predicate. -/
theorem vcIn_of_vc {F : Cert I K} {Q : σ → σ → Prop} (R : σ → σ → Prop)
    (hind : ∀ b R' s Q', K.WP b (fun _ => True) s Q' → K.WP b R' s Q') (h : F.VC Q) :
    F.VCIn R Q :=
  fun b hb s0 m ha hlv hrip hl => hind _ _ _ _ (h b hb s0 m ha hlv hrip hl)

/-- **First return for local kinds.** For a kind whose admissible run predicates are those
containing the code region and whose WP ignores the run predicate (every listing kind), the
total-correctness VC already gives the strict spec on entries whose return address lies outside
the code. -/
theorem strict_of_local {F : Cert I K} (S : Spec σ) {entry : CBlock K}
    (hloc : ∀ base len R, BlockKind.Local I base len R → K.Admits base len R)
    (hind : ∀ b R' s Q', K.WP b (fun _ => True) s Q' → K.WP b R' s Q')
    (hentry : entry ∈ F.blocks) (hc : F.checked = true) (hvc : F.VC fun s0 t => S.Result I s0 t)
    (hpre : ∀ s, AbiEntry (I.core s) (I.mem s) → S.entry s →
      Loaded (I.mem s) F.base F.code ∧ (I.core s).rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off s s) :
    (S.restrict (RetOutside I F.base F.code.length)).Strict I := by
  intro s hlv hab he
  obtain ⟨t, r, res⟩ := totalIn
    (R := fun s0 m => RetOutside I F.base F.code.length s0 → ¬ Returned I s0 m) S hentry hc
    (vcIn_of_vc _ hind hvc)
    (fun _ _ _ _ => hloc _ _ _ fun _ hin hout => FnContract.not_returned_of_inCode hout hin)
    hpre s hlv hab he.1
  exact ⟨t, FnContract.runsIn_mono (fun _ h => h he.2) r, res.restrict⟩

/-- **The function contract** of a certificate. -/
def contract (F : Cert I K) (S : Spec σ) {entry : CBlock K} (hentry : entry ∈ F.blocks)
    (hc : F.checked = true) (hvc : F.VC fun s0 t => S.Result I s0 t)
    (hpre : ∀ s, AbiEntry (I.core s) (I.mem s) → S.entry s →
      Loaded (I.mem s) F.base F.code ∧ (I.core s).rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off s s) :
    FnContract I :=
  ⟨S, total S hentry hc hvc hpre⟩

/-- **The strict function contract** of a certificate. -/
def strictContract (F : Cert I K) (S : Spec σ) {entry : CBlock K} (hentry : entry ∈ F.blocks)
    (hc : F.checked = true)
    (hvc : F.VCIn (fun s0 m => ¬ Returned I s0 m) fun s0 t => S.Result I s0 t)
    (hadm : ∀ s, I.live s → AbiEntry (I.core s) (I.mem s) → S.entry s →
      K.Admits F.base F.code.length fun m => ¬ Returned I s m)
    (hpre : ∀ s, AbiEntry (I.core s) (I.mem s) → S.entry s →
      Loaded (I.mem s) F.base F.code ∧ (I.core s).rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off s s) :
    FnContract.Strict I :=
  FnContract.Strict.ofStrict S (strict S hentry hc hvc hadm hpre)

end Cert

/-! ## Combinators -/

namespace BlockKind

variable {σ : Type} {I : Isa σ}

/-- Soundness of a call block (`call`): the block before the callee, then the callee's
`TotalIn` run, which the WP asks to stay inside `R`. -/
theorem call_sound {K : BlockKind I} {code : List Byte} {base : Word} {o : Nat} {b : K.B}
    {C : FnContract I} {P : σ → σ → Prop} (hC : C.toSpec.TotalIn I P) {R : σ → Prop} {s : σ}
    {Q : σ → Prop} (hok : K.check code o b = true) (hlv : I.live s)
    (hl : Loaded (I.mem s) base code) (hrip : (I.core s).rip = base + BitVec.ofNat 64 o)
    (hadm : K.Admits base code.length R)
    (hwp : K.WP b R s fun m1 => AbiEntry (I.core m1) (I.mem m1) ∧ C.entry m1 ∧
      (∀ m, P m1 m → R m) ∧ ∀ t, C.Result m1 t → Q t) :
    ∃ t, RunsIn I R s t ∧ Q t :=
  Silmaril.Proofs.Machine.X86.Cert.Combinators.call_sound hC hok hlv hl hrip hadm hwp

/-- **Blocks of either kind**, over one machine. -/
def sum (K₁ K₂ : BlockKind I) : BlockKind I where
  B := K₁.B ⊕ K₂.B
  check code o
    | .inl b => K₁.check code o b
    | .inr b => K₂.check code o b
  WP
    | .inl b => K₁.WP b
    | .inr b => K₂.WP b
  Admits base len R := K₁.Admits base len R ∧ K₂.Admits base len R
  admits_top base len := ⟨K₁.admits_top base len, K₂.admits_top base len⟩
  sound {code base o b R s Q} hok hlv hl hrip hadm hwp := by
    cases b with
    | inl b => exact K₁.sound hok hlv hl hrip hadm.1 hwp
    | inr b => exact K₂.sound hok hlv hl hrip hadm.2 hwp

/-- A callee of a call block: a contract with a `TotalIn` proof for the run predicate `P`
(`P m1 m`: the callee's run from its entry `m1` takes steps only from states `m` with
`P m1 m`). -/
structure Callee (I : Isa σ) where
  contract : FnContract I
  P : σ → σ → Prop
  totalIn : contract.toSpec.TotalIn I P

/-- A plain total contract as a callee (with the trivial run predicate). -/
def Callee.ofContract (C : FnContract I) : Callee I :=
  ⟨C, fun _ _ => True, C.total.totalIn⟩

/-- A strict contract as a callee (its run never passes its own return). -/
def Callee.ofStrict (C : FnContract.Strict I) : Callee I :=
  ⟨C.toFnContract, fun s m => ¬ Returned I s m, C.strict⟩

/-- The postcondition a call block's first part (the `call`) must establish: the System V
entry obligations and the callee's precondition, the callee's run inside `R`, and every
result of the callee in `Q`. -/
def CallPost (c : Callee I) (R : σ → Prop) (Q : σ → Prop) (m1 : σ) : Prop :=
  AbiEntry (I.core m1) (I.mem m1) ∧ c.contract.entry m1 ∧ (∀ m, c.P m1 m → R m) ∧
    ∀ t, c.contract.Result m1 t → Q t

/-- **Call blocks**: a `K`-block (the `call` instruction) followed by the callee, discharged
against its contract. The call's own run is not measured: the callee's contract is total. -/
def call (K : BlockKind I) : BlockKind I where
  B := K.B × Callee I
  check code o b := K.check code o b.1
  WP b R s Q := K.WP b.1 R s (CallPost b.2 R Q)
  Admits := K.Admits
  admits_top := K.admits_top
  sound {_ _ _ b _ _ _} hok hlv hl hrip hadm hwp :=
    call_sound b.2.totalIn hok hlv hl hrip hadm hwp

end BlockKind

end Silmaril.Machine.X86
