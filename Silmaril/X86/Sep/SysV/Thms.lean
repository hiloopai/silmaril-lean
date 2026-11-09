module

public import Silmaril.X86.Sep.SysV.Defs
public import Silmaril.X86.Sep.Spec.Thms
public import Silmaril.X86.FnContract.Thms
public import Silmaril.X86.Open.Thms
public import Silmaril.X86.Open9.Thms
public import Silmaril.X86.Str9.Thms
import Silmaril.Proofs.X86.Sep.Call
import Silmaril.Proofs.X86.Sep.SysV
import Silmaril.Proofs.X86.Sep.Contract

/-!
# System V specs: the call rule, frames, refinement and contracts

* `call_step`, `ret_step`, `push_step`, `pop_step`: the `call rel32`, `ret`, `push r` and
  `pop r` triples, proved on `Open.isa` and
  stated on every machine `I` with `Open.isa.Extends I` (`Isa.Extends.refl`,
  `Open9.extendsOpen`, `Str9.extendsOpen`).
* `call_rule`: **calling a function that meets `S`.** A `call rel32` to the callee's entry,
  from a 16-byte-aligned (or `A`-admissible) stack pointer `s` with `S.stack + 8` bytes of
  budget below it, behaves as one instruction that consumes the arguments and returns
  `rax ↦ v` with `S.post`. It is derived from `call_step`, the callee's `SatWith` and the
  frame rule; nothing else of the caller is touched.
* `calleeSaved_by_frame`: callee-saved registers (and anything else the caller owns) survive
  a call because they are in the frame, not in the template.
* `FnSpec.Sub.refl`, `FnSpec.Sub.trans`, `FnSpec.SatWith.mono`: refinement of specs;
  `FnSpec.SatWith.lift`, `FnSpec.Sat.lift`: specs move up machine extensions.
* `FnSpec.satWith_of_runs`: a spec from returning runs (the bridge for machine proofs).
  `FnSpec.sat_of_fnContract`: a spec from a `FnContract` (a `FnContract.Strict` gives one
  through its `toFnContract`).
* `FnSpec.Sat.toFnContract`: a spec as a total `FnContract` on a `Flat` machine
  (`flat_open`, `flat_open9`, `flat_str9`), when its precondition's fragments own neither
  the mappings nor a callee-saved register. A spec is angelic (`Triple`), so it gives
  `Spec.Total`, not the first-return `Spec.Strict`.
-/

@[expose] public section

namespace Silmaril.X86.Sep

open Silmaril.X86 (State MState Word Byte Reg Insn sysv64)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86.SegVC (Isa)
open Frag (union Disjoint Le reval)

variable {σ τ : Type} {I : Isa σ}

theorem calleeSavedRegs_eq : calleeSavedRegs = sysv64.calleeSaved := rfl

/-! ## Instructions -/

/-- **`call rel32`**: push the return address into the eight bytes below `rsp` and jump. -/
theorem call_step (E : Open.isa.Extends I) (pc s : Word) (rel : BitVec 32)
    (hs : 8 ≤ s.toNat) :
    Triple I (codePt pc.toNat (Insn.encode (.call rel)) ∗ ripPt pc ∗ regPt .rsp s ∗
        blockAny (s.toNat - 8) 8)
      (codePt pc.toNat (Insn.encode (.call rel)) ∗ ripPt (pc + 5#64 + rel.signExtend 64) ∗
        regPt .rsp (s - 8#64) ∗ wordPt (s.toNat - 8) (pc + 5#64)) :=
  (Silmaril.Proofs.X86.Sep.call_step pc s rel hs).lift E

/-- **`ret`**: pop the return address into `rip`. -/
theorem ret_step (E : Open.isa.Extends I) (q s r : Word) :
    Triple I (codePt q.toNat (Insn.encode .ret) ∗ ripPt q ∗ regPt .rsp s ∗ wordPt s.toNat r)
      (codePt q.toNat (Insn.encode .ret) ∗ ripPt r ∗ regPt .rsp (s + 8#64) ∗
        wordPt s.toNat r) :=
  (Silmaril.Proofs.X86.Sep.ret_step q s r).lift E

/-- **`push r`** (`r ≠ rsp`): store `r` into the eight bytes below `rsp`. -/
theorem push_step (E : Open.isa.Extends I) (pc s v : Word) (r : Reg) (hr : r ≠ .rsp)
    (hs : 8 ≤ s.toNat) :
    Triple I (codePt pc.toNat (Insn.encode (.push r)) ∗ ripPt pc ∗ regPt .rsp s ∗ regPt r v ∗
        blockAny (s.toNat - 8) 8)
      (codePt pc.toNat (Insn.encode (.push r)) ∗
        ripPt (pc + BitVec.ofNat 64 (Insn.push r).length) ∗ regPt .rsp (s - 8#64) ∗
        regPt r v ∗ wordPt (s.toNat - 8) v) :=
  (Silmaril.Proofs.X86.Sep.push_step pc s v r hr hs).lift E

/-- **`pop r`** (`r ≠ rsp`): load the eight bytes at `rsp` into `r`. -/
theorem pop_step (E : Open.isa.Extends I) (q s w : Word) (r : Reg) (hr : r ≠ .rsp) :
    Triple I (codePt q.toNat (Insn.encode (.pop r)) ∗ ripPt q ∗ regPt .rsp s ∗ regAny r ∗
        wordPt s.toNat w)
      (codePt q.toNat (Insn.encode (.pop r)) ∗
        ripPt (q + BitVec.ofNat 64 (Insn.pop r).length) ∗ regPt .rsp (s + 8#64) ∗
        regPt r w ∗ wordPt s.toNat w) :=
  (Silmaril.Proofs.X86.Sep.pop_step q s w r hr).lift E

/-! ## The call rule -/

/-- **The call rule.** -/
theorem call_rule (E : Open.isa.Extends I) {A : Word → Prop} {S : FnSpec} {Cf : SProp}
    {f pc s : Word} {rel : BitVec 32} (x : S.Arg) (hS : S.SatWith I A Cf f)
    (hf : pc + 5#64 + rel.signExtend 64 = f) (hA : A (s - 8#64))
    (hlow : S.stack + 8 ≤ s.toNat) :
    SPEC I (codePt pc.toNat (Insn.encode (.call rel)) ∗ Cf)
      (ripPt pc ∗ regPt .rsp s ∗ SysVRegs (S.args x) ∗ flagsAny ∗
        blockAny (s.toNat - 8 - S.stack) (S.stack + 8) ∗ S.pre x)
      (sexists fun v => ripPt (pc + 5#64) ∗ regPt .rsp s ∗ SysVRet v ∗ flagsAny ∗
        blockAny (s.toNat - 8 - S.stack) (S.stack + 8) ∗ S.post x v) :=
  Silmaril.Proofs.X86.SepSysV.call_rule E x hS hf hA hlow

/-- A 16-byte-aligned call site gives the callee an aligned entry. -/
theorem entryAligned_of_call {s : Word} (h : s.toNat % 16 = 0) (h8 : 8 ≤ s.toNat) :
    FnSpec.EntryAligned (s - 8#64) := by
  unfold FnSpec.EntryAligned
  rw [Silmaril.Proofs.X86.Sep.toNat_sub_eight h8]
  omega

/-- **Callee-saved registers by frame.** Whatever the caller owns besides the template —
in particular the callee-saved registers with their values — is returned unchanged. -/
theorem calleeSaved_by_frame {A : Word → Prop} {S : FnSpec} {C : SProp} {entry : Word}
    (hS : S.SatWith I A C entry) (x : S.Arg) {sp ret : Word} (hA : A sp)
    (hst : S.stack ≤ sp.toNat) (vs : List Word) :
    SPEC I C (S.SysVPre x entry sp ret ∗ regsWith calleeSavedRegs vs)
      (S.SysVPost x sp ret ∗ regsWith calleeSavedRegs vs) :=
  SPEC.frame (hS x sp ret hA hst) _

/-! ## Refinement -/

theorem FnSpec.Sub.refl (S : FnSpec) : S.Sub S :=
  ⟨le_refl _, fun y => ⟨y, rfl, emp, entails_of_eq (sep_emp _).symm,
    fun _ => entails_of_eq (sep_emp _)⟩⟩

theorem FnSpec.Sub.trans {S T U : FnSpec} (h₁ : S.Sub T) (h₂ : T.Sub U) : S.Sub U :=
  Silmaril.Proofs.X86.SepSysV.sub_trans h₁ h₂

/-- **Refinement**: a function meeting `S` meets every `T` with `S ⊑ T`. -/
theorem FnSpec.SatWith.mono {A : Word → Prop} {S T : FnSpec} {C : SProp} {entry : Word}
    (hS : S.SatWith I A C entry) (hsub : S.Sub T) : T.SatWith I A C entry :=
  Silmaril.Proofs.X86.SepSysV.sub_mono hS hsub

/-- A stronger stack-pointer assumption is a weaker spec. -/
theorem FnSpec.SatWith.weaken {A B : Word → Prop} {S : FnSpec} {C : SProp} {entry : Word}
    (hS : S.SatWith I A C entry) (hBA : ∀ sp, B sp → A sp) : S.SatWith I B C entry :=
  fun x sp ret hB hst => hS x sp ret (hBA sp hB) hst

theorem FnSpec.SatWith.code_frame {A : Word → Prop} {S : FnSpec} {C : SProp} {entry : Word}
    (hS : S.SatWith I A C entry) (D : SProp) : S.SatWith I A (C ∗ D) entry :=
  fun x sp ret hA hst => SPEC.code_frame (hS x sp ret hA hst) D

/-- **A spec on `I` is a spec on every machine extending `I`.** -/
theorem FnSpec.SatWith.lift {J : Isa τ} (E : I.Extends J) {A : Word → Prop} {S : FnSpec}
    {C : SProp} {entry : Word} (hS : S.SatWith I A C entry) : S.SatWith J A C entry :=
  fun x sp ret hA hst => (hS x sp ret hA hst).lift E

theorem FnSpec.Sat.lift {J : Isa τ} (E : I.Extends J) {S : FnSpec} {C : SProp} {entry : Word}
    (hS : S.Sat I C entry) : S.Sat J C entry :=
  FnSpec.SatWith.lift E hS

/-! ## Specs from runs and contracts -/

/-- **A System V spec from returning runs.** For every live entry state whose fragment
splits as code `hc`, template `ht` and user part `hu`, a run of `I` to the return address,
with `rsp` popped, callee-saved registers restored, memory written only inside the template
and the user part, and the user postcondition on the user part of the final state. -/
theorem FnSpec.satWith_of_runs {A : Word → Prop} {S : FnSpec} {C : SProp} {entry : Word}
    (h : ∀ x sp ret (m : σ) (hc ht hu : Frag), I.live m → A sp → S.stack ≤ sp.toNat → C hc →
      S.SysVEntry x entry sp ret ht → S.pre x hu → Disjoint hc (union ht hu) →
      Disjoint ht hu → Le (union hc (union ht hu)) (frag I m) →
      ∃ fin, Reaches I.step m fin ∧ (I.core fin).rip = ret ∧
        (I.core fin).read .rsp = sp + 8#64 ∧
        (∀ r ∈ sysv64.calleeSaved, (I.core fin).read r = (I.core m).read r) ∧
        (I.mem m).WritesWithin (I.mem fin) (fun a => (union ht hu (.mem a)).isSome) ∧
        S.post x ((I.core fin).read .rax) (reval hu (frag I fin))) :
    S.SatWith I A C entry :=
  Silmaril.Proofs.X86.SepSysV.satWith_of_runs h

/-- The return slot of the entry template. -/
theorem FnSpec.sysVEntry_ret {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag}
    {m : MState} (hT : S.SysVEntry x entry sp ret h) (hl : Le h (toFrag m)) :
    m.memory.readBytes sp.toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [ret]) :=
  Silmaril.Proofs.X86.SepContract.sysVEntry_ret hT hl

theorem FnSpec.sysVEntry_rsp {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag}
    {m : MState} (hT : S.SysVEntry x entry sp ret h) (hl : Le h (toFrag m)) :
    m.core.read .rsp = sp :=
  Silmaril.Proofs.X86.SepContract.sysVEntry_rsp hT hl

theorem FnSpec.sysVEntry_rip {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag}
    {m : MState} (hT : S.SysVEntry x entry sp ret h) (hl : Le h (toFrag m)) :
    m.core.rip = entry :=
  Silmaril.Proofs.X86.SepContract.sysVEntry_rip hT hl

/-- The argument registers hold the arguments. -/
theorem FnSpec.sysVEntry_args {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag}
    {m : MState} (hT : S.SysVEntry x entry sp ret h) (hl : Le h (toFrag m)) (i : Nat)
    (h₁ : i < argRegs.length) (h₂ : i < (S.args x).length) :
    m.core.read argRegs[i] = (S.args x)[i] :=
  Silmaril.Proofs.X86.SepContract.sysVEntry_args hT hl i h₁ h₂

/-- Reading a returned state off the postcondition template. -/
theorem FnSpec.sysVPost_le {S : FnSpec} {C : SProp} {x : S.Arg} {sp ret : Word} {h : Frag}
    {m : MState} (hq : (C ∗ S.SysVPost x sp ret) h) (hl : Le h (toFrag m)) :
    ∃ v, m.core.rip = ret ∧ m.core.read .rsp = sp + 8#64 ∧ m.core.read .rax = v ∧
      Holds (S.post x v) m :=
  Silmaril.Proofs.X86.SepContract.sysVPost_le hq hl

/-- **A System V spec from a function contract** on any segment-VC machine. -/
theorem FnSpec.sat_of_fnContract {S : FnSpec} {C : SProp} {entry : Word} (K : FnContract I)
    (h : ∀ x sp ret (m : σ) (hc ht hu : Frag), FnSpec.EntryAligned sp →
      S.stack ≤ sp.toNat → C hc → S.SysVEntry x entry sp ret ht → S.pre x hu →
      Disjoint hc (union ht hu) → Disjoint ht hu → Le (union hc (union ht hu)) (frag I m) →
      K.entry m ∧ (∀ a, K.footprint m a → (union ht hu (.mem a)).isSome) ∧
        ∀ fin, K.post m fin → S.post x ((I.core fin).read .rax) (reval hu (frag I fin))) :
    S.Sat I C entry :=
  Silmaril.Proofs.X86.SepContract.sat_of_fnContract K h

/-- A System V spec is a total function-contract spec on a `Flat` machine. -/
theorem FnSpec.Sat.total {S : FnSpec} {C : SProp} {entry : Word} (hflat : Flat I)
    (hS : S.Sat I C entry) : (S.contractSpec I C entry).Total I :=
  Silmaril.Proofs.X86.SepContract.total_of_sat hflat hS

/-- **`SPEC → FnContract`**: a System V spec as a total function contract on a `Flat`
machine. -/
def FnSpec.Sat.toFnContract {S : FnSpec} {C : SProp} {entry : Word} (hflat : Flat I)
    (hS : S.Sat I C entry) : FnContract I :=
  ⟨S.contractSpec I C entry, hS.total hflat⟩

/-! ## The open machines are flat -/

theorem flat_open : Flat Open.isa := fun _ _ => rfl
theorem flat_open9 : Flat Open9.isa := fun _ _ => rfl
theorem flat_str9 : Flat Str9.isa := fun _ _ => rfl

end Silmaril.X86.Sep
