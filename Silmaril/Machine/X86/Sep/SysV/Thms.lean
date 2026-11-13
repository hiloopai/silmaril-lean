module

public import Silmaril.Machine.X86.Sep.SysV.Defs
public import Silmaril.Machine.X86.Sep.Spec.Thms
public import Silmaril.Machine.X86.FnContract.Thms
public import Silmaril.Machine.X86.Sep.Contract.Defs
import Silmaril.Proofs.Machine.X86.Sep.Call
import Silmaril.Proofs.Machine.X86.Sep.SysV
import Silmaril.Proofs.Machine.X86.Sep.Contract

/-!
# System V specs: the call rule, frames, refinement and contracts

* `call_step`, `ret_step`: the `call rel32` and `ret` triples on the open machine.
* `call_rule`: **calling a function that meets `S`.** A `call rel32` to the callee's entry,
  from a 16-byte-aligned (or `A`-admissible) stack pointer `s` with `S.stack + 8` bytes of
  budget below it, behaves as one instruction that consumes the arguments and returns
  `rax ↦ v` with `S.post`. It is derived from `call_step`, the callee's `SatWith` and the frame
  rule; nothing else of the caller is touched.
* `calleeSaved_by_frame`: callee-saved registers (and anything else the caller owns) survive a
  call because they are in the frame, not in the template.
* `FnSpec.Sub.refl`, `FnSpec.Sub.trans`, `FnSpec.SatWith.mono`: refinement of specs.
* `FnSpec.satWith_of_runs`: a spec from returning open-machine runs (the bridge for existing
  proofs). `FnSpec.sat_of_fnContract`: a spec from a WP3 `FnContract` on the open machine.
* `FnSpec.Sat.toFnContract`: a spec as a total WP3 `FnContract` on the open machine (and so,
  through `FnContract.toRealizes`/`toFfiRealizes`, as a System V `Realizes` certificate),
  when its precondition's fragments own neither the mappings nor a callee-saved register.
-/

@[expose] public section

namespace Silmaril.Machine.X86.Sep

open Silmaril.X86 (State MState Word Byte Reg Insn sysv64)
open Silmaril.Machine.Execution (Reaches)
open Frag (union Disjoint Le reval)

theorem calleeSavedRegs_eq : calleeSavedRegs = sysv64.calleeSaved := rfl

/-! ## Instructions -/

/-- **`call rel32`**: push the return address into the eight bytes below `rsp` and jump. -/
theorem call_step (pc s : Word) (rel : BitVec 32) (hs : 8 ≤ s.toNat) :
    Triple (codePt pc.toNat (Insn.encode (.call rel)) ∗ ripPt pc ∗ regPt .rsp s ∗
        blockAny (s.toNat - 8) 8)
      (codePt pc.toNat (Insn.encode (.call rel)) ∗ ripPt (pc + 5#64 + rel.signExtend 64) ∗
        regPt .rsp (s - 8#64) ∗ wordPt (s.toNat - 8) (pc + 5#64)) :=
  Silmaril.Proofs.Machine.X86.Sep.call_step pc s rel hs

/-- **`ret`**: pop the return address into `rip`. -/
theorem ret_step (q s r : Word) :
    Triple (codePt q.toNat (Insn.encode .ret) ∗ ripPt q ∗ regPt .rsp s ∗ wordPt s.toNat r)
      (codePt q.toNat (Insn.encode .ret) ∗ ripPt r ∗ regPt .rsp (s + 8#64) ∗
        wordPt s.toNat r) :=
  Silmaril.Proofs.Machine.X86.Sep.ret_step q s r

/-! ## The call rule -/

/-- **The call rule.** -/
theorem call_rule {A : Word → Prop} {S : FnSpec} {Cf : SProp} {f pc s : Word}
    {rel : BitVec 32} (x : S.Arg) (hS : S.SatWith A Cf f)
    (hf : pc + 5#64 + rel.signExtend 64 = f) (hA : A (s - 8#64))
    (hlow : S.stack + 8 ≤ s.toNat) :
    SPEC (codePt pc.toNat (Insn.encode (.call rel)) ∗ Cf)
      (ripPt pc ∗ regPt .rsp s ∗ SysVRegs (S.args x) ∗ flagsAny ∗
        blockAny (s.toNat - 8 - S.stack) (S.stack + 8) ∗ S.pre x)
      (sexists fun v => ripPt (pc + 5#64) ∗ regPt .rsp s ∗ SysVRet v ∗ flagsAny ∗
        blockAny (s.toNat - 8 - S.stack) (S.stack + 8) ∗ S.post x v) :=
  Silmaril.Proofs.Machine.X86.SepSysV.call_rule x hS hf hA hlow

/-- A 16-byte-aligned call site gives the callee an aligned entry. -/
theorem entryAligned_of_call {s : Word} (h : s.toNat % 16 = 0) (h8 : 8 ≤ s.toNat) :
    FnSpec.EntryAligned (s - 8#64) := by
  unfold FnSpec.EntryAligned
  rw [Silmaril.Proofs.Machine.X86.Sep.toNat_sub_eight h8]
  omega

/-- **Callee-saved registers by frame.** Whatever the caller owns besides the template —
in particular the callee-saved registers with their values — is returned unchanged. -/
theorem calleeSaved_by_frame {A : Word → Prop} {S : FnSpec} {C : SProp} {entry : Word}
    (hS : S.SatWith A C entry) (x : S.Arg) {sp ret : Word} (hA : A sp)
    (hst : S.stack ≤ sp.toNat) (vs : List Word) :
    SPEC C (S.SysVPre x entry sp ret ∗ regsWith calleeSavedRegs vs)
      (S.SysVPost x sp ret ∗ regsWith calleeSavedRegs vs) :=
  SPEC.frame (hS x sp ret hA hst) _

/-! ## Refinement -/

theorem FnSpec.Sub.refl (S : FnSpec) : S.Sub S :=
  ⟨le_refl _, fun y => ⟨y, rfl, emp, entails_of_eq (sep_emp _).symm,
    fun _ => entails_of_eq (sep_emp _)⟩⟩

theorem FnSpec.Sub.trans {S T U : FnSpec} (h₁ : S.Sub T) (h₂ : T.Sub U) : S.Sub U := by
  refine ⟨le_trans h₁.stack h₂.stack, fun z => ?_⟩
  obtain ⟨y, hy, R₂, hpre₂, hpost₂⟩ := h₂.arg z
  obtain ⟨x, hx, R₁, hpre₁, hpost₁⟩ := h₁.arg y
  refine ⟨x, hx.trans hy, R₁ ∗ R₂, ?_, fun v => ?_⟩
  · refine entails_trans hpre₂ (entails_trans (sep_mono_left R₂ hpre₁) ?_)
    exact entails_of_eq (sep_assoc _ _ _)
  · refine entails_trans (entails_of_eq (sep_assoc _ _ _).symm) ?_
    exact entails_trans (sep_mono_left R₂ (hpost₁ v)) (hpost₂ v)

/-- **Refinement**: a function meeting `S` meets every `T` with `S ⊑ T`. -/
theorem FnSpec.SatWith.mono {A : Word → Prop} {S T : FnSpec} {C : SProp} {entry : Word}
    (hS : S.SatWith A C entry) (hsub : S.Sub T) : T.SatWith A C entry :=
  Silmaril.Proofs.Machine.X86.SepSysV.sub_mono hS hsub

/-- A stronger stack-pointer assumption is a weaker spec. -/
theorem FnSpec.SatWith.weaken {A B : Word → Prop} {S : FnSpec} {C : SProp} {entry : Word}
    (hS : S.SatWith A C entry) (hBA : ∀ sp, B sp → A sp) : S.SatWith B C entry :=
  fun x sp ret hB hst => hS x sp ret (hBA sp hB) hst

theorem FnSpec.SatWith.code_frame {A : Word → Prop} {S : FnSpec} {C : SProp} {entry : Word}
    (hS : S.SatWith A C entry) (D : SProp) : S.SatWith A (C ∗ D) entry :=
  fun x sp ret hA hst => SPEC.code_frame (hS x sp ret hA hst) D

/-! ## Specs from runs and contracts -/

/-- **A System V spec from returning runs.** For every entry state whose fragment splits as
code `hc`, template `ht` and user part `hu`, a run on the open machine to the return address,
with `rsp` popped, callee-saved registers restored, memory written only inside the template
and the user part, and the user postcondition on the user part of the final state. -/
theorem FnSpec.satWith_of_runs {A : Word → Prop} {S : FnSpec} {C : SProp} {entry : Word}
    (h : ∀ x sp ret (m : MState) (hc ht hu : Frag), A sp → S.stack ≤ sp.toNat → C hc →
      S.SysVEntry x entry sp ret ht → S.pre x hu → Disjoint hc (union ht hu) →
      Disjoint ht hu → Le (union hc (union ht hu)) (toFrag m) →
      ∃ fin, Reaches Silmaril.Machine.X86.Open.step m fin ∧ fin.core.rip = ret ∧
        fin.core.read .rsp = sp + 8#64 ∧
        (∀ r ∈ sysv64.calleeSaved, fin.core.read r = m.core.read r) ∧
        m.memory.WritesWithin fin.memory (fun a => (union ht hu (.mem a)).isSome) ∧
        S.post x (fin.core.read .rax) (reval hu (toFrag fin))) :
    S.SatWith A C entry :=
  Silmaril.Proofs.Machine.X86.SepSysV.satWith_of_runs h

/-- The return slot of the entry template. -/
theorem FnSpec.sysVEntry_ret {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag}
    {m : MState} (hT : S.SysVEntry x entry sp ret h) (hl : Le h (toFrag m)) :
    m.memory.readBytes sp.toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [ret]) :=
  Silmaril.Proofs.Machine.X86.SepContract.sysVEntry_ret hT hl

theorem FnSpec.sysVEntry_rsp {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag}
    {m : MState} (hT : S.SysVEntry x entry sp ret h) (hl : Le h (toFrag m)) :
    m.core.read .rsp = sp :=
  Silmaril.Proofs.Machine.X86.SepContract.sysVEntry_rsp hT hl

theorem FnSpec.sysVEntry_rip {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag}
    {m : MState} (hT : S.SysVEntry x entry sp ret h) (hl : Le h (toFrag m)) :
    m.core.rip = entry :=
  Silmaril.Proofs.Machine.X86.SepContract.sysVEntry_rip hT hl

/-- The argument registers hold the arguments. -/
theorem FnSpec.sysVEntry_args {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag}
    {m : MState} (hT : S.SysVEntry x entry sp ret h) (hl : Le h (toFrag m)) (i : Nat)
    (h₁ : i < argRegs.length) (h₂ : i < (S.args x).length) :
    m.core.read argRegs[i] = (S.args x)[i] :=
  Silmaril.Proofs.Machine.X86.SepContract.sysVEntry_args hT hl i h₁ h₂

/-- Reading a returned state off the postcondition template. -/
theorem FnSpec.sysVPost_le {S : FnSpec} {C : SProp} {x : S.Arg} {sp ret : Word} {h : Frag}
    {m : MState} (hq : (C ∗ S.SysVPost x sp ret) h) (hl : Le h (toFrag m)) :
    ∃ v, m.core.rip = ret ∧ m.core.read .rsp = sp + 8#64 ∧ m.core.read .rax = v ∧
      Holds (S.post x v) m :=
  Silmaril.Proofs.Machine.X86.SepContract.sysVPost_le hq hl

/-- **A System V spec from a WP3 `FnContract`** on the open machine. -/
theorem FnSpec.sat_of_fnContract {S : FnSpec} {C : SProp} {entry : Word}
    (K : FnContract Silmaril.Machine.X86.Open.isa)
    (h : ∀ x sp ret (m : MState) (hc ht hu : Frag), FnSpec.EntryAligned sp →
      S.stack ≤ sp.toNat → C hc → S.SysVEntry x entry sp ret ht → S.pre x hu →
      Disjoint hc (union ht hu) → Disjoint ht hu → Le (union hc (union ht hu)) (toFrag m) →
      K.entry m ∧ (∀ a, K.footprint m a → (union ht hu (.mem a)).isSome) ∧
        ∀ fin, K.post m fin → S.post x (fin.core.read .rax) (reval hu (toFrag fin))) :
    S.Sat C entry :=
  Silmaril.Proofs.Machine.X86.SepContract.sat_of_fnContract K h

theorem FnSpec.Sat.total {S : FnSpec} {C : SProp} {entry : Word} (hS : S.Sat C entry) :
    (S.contractSpec C entry).Total Silmaril.Machine.X86.Open.isa :=
  Silmaril.Proofs.Machine.X86.SepContract.total_of_sat hS

/-- **`SPEC → FnContract`**: a System V spec as a total WP3 contract on the open machine. -/
def FnSpec.Sat.toFnContract {S : FnSpec} {C : SProp} {entry : Word} (hS : S.Sat C entry) :
    FnContract Silmaril.Machine.X86.Open.isa :=
  ⟨S.contractSpec C entry, hS.total⟩

end Silmaril.Machine.X86.Sep
