module

public import Silmaril.X86.Sep.CSpec.Defs
public import Silmaril.X86.Sep.Xmm.Thms
public import Silmaril.X86.Sep.Ind.Defs
public import Silmaril.X86.Safe.Defs
public import Silmaril.X86.Link.Env.Defs
public import Silmaril.X86.Stencils.ByteLoop.Defs
public import Silmaril.X86.Ladder.LibMini.Defs
public import Silmaril.X86.Sep.Demo.Thms
import Silmaril.Proofs.X86.Sep.CSpec.Template
import Silmaril.Proofs.X86.Sep.CSpec.Call
import Silmaril.Proofs.X86.Sep.CSpec.Bridge
import Silmaril.Proofs.X86.Sep.CSpec.NonVacuity
/-!
# `CSpec`: call rules, refinement and the `FnSpec` embedding

PROVED (standard axioms; proofs in `Silmaril/Proofs/Machine/X86/Sep/CSpec/{Template,Call,Bridge}`).
**Sequencing on XMM machines.** `XSTriple.seq`; `XSTriple.progress_seq` (a step pays for the
index); `XProgress.frame`, `XProgress.conseq`; `xprogress_of_progress` (an `Open9` progress
law holds on every XMM machine extending `Open9`).

**Refinement.** `CSpec.SatN.zero`, `mono`, `code_frame`, **`CSpec.SatN.sub`** (code meeting
`S` meets every `T` with `S ⊑ T`), `CSpec.Sat.sub`, `CSpec.Sub.refl`, `CSpec.Sub.trans`.

**Call rules** (any XMM machine `M` with `[ExtendsOpen9X M]`, e.g. `Sse9.step`):
* **`CSpec.ccall_rule`** (`call rel32`): from the callee's `CSpec.Sat`, a 16-byte-aligned call
  site `s` with `S.stack x + 8` bytes of room below it, the caller's `ArgsIn` and `pre` at the
  callee frame `⟨s - 8, pc + 5⟩`, the call behaves as one instruction that returns `RetOut`
  and `post` for some result bytes. Callee-saved registers and everything else the caller
  owns are in the frame.
* **`CSpec.cicall_safe`** (`call *%r`, callee-safe form): from `CSpec.SatN M n C p`, a
  triple at `n + 1`. The call instruction is part of the code `C` (`hC`), and the target
  register with the rest `X` of the caller's state hands over `ArgsIn` and `pre`, leaving `K`.
* **`CSpec.cicall_rule`** (`call *%r` through a function pointer): the same with CP-3/LK1's
  `FnPtr` and `Env.Safe` at `Spec := CSpec`, for the code-fixed logic `CSpec.logicAt M C`
  (`Safe n a S _ := S.SatN M n C a`; it ignores the image). The image-based logic
  (`SafeOnC`, `logicC`) is CP-11's.

**The `FnSpec` embedding.** `CSpec.argsIn_intShape`, `CSpec.retOut_intShape`, `CSpec.toC_pre`,
`CSpec.toC_post`; **`CSpec.sat_toC_of_sat`**: `S.Sat Open.isa C entry → S.toC.Sat M ↑ₓC entry`, so
every existing `FnSpec` proof is a `CSpec` proof on every XMM machine extending `Open9`;
`CSpec.toC_sub`. **`CSpec.intPlan_eq_plan`**: `FnSpec.toC`'s plan is what `Abi.plan` computes
for up to six 64-bit INTEGER arguments. **`CSpec.strlen_csat`** (acceptance): libmini's
`strlen` meets `scanSpec.toC` on `Sse9.isa`.

**Words as bytes.** `CSpec.wordBytes_inj`, `CSpec.chunksPt_gp8` (a one-word GP chunk is a
register atom).

**Non-vacuity** (CP-10b review). `CSpec.xholds_lift_xmmsAll` (an integer assertion holding of
a machine state, with all sixteen XMM registers beside it); `CSpec.leaf_toC_pre_satisfiable`:
a concrete `XState` carries the leaf's code and its whole `FnSpec.toC` precondition (entry
template with every XMM register, and user precondition). Non-vacuity of `Entry` for a plan
with vector, stack, sret or `al` placement is **not** proved.
-/

@[expose] public section

namespace Silmaril.X86.Sep

open Silmaril.X86 (Reg XReg Word Byte MState Insn)
open Silmaril.X86.Sse9 (XState)
open Silmaril.X86.Sep.Xmm
open Silmaril.X86.Sep.Plan
open Silmaril.X86.Sep.Ind (encCallR nextPc)
open Silmaril.X86.Link.Env (Env FnPtr)

/-! ## Sequencing on XMM machines -/

theorem Xmm.XSTriple.seq {M : Silmaril.X86.SegVC.Isa XState} {n : Nat} {P Q R : XSProp}
    (h₁ : XSTriple M n P Q) (h₂ : XSTriple M n Q R) : XSTriple M n P R :=
  Silmaril.Proofs.X86.SepCSpec.XSTriple.seq h₁ h₂

theorem Xmm.XSTriple.progress_seq {M : Silmaril.X86.SegVC.Isa XState} {n : Nat} {P R Q : XSProp}
    (h₁ : XProgress M P R) (h₂ : XSTriple M n R Q) : XSTriple M (n + 1) P Q :=
  Silmaril.Proofs.X86.SepCSpec.XSTriple.progress_seq h₁ h₂

theorem XProgress.frame {M : Silmaril.X86.SegVC.Isa XState} {P R : XSProp}
    (h : XProgress M P R) (G : XSProp) : XProgress M (P ∗ₓ G) (R ∗ₓ G) :=
  Silmaril.Proofs.X86.SepCSpec.XProgress.frame h G

theorem XProgress.conseq {M : Silmaril.X86.SegVC.Isa XState} {P P' R R' : XSProp}
    (hp : P' ⊢ₓ P) (h : XProgress M P R) (hr : R ⊢ₓ R') : XProgress M P' R' :=
  Silmaril.Proofs.X86.SepCSpec.XProgress.conseq hp h hr

/-- An `Open9` progress law holds on every XMM machine extending `Open9`. -/
theorem xprogress_of_progress {M : Silmaril.X86.SegVC.Isa XState} [ExtendsOpen9X M]
    {P R : SProp} (h : Silmaril.X86.Safe.Progress Silmaril.X86.Open9.isa P R) :
    XProgress M (lift P) (lift R) :=
  Silmaril.Proofs.X86.SepCSpec.xprogress_of_progress h

namespace CSpec

/-! ## Words as bytes -/

theorem wordBytes_inj {v w : Word} (h : wordBytes v = wordBytes w) : v = w :=
  Silmaril.Proofs.X86.SepCSpec.wordBytes_inj h

/-- A one-word GP chunk is a register atom. -/
theorem chunksPt_gp8 (r : Reg) (w : Word) :
    chunksPt (wordBytes w) [⟨0, 8, .gp r⟩] = ↑ₓ(regPt r w) :=
  Silmaril.Proofs.X86.SepCSpec.chunksPt_gp8 r w

/-! ## Refinement -/

section Sat

variable {M : Silmaril.X86.SegVC.Isa XState} {C : XSProp} {entry : Word}

theorem SatN.zero (S : CSpec) : S.SatN M 0 C entry :=
  Silmaril.Proofs.X86.SepCSpec.SatN.zero S

theorem SatN.mono {n : Nat} {S : CSpec} (h : S.SatN M (n + 1) C entry) :
    S.SatN M n C entry :=
  Silmaril.Proofs.X86.SepCSpec.SatN.mono h

theorem SatN.code_frame {n : Nat} {S : CSpec} (h : S.SatN M n C entry) (D : XSProp) :
    S.SatN M n (C ∗ₓ D) entry :=
  Silmaril.Proofs.X86.SepCSpec.SatN.code_frame h D

/-- **Refinement**: code meeting `S` for `n` steps meets every `T` with `S ⊑ T`. -/
theorem SatN.sub {n : Nat} {S T : CSpec} (h : S.SatN M n C entry) (hsub : S.Sub T) :
    T.SatN M n C entry :=
  Silmaril.Proofs.X86.SepCSpec.SatN.sub h hsub

theorem Sat.sub {S T : CSpec} (h : S.Sat M C entry) (hsub : S.Sub T) :
    T.Sat M C entry :=
  fun n => (h n).sub hsub

theorem Sat.code_frame {S : CSpec} (h : S.Sat M C entry) (D : XSProp) :
    S.Sat M (C ∗ₓ D) entry :=
  fun n => (h n).code_frame D

end Sat

theorem Sub.refl (S : CSpec) : S.Sub S := Silmaril.Proofs.X86.SepCSpec.Sub.refl S

theorem Sub.trans {S T U : CSpec} (h₁ : S.Sub T) (h₂ : T.Sub U) : S.Sub U :=
  Silmaril.Proofs.X86.SepCSpec.Sub.trans h₁ h₂

/-! ## The code-fixed logic -/

/-- **The `CSpec` logic for a fixed code assertion `C`**: the code at `a` meets `S` for `n`
steps with code `C` (the image is not consulted). It instantiates CP-3/LK1's `FnPtr` and
`Env.Safe` at `Spec := CSpec`. -/
def logicAt (M : Silmaril.X86.SegVC.Isa XState) (C : XSProp) :
    Silmaril.X86.Link.Contract.Logic CSpec where
  Safe n a S _ := S.SatN M n C (BitVec.ofNat 64 a)
  zero _ S _ := SatN.zero S
  mono h := SatN.mono h
  frame _ h := h
  Sub := Sub
  sub hs h := SatN.sub h hs

/-! ## Call rules -/

section Calls

variable {M : Silmaril.X86.SegVC.Isa XState} [ExtendsOpen9X M]

/-- **The direct call rule** (`call rel32` to code meeting `S`). -/
theorem ccall_rule {S : CSpec} {Cf : XSProp} {f pc s : Word} {rel : BitVec 32} (x : S.Arg)
    (hS : S.Sat M Cf f) (hf : pc + 5#64 + rel.signExtend 64 = f)
    (hal : s.toNat % 16 = 0) (hlow : S.stack x + 8 ≤ s.toNat) (n : Nat) :
    XSTriple M n
      (↑ₓ(codePt pc.toNat (Insn.encode (.call rel))) ∗ₓ Cf ∗ₓ
        ↑ₓ(ripPt pc ∗ regPt .rsp s ∗ flagsAny ∗
          blockAny (s.toNat - 8 - S.stack x) (S.stack x + 8)) ∗ₓ
        ArgsIn (S.shape x) ⟨s - 8#64, pc + 5#64⟩ ∗ₓ S.pre x ⟨s - 8#64, pc + 5#64⟩)
      (↑ₓ(codePt pc.toNat (Insn.encode (.call rel))) ∗ₓ Cf ∗ₓ xsexists fun rb =>
        ↑ₓ(ripPt (pc + 5#64) ∗ regPt .rsp s ∗ flagsAny ∗
          blockAny (s.toNat - 8 - S.stack x) (S.stack x + 8)) ∗ₓ
        RetOut (S.shape x) ⟨s - 8#64, pc + 5#64⟩ rb ∗ₓ S.post x ⟨s - 8#64, pc + 5#64⟩ rb) :=
  Silmaril.Proofs.X86.SepCSpec.ccall_rule x hS hf hal hlow n

/-- **The indirect call rule** (`call *%r`), callee-safe form. -/
theorem cicall_safe {S : CSpec} {C Cr X K : XSProp} {r : Reg} {pc s p : Word} {n : Nat}
    (x : S.Arg) (hS : S.SatN M n C p)
    (hC : C = (↑ₓ(codePt pc.toNat (encCallR r)) ∗ₓ Cr))
    (hal : s.toNat % 16 = 0) (hlow : S.stack x + 8 ≤ s.toNat)
    (hho : (↑ₓ(regPt r p) ∗ₓ X) ⊢ₓ
      (ArgsIn (S.shape x) ⟨s - 8#64, nextPc pc (encCallR r)⟩ ∗ₓ
        S.pre x ⟨s - 8#64, nextPc pc (encCallR r)⟩ ∗ₓ K)) :
    XSTriple M (n + 1)
      (C ∗ₓ ↑ₓ(ripPt pc ∗ regPt .rsp s ∗ flagsAny ∗
          blockAny (s.toNat - 8 - S.stack x) (S.stack x + 8)) ∗ₓ ↑ₓ(regPt r p) ∗ₓ X)
      (C ∗ₓ (xsexists fun rb =>
        ↑ₓ(ripPt (nextPc pc (encCallR r)) ∗ regPt .rsp s ∗ flagsAny ∗
          blockAny (s.toNat - 8 - S.stack x) (S.stack x + 8)) ∗ₓ
        RetOut (S.shape x) ⟨s - 8#64, nextPc pc (encCallR r)⟩ rb ∗ₓ
        S.post x ⟨s - 8#64, nextPc pc (encCallR r)⟩ rb) ∗ₓ K) :=
  Silmaril.Proofs.X86.SepCSpec.cicall_safe x hS hC hal hlow hho

/-- **The indirect call rule through a function pointer** (`call *%r`): `p` is a code
pointer (`FnPtr`) into a code environment `Γ` that is safe for `n` steps in the code-fixed
logic; the call is a triple at `n + 1`. -/
theorem cicall_rule {Code : Type} {I : Env Code → Code → CSpec} {Γ : Env Code}
    {ctx : Silmaril.X86.Link.Contract.Image} {S : CSpec} {C Cr X K : XSProp} {r : Reg}
    {pc s p : Word} {n : Nat} (x : S.Arg)
    (hp : FnPtr (logicAt M C) I Γ p S) (hΓ : Silmaril.X86.Link.Env.Env.Safe
      (logicAt M C) I Γ n ctx)
    (hC : C = (↑ₓ(codePt pc.toNat (encCallR r)) ∗ₓ Cr))
    (hal : s.toNat % 16 = 0) (hlow : S.stack x + 8 ≤ s.toNat)
    (hho : (↑ₓ(regPt r p) ∗ₓ X) ⊢ₓ
      (ArgsIn (S.shape x) ⟨s - 8#64, nextPc pc (encCallR r)⟩ ∗ₓ
        S.pre x ⟨s - 8#64, nextPc pc (encCallR r)⟩ ∗ₓ K)) :
    XSTriple M (n + 1)
      (C ∗ₓ ↑ₓ(ripPt pc ∗ regPt .rsp s ∗ flagsAny ∗
          blockAny (s.toNat - 8 - S.stack x) (S.stack x + 8)) ∗ₓ ↑ₓ(regPt r p) ∗ₓ X)
      (C ∗ₓ (xsexists fun rb =>
        ↑ₓ(ripPt (nextPc pc (encCallR r)) ∗ regPt .rsp s ∗ flagsAny ∗
          blockAny (s.toNat - 8 - S.stack x) (S.stack x + 8)) ∗ₓ
        RetOut (S.shape x) ⟨s - 8#64, nextPc pc (encCallR r)⟩ rb ∗ₓ
        S.post x ⟨s - 8#64, nextPc pc (encCallR r)⟩ rb) ∗ₓ K) := by
  obtain ⟨c, hc, hsub⟩ := hp
  have h : S.SatN M n C (BitVec.ofNat 64 p.toNat) := SatN.sub (hΓ _ c hc) hsub
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  exact cicall_safe x h hC hal hlow hho

end Calls

/-! ## The `FnSpec` embedding -/

/-- The integer entry placement is `SysVRegs`, with all XMM registers. -/
theorem argsIn_intShape (args : List Word) (fr : Frame) :
    ArgsIn (intShape args) fr = (↑ₓ(SysVRegs args) ∗ₓ xmmsAny allXRegs) :=
  Silmaril.Proofs.X86.SepCSpec.argsIn_intShape args fr

/-- The integer exit placement for the result word `v`. -/
theorem retOut_intShape (args : List Word) (fr : Frame) (v : Word) :
    RetOut (intShape args) fr (wordBytes v) =
      (↑ₓ(regPt .rax v ∗ regsAny [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11]) ∗ₓ
        xmmsAny allXRegs) :=
  Silmaril.Proofs.X86.SepCSpec.retOut_intShape args fr v

/-- The precondition of `S.toC` is `S`'s System V precondition with all XMM registers. -/
theorem toC_pre (S : FnSpec) (x : S.Arg) (entry : Word) (fr : Frame) :
    S.toC.Pre x entry fr = (↑ₓ(S.SysVPre x entry fr.sp fr.ret) ∗ₓ xmmsAny allXRegs) :=
  Silmaril.Proofs.X86.SepCSpec.toC_pre S x entry fr

/-- `S`'s System V postcondition with all XMM registers gives `S.toC`'s. -/
theorem toC_post (S : FnSpec) (x : S.Arg) (fr : Frame) :
    (↑ₓ(S.SysVPost x fr.sp fr.ret) ∗ₓ xmmsAny allXRegs) ⊢ₓ S.toC.Post x fr :=
  Silmaril.Proofs.X86.SepCSpec.toC_post S x fr

/-- **Every `FnSpec` proof is a `CSpec` proof** on every XMM machine extending `Open9`. -/
theorem sat_toC_of_sat {M : Silmaril.X86.SegVC.Isa XState} [ExtendsOpen9X M] {S : FnSpec}
    {C : SProp} {entry : Word} (hS : S.Sat Silmaril.X86.Open.isa C entry) : S.toC.Sat M ↑ₓC entry :=
  Silmaril.Proofs.X86.SepCSpec.sat_toC_of_sat hS

/-- `FnSpec.toC` preserves refinement. -/
theorem toC_sub {S T : FnSpec} (h : S.Sub T) : S.toC.Sub T.toC :=
  Silmaril.Proofs.X86.SepCSpec.toC_sub h

/-- `FnSpec.toC`'s plan is `Abi.plan`'s for up to six 64-bit INTEGER arguments and a 64-bit
INTEGER result. -/
theorem intPlan_eq_plan (args : List Word) (h : args.length ≤ 6) :
    (Silmaril.Machine.SystemV.Abi.plan {} (List.replicate args.length int64Object)
      (some int64Object) args.length false).toOption = some (intPlan args) :=
  Silmaril.Proofs.X86.SepCSpec.intPlan_eq_plan args h

open Silmaril.X86.Stencils.ByteLoop Silmaril.X86.Ladder.LibMini in
/-- **Acceptance (CP-10b)**: libmini's `strlen` meets `scanSpec.toC` on `Sse9.isa`, from
`SpecNotions.strlen_spine`'s author spec, with no re-proof. -/
theorem strlen_csat (entry : Word) :
    scanSpec.toC.Sat Silmaril.X86.Sse9.isa ↑ₓ(codePt entry.toNat strlenCode) entry :=
  Silmaril.Proofs.X86.SepCSpec.strlen_csat entry

/-! ## Non-vacuity -/

/-- An integer assertion that holds of `m`, with all sixteen XMM registers beside it. -/
theorem xholds_lift_xmmsAll {P : SProp} {m : MState} (v : Silmaril.X86.Sse9.XFile)
    (hp : Holds P m) : XHolds (lift P ∗ₓ xmmsAny allXRegs) ⟨m, v⟩ :=
  Silmaril.Proofs.X86.SepCSpec.xholds_lift_xmmsAll v hp

/-- **Non-vacuity of the `toC` template**: a concrete XMM machine state carries the leaf's
code and its whole `FnSpec.toC` precondition (`CSpec.Pre`). -/
theorem leaf_toC_pre_satisfiable : ∃ x : XState,
    XHolds (↑ₓ(codePt (0x400000 : Word).toNat Silmaril.X86.Leaf.bytes) ∗ₓ
      Silmaril.X86.Sep.Demo.leafSpec.toC.Pre ((2 : Word), (3 : Word)) 0x400000
        ⟨0x7000, 0x401000⟩) x :=
  Silmaril.Proofs.X86.SepCSpec.leaf_toC_pre_satisfiable

end CSpec

end Silmaril.X86.Sep
