module

public import CompilesToExamples.Straight.Defs
public import CompilesToExamples.Straight.Proofs.Elaborates
public import Silmaril.Project.CompilesTo.Thms

/-! `examples/compiles-to/straight/straight.c`, `O2`, `add3`, segment 0 (function granularity:
from the call to the return). The Core runs the whole body (`FnData.core_straight`: create `s`
and `t`, `int s = a + b;`, `int t = s + c;`, `return t;`, the return label `pure(r)`) to the
value `(a + b) + c`, an `int` because the Core does not overflow (`Safe`); the machine runs
`add %esi,%edi; lea (%rdi,%rdx),%eax; ret` and returns with the 32-bit sum of the argument
registers in `eax`, which encodes that value. `FnData.segment_call` puts them together
(Core ↔ x86), and with C ↔ Core (C ↔ x86). -/

namespace CompilesToExamples.Straight.O2

open Silmaril.Project.CompilesTo Silmaril.Project.Shapes.CompilesTo
open Silmaril.Compiler.CompilesTo (Seg Hop)
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.Core.Verified
open Silmaril.X86.Ext (Mem Sz)
open Silmaril.X86.Lift (ix)
open StateMem (defsOf)
open StateExpr (values)

/-! ## The Core -/

/-- The symbol of `add3`'s object `name`: the C file's digest and Cerberus's number `n`. -/
def objSym (n : Nat) (name : String) : Sym :=
  ⟨⟨[0x42, 0x14, 0x5c, 0xf2, 0x6f, 0xbc, 0x46, 0x7b, 0xd1, 0x56, 0xcf, 0x1e, 0x7e, 0x91, 0x7a,
    0x78]⟩, n, .objectAddress name⟩

/-- The block's initialisations `int s = a + b;` and `int t = s + c;` (then `return t;`). -/
def inits : List (Sym × StateExpr.Key × StateExpr.Key) :=
  [(objSym 6 "s", (objSym 1 "a").key, (objSym 2 "b").key),
    (objSym 7 "t", (objSym 6 "s").key, (objSym 3 "c").key)]

/-- The value returned: `(a + b) + c`. -/
theorem vals_inits (σ : StateExpr.Key → Int) :
    valsAfter inits σ (objSym 7 "t").key =
      σ (objSym 1 "a").key + σ (objSym 2 "b").key + σ (objSym 3 "c").key := by
  have h : (objSym 3 "c").key ≠ (objSym 6 "s").key := by decide +kernel
  simp [valsAfter, inits, h]

theorem params_nodup : (add3.params.map (·.1.key)).Nodup := by decide +kernel

/-- The value of a parameter is its argument. -/
theorem param_val {vs : List Int} {i : Nat} (q : StateExpr.Key) {n : Int}
    (hq : (add3.params.map (·.1.key))[i]? = some q) (hv : vs[i]? = some n) :
    values (defsOf (Silmaril.Project.Shapes.C.CFn.paramDefs add3.params vs)) q = n := by
  show ((Silmaril.Project.Shapes.C.CFn.paramDefs add3.params vs q).getD (.lit 0)).val 0 = n
  rw [paramDefs_key params_nodup hq hv]
  rfl

/-- **The Core run of `add3`**: from a safe Core entry with the arguments `vs`, the Core returns
`(a + b) + c` (`valsAfter`), an `int`. -/
theorem core_run {k0 : List Frame} {vs : List Int} {s : State} (he : add3.CoreEntry k0 vs s)
    (hsafe : (add3.source k0).Safe s) :
    ∃ m', Relation.TransGen (add3.source k0).step s
        ⟨.value (IntExpr.spec (valsAfter inits (values (defsOf (Silmaril.Project.Shapes.C.CFn.paramDefs add3.params vs)))
          (objSym 7 "t").key)), .procedureReturn add3.bodyLabels :: k0, m'⟩ ∧
      ConvInt.IsInt (valsAfter inits (values (defsOf (Silmaril.Project.Shapes.C.CFn.paramDefs add3.params vs)))
        (objSym 7 "t").key) :=
  add3.core_straight (xs := [objSym 6 "s", objSym 7 "t"]) (inits := inits)
    (kv := (objSym 7 "t").key) (r := retParam add3.body)
    (hbody := rfl) (hcr := rfl) (hnodup := by decide +kernel) (hroom := by decide)
    (hstraight := by decide +kernel) (hdefd := by decide +kernel)
    (hlocals := by decide +kernel) (hlab := by decide +kernel) he hsafe

/-! ## The machine -/

/-- **The machine run of `add3`**: from the call, `add %esi,%edi; lea (%rdi,%rdx),%eax; ret`,
through no cut point, to the return, keeping the callee-saved registers and the memory, with
`eax` the 32-bit sum of `edi`, `esi` and `edx` at the call. -/
theorem machine_run (k0 : List Frame) {x0 : MState}
    {args : Silmaril.X86.SystemV.CApi.Arguments add3.sig.arguments}
    (hme : MachineEntry add3.sig add3.addr add3.code add3.frame args x0) :
    ∃ y, Seg (add3.corr Silmaril.X86.Open.isa k0).tgtStep
        ((add3.corr Silmaril.X86.Open.isa k0).tgtCut x0) x0 y ∧ Returned x0 y ∧
      ReturnFrame add3.frame x0 y ∧
      (y.core.read .rax).setWidth 32 = (x0.core.read .rdi).setWidth 32 +
        (x0.core.read .rsi).setWidth 32 + (x0.core.read .rdx).setWidth 32 := by
  -- `add %esi,%edi`
  have hrip0 : x0.core.rip = BitVec.ofNat 64 (add3.addr + 0) := hme.rip
  have hs1 := step_add32 (m := x0) (dst := .rdi) (src := .rsi) hme.loaded hrip0 (by decide)
    (by decide)
  let c1 : Silmaril.X86.State :=
    { Sz.d.write x0.core .rdi (Sz.d.read x0.core .rdi + Sz.d.read x0.core .rsi) with
      flags := Silmaril.X86.Ext.AluOp.flagsN .add (Sz.d.read x0.core .rdi)
        (Sz.d.read x0.core .rsi)
      rip := BitVec.ofNat 64 (add3.addr + 0 + 2) }
  have hrip1 : c1.rip = BitVec.ofNat 64 (add3.addr + 2) := rfl
  -- `lea (%rdi,%rdx),%eax`
  have hs2 := step_lea32 (m := ⟨c1, x0.memory⟩) (dst := .rax)
    (src := Mem.ofReg .rdi (some (ix .rdx 0)) 0x0) (l := 3) hme.loaded hrip1 (by decide)
    (by decide)
  let c2 : Silmaril.X86.State :=
    { Sz.d.write c1 .rax (((Mem.ofReg .rdi (some (ix .rdx 0)) 0x0).addr c1
        (BitVec.ofNat 64 (add3.addr + 2 + 3))).setWidth 32) with
      rip := BitVec.ofNat 64 (add3.addr + 2 + 3) }
  have hrsp1 : c1.read .rsp = x0.core.read .rsp :=
    dwrite_flags_rip_read_other x0.core .rdi .rsp _ _ _ (by decide)
  have hrsp2 : c2.read .rsp = x0.core.read .rsp :=
    (dwrite_rip_read_other c1 .rax .rsp _ _ (by decide)).trans hrsp1
  -- `ret`
  have hread : x0.memory.readBytes (c2.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords
        [Silmaril.X86.FnContract.retOf x0.core x0.memory]) := by
    rw [hrsp2]; exact hme.abi.returnAddress
  have hrip2 : (BitVec.ofNat 64 (add3.addr + 2 + 3) : BitVec 64) =
      BitVec.ofNat 64 add3.addr + BitVec.ofNat 64 5 := by decide
  have hs3 := step_ret (m := ⟨c2, x0.memory⟩) hme.loaded hrip2 (by decide) (by decide) hread
  -- The states inside are no cut points.
  have hnc1 : ¬ (add3.corr Silmaril.X86.Open.isa k0).tgtCut x0 ⟨c1, x0.memory⟩ :=
    add3.notCut_rsp0 (o := 2) hrip1 (by decide) (by decide) (by decide) (by decide) hrsp1
  have hnc2 : ¬ (add3.corr Silmaril.X86.Open.isa k0).tgtCut x0 ⟨c2, x0.memory⟩ :=
    add3.notCut_rsp0 (o := 5) rfl (by decide) (by decide) (by decide) (by decide) hrsp2
  -- The registers at the return.
  have hregs : ∀ r, r ≠ .rsp → r ≠ .rax → r ≠ .rdi →
      (afterRet ⟨c2, x0.memory⟩ (Silmaril.X86.FnContract.retOf x0.core x0.memory)).core.read r =
        x0.core.read r := fun r h1 h2 h3 =>
    ((Silmaril.X86.State.read_write_other _ _ _ _ h1).trans
      (dwrite_rip_read_other c1 .rax r _ _ h2)).trans
      (dwrite_flags_rip_read_other x0.core .rdi r _ _ _ h3)
  refine ⟨afterRet ⟨c2, x0.memory⟩ (Silmaril.X86.FnContract.retOf x0.core x0.memory),
    ⟨.more hs1 hnc1 (.more hs2 hnc2 (.one hs3)), Or.inr ⟨rfl, ?_⟩⟩, ⟨rfl, ?_⟩,
    ⟨?_, Silmaril.Process.Memory.WritesWithin.refl x0.memory _⟩, ?_⟩
  · simp [afterRet, hrsp2]
  · simp [afterRet, hrsp2]
  · intro r hr
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    refine hregs r ?_ ?_ ?_ <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · -- `eax`: the low half of `(edi + esi) + rdx`.
    show ((afterRet ⟨c2, x0.memory⟩ (Silmaril.X86.FnContract.retOf x0.core x0.memory)).core.read
      .rax).setWidth 32 = _
    have hrax : (afterRet ⟨c2, x0.memory⟩
        (Silmaril.X86.FnContract.retOf x0.core x0.memory)).core.read .rax = c2.read .rax := by
      simp [afterRet]
    have hc2rax : (c2.read .rax).setWidth 32 = ((Mem.ofReg .rdi (some (ix .rdx 0)) 0x0).addr c1
        (BitVec.ofNat 64 (add3.addr + 2 + 3))).setWidth 32 :=
      dwrite_read_self c1 .rax _
    have hc1rdi : c1.read .rdi =
        ((x0.core.read .rdi).setWidth 32 + (x0.core.read .rsi).setWidth 32).setWidth 64 :=
      Silmaril.X86.Ext.write_d_read x0.core .rdi _
    have hc1rdx : c1.read .rdx = x0.core.read .rdx :=
      dwrite_flags_rip_read_other x0.core .rdi .rdx _ _ _ (by decide)
    have haddr : (Mem.ofReg .rdi (some (ix .rdx 0)) 0x0).addr c1
        (BitVec.ofNat 64 (add3.addr + 2 + 3)) = c1.read .rdi + c1.read .rdx := by
      simp [Silmaril.X86.Ext.Mem.addr, Mem.ofReg, Silmaril.X86.Ext.Index.value, ix]
    rw [hrax, hc2rax, haddr, hc1rdi, hc1rdx]
    bv_omega

/-! ## The segment -/

/-- **Core ↔ x86**, segment 0 of `add3` (the call, to the return). -/
public theorem add3_seg_0 : Task.add3_seg_0 := by
  refine add3.segment_call Silmaril.X86.Open.isa rfl rfl ?_
  intro k0 x0 args s hme hce hsafe
  -- The arguments, in `edi`, `esi`, `edx`.
  obtain ⟨w1, hw1, hv1⟩ := argsAt_regs args 0 (by decide) hme.args 0 (by decide) (by decide)
  obtain ⟨w2, hw2, hv2⟩ := argsAt_regs args 0 (by decide) hme.args 1 (by decide) (by decide)
  obtain ⟨w3, hw3, hv3⟩ := argsAt_regs args 0 (by decide) hme.args 2 (by decide) (by decide)
  have hw1' : (x0.core.read .rdi).setWidth 32 = w1 := hw1
  have hw2' : (x0.core.read .rsi).setWidth 32 = w2 := hw2
  have hw3' : (x0.core.read .rdx).setWidth 32 = w3 := hw3
  -- The Core returns `(a + b) + c`.
  have hval : valsAfter inits (values (defsOf (Silmaril.Project.Shapes.C.CFn.paramDefs add3.params
      (Silmaril.Project.Shapes.C.argValues args)))) (objSym 7 "t").key = w1.toInt + w2.toInt + w3.toInt := by
    rw [vals_inits, param_val (objSym 1 "a").key (by decide +kernel) hv1,
      param_val (objSym 2 "b").key (by decide +kernel) hv2,
      param_val (objSym 3 "c").key (by decide +kernel) hv3]
  obtain ⟨m', hrun, hint⟩ := core_run hce hsafe
  rw [hval] at hrun hint
  -- The machine returns their 32-bit sum.
  obtain ⟨y, hseg, hret, hfr, hrax⟩ := machine_run k0 hme
  refine ⟨_, _, y, hrun, ⟨rfl, rfl⟩, hseg, hret, hfr, w1.toInt + w2.toInt + w3.toInt, rfl,
    BitVec.ofInt 32 (w1.toInt + w2.toInt + w3.toInt), ?_, ?_⟩
  · show (y.core.read .rax).setWidth 32 = _
    rw [hrax, hw1', hw2', hw3']
    simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  · show (BitVec.ofInt 32 (w1.toInt + w2.toInt + w3.toInt)).toInt = _
    obtain ⟨h1, h2⟩ := hint
    exact BitVec.toInt_ofInt_eq_self (by decide) (by norm_num; omega) (by norm_num; omega)

/-- **C ↔ x86**, segment 0 of `add3`: C ↔ Core (function and point) and Core ↔ x86. -/
public theorem add3_seg_0_from_c : Task.add3_seg_0_from_c :=
  ⟨elaborates_add3, add3_point_0, add3_seg_0⟩

end CompilesToExamples.Straight.O2
