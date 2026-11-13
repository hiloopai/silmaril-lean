module

public import Silmaril.X86.SegVC
public import Silmaril.X86.Features.Cpuid.Dispatch

/-!
# The segment VC generator on a processor profile

`Profile.isa p exit` is the `SegVC.Isa` of the feature-parametric machine of the
profile `p`: its steps are `Features.stepOpt p.features [sysExt p] exit`, on the
extended state, so a segment proved with it is a run of the real machine of `p`,
CPUID and XGETBV answering as `p` does and every instruction gated by
`p.features`. It is an `Isa.ofExt` instance, so `seg_vc` applies unchanged:

* its listed instructions are `X86.Ext`'s, and an instruction's side condition
  (`ok`) is its feature check `baseCheck p.features i = none` (POPCNT, LZCNT,
  TZCNT) together with `Isa.ext`'s "a RET does not pop the exit";
* CPUID is not an `X86.Ext` instruction: it enters a segment as a *summary*
  (`cpuidSub`, for SegVC's `subs`) whose run is one step of `sysExt p`
  (`step_cpuid`).

The law `step_of` (`stepOpt_of_loaded`) is the integer machine's
`Ext.step_of_loaded` lifted by `Features.step_of_base`.

A dispatch proof is then one `seg_vc` over the whole function, for an arbitrary
profile: at the branch on the tested bit, the VC of the instruction that needs
the feature asks for `baseCheck p.features i = none`, which the path condition
gives through `Profile.popcnt_test` (and the other `Dispatch.lean` lemmas) on a
consistent profile.
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.SegVC
open Silmaril.Process (Memory)

/-- An `X86.Ext` instruction of a loaded image, executed by the feature machine. -/
theorem stepOpt_of_loaded {F : FeatureSet} {exts : List Extension} {exit : Word} {s : MState}
    {base : Word} {code : List Byte} {o l : Nat} {i : Ext.Instr} {c : X86.State} {m : Memory}
    (hl : Loaded s.memory base code) (hrip : s.state.core.rip = base + BitVec.ofNat 64 o)
    (hfit : o + l ≤ code.length) (hdec : Ext.decode ((code.drop o).take l) = some (i, l))
    (hx : Ext.exec i s.state.core s.memory l = .ok c m) (hb : baseCheck F i = none)
    (hret : ¬ (i = .ret ∧ c.rip = exit)) :
    stepOpt F exts exit s = some ⟨s.state.setCore c, m⟩ := by
  obtain ⟨hlen, hpos, -, -⟩ := Ext.decode_length hdec
  have hfetched : s.memory.fetchBytes s.state.core.rip.toNat l = some ((code.drop o).take l) := by
    rw [hrip, hl.toNat_add (by omega)]
    exact hl.fetchBytes_sub hpos hfit
  have hf : Ext.fetch s.memory s.state.core.rip.toNat = .decoded i l :=
    Ext.fetch_eq_decoded_iff.mpr ⟨_, hfetched, hdec⟩
  have hbase := Ext.step_of_loaded (exit := exit) (m := s.toBase) hl hrip hfit hdec
  rw [stepOpt_eq_some_iff, step_of_base hf, hb]
  simp only
  rw [hbase]
  subst hlen
  have hx' : Ext.exec i s.toBase.core s.toBase.memory = .ok c m := hx
  rw [hx']
  simp only [hret, ite_false]
  rfl

/-- The segment VC machine of a profile. -/
@[reducible] def Profile.isa (p : Profile) (exit : Word) : Isa MState :=
  Isa.ofExt (fun s => s.state.core) MState.memory (fun s c m => ⟨s.state.setCore c, m⟩)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    (fun i c => baseCheck p.features i = none ∧ ¬ (i = .ret ∧ c.rip = exit)) (fun _ => True)
    (stepOpt p.features [sysExt p] exit) (fun _ _ => trivial) (by
      intro s base code o l i c m _ hl hrip hfit hdec hx hok
      exact stepOpt_of_loaded hl hrip hfit hdec hx hok.1 hok.2)

/-- The successor of a CPUID at `s`. -/
def cpuidNext (p : Profile) (s : MState) : MState :=
  ⟨(s.state.setCore (Ext.Wire.cpuidState p.platform s.state.core)).advance 2, s.memory⟩

/-- CPUID at offset `o` of a loaded image, as a summary: one step of `sysExt p`. -/
def cpuidSub (p : Profile) (exit base : Word) (code : List Byte) (o : Nat)
    (hcode : (code.drop o).take 2 = [0x0F, 0xA2]) (hfit : o + 2 ≤ code.length) :
    Call (p.isa exit) where
  pre s := Loaded s.memory base code ∧ s.state.core.rip = base + BitVec.ofNat 64 o
  post s t := t = cpuidNext p s
  runs := by
    rintro s - ⟨hl, hrip⟩
    refine ⟨_, reaches_head (I := p.isa exit) ?_, rfl⟩
    show stepOpt p.features [sysExt p] exit s = some (cpuidNext p s)
    rw [stepOpt_eq_some_iff]
    apply step_cpuid (List.pairwise_singleton _ _) (List.mem_singleton_self _)
    rw [hrip, hl.toNat_add (by omega), ← hcode]
    exact hl.fetchBytes_sub (by decide) hfit

@[simp] theorem cpuidNext_core (p : Profile) (s : MState) :
    (cpuidNext p s).state.core =
      { Ext.Wire.cpuidState p.platform s.state.core with
        rip := s.state.core.rip + BitVec.ofNat 64 2 } := rfl

@[simp] theorem cpuidNext_memory (p : Profile) (s : MState) :
    (cpuidNext p s).memory = s.memory := rfl

end Silmaril.X86.Features
