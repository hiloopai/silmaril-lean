module

public import Silmaril.Machine.X86.Lir.Prologue.Defs

/-!
# Simulation of calls

`Env.sim_call`: a Lir call is matched by the code of the call site (save the
allocatable registers, load the arguments, `call rel32`) followed by the
prologue of the callee (`sim_entry`), which ends at the entry block of the
callee or at the UD2 of its stack-limit check.
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.Process (Memory)
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine
open Relation

set_option linter.unusedSectionVars false

namespace Env

variable {P : Type} (E : Env P) [DecidableEq P]

theorem enter_eq {g : Lir.FuncId} {vals : List Word} {pt : Lir.Point} {fr : Lir.Frame P}
    (h : E.p.enter g vals = some (pt, fr)) :
    ∃ fn, E.p.func? g = some fn ∧ Lir.Frame.empty.writeAll fn.params vals = some fr ∧
      pt = ⟨g, fn.entry, 0⟩ := by
  simp only [Lir.Prog.enter, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨fn, hfn, fr', hfr, rfl, rfl⟩ := h
  exact ⟨fn, hfn, hfr, rfl⟩

theorem retAddr_call {pt : Lir.Point} {g : Lir.FuncId} {args results : List (Lir.Loc P)}
    (h : E.p.fetch pt = some (.instr (.call g args results))) :
    E.retAddr pt = E.pa pt + E.callPrefix (E.ns pt.func) args := by
  simp [retAddr, h]

/-- The entry of an existing function lies in the code. -/
theorem func_in_code {g : Lir.FuncId} {fn : Lir.Func P} (hg : E.p.func? g = some fn) :
    ∃ o, E.L.func g = E.S.codeBase + o ∧ o ≤ E.code.length := by
  obtain ⟨post, hsplit⟩ := prologue_at E.A E.p hg
  refine ⟨_, layout_func E.A E.p E.S.codeBase g, ?_⟩
  have := lenOf_le hsplit
  rw [code, encodeAt_length]
  omega

theorem call_errors {pt : Lir.Point} {fn : Lir.Func P} {b : Lir.Block P} (hok : E.Ok)
    (hfn : E.p.func? pt.func = some fn) (hbl : fn.blocks[pt.label]? = some b)
    {g : Lir.FuncId} {args results : List (Lir.Loc P)}
    (hi : b.instrs[pt.index]? = some (.call g args results)) :
    args.length ≤ 6 ∧ results.length ≤ 2 ∧ g < E.p.funcs.length := by
  have := (funcOk hok.errors hfn).instrs b (instr_mem hbl hi).1 _ (instr_mem hbl hi).2
  simp only [instrErrors, List.append_eq_nil_iff] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  refine ⟨?_, ?_, ?_⟩
  · by_contra h; rw [ite_eq_right h] at h1; cases h1
  · by_contra h; rw [ite_eq_right h] at h2; cases h2
  · by_contra h; rw [ite_eq_right h] at h3; cases h3

/-- The call site: from a Lir call, the machine reaches the first instruction of
the callee with the arguments in their registers. -/
theorem sim_callSite (hok : E.Ok) {s : Lir.State P} {t : MState} {B : Nat} (hm : E.Body s t B)
    {g : Lir.FuncId} {args results : List (Lir.Loc P)} {vals : List Word}
    (hf : E.p.fetch s.point = some (.instr (.call g args results)))
    (ha : s.frame.readAll args = some vals) :
    ∃ t', TransGen (RStep E.exit) t t' ∧
      E.Entry g vals (⟨s.point, s.frame⟩ :: s.stack) s.mem t' (B - 8) := by
  have hv := hok.valid
  obtain ⟨fn, b, hfn, hbl, hi⟩ := E.fetch_instr hf
  have hlt : s.point.index < b.instrs.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨hargs, hres, hg⟩ := E.call_errors hok hfn hbl hi
  have hns := E.ns_eq hfn
  have hslots : ∀ k ∈ locSlots args, k < E.ns s.point.func := fun k hk => by
    rw [hns]; exact slot_lt hbl hi (by simp [instrSlots, hk])
  obtain ⟨hneed, hhi, hlo⟩ := E.frame_bounds hok hm hfn
  have hfit : Fits E.S B (E.ns s.point.func) := ⟨by omega, by omega, hneed⟩
  have hFg := Env.frameSize_ge (E.ns s.point.func)
  -- the code of the call
  have hci : s.point.index < (blockChunks E.A s.point.func (nslots fn) b).length := by
    rw [blockChunks_length]; omega
  obtain ⟨o', rest, hpa, hd, hbound⟩ := E.code_at hfn hbl hci
  have hchunk : (blockChunks E.A s.point.func (nslots fn) b)[s.point.index] =
      instrChunk E.A (nslots fn) (.call g args results) := by
    rw [blockChunks_instr E.A _ _ b hlt, (List.getElem?_eq_some_iff.mp hi).2]
  rw [hchunk] at hd
  simp only [instrChunk, encodeAt_append, encodeAt_plain, encodeAt, AInstr.resolve, List.append_nil,
    List.append_assoc] at hd
  rw [← hns] at hd
  -- save the registers and load the arguments
  obtain ⟨c₁, m₁, hr₁, hk₁, hreg₁, hw₁, hout₁⟩ :=
    run_saveAll hv hfit t.core t.memory hm.rsp hm.good.regions
  have hslots₁ : SlotsAt s.frame (E.ns s.point.func) B m₁ :=
    slotsAt_congr hm.slots (hi := B + 8 * E.ns s.point.func) le_rfl
      (fun x _ hx => hout₁ x (.inl hx))
  have hsaved : ∀ q v, s.frame.regs q = some v →
      WordAt m₁ (B + saveDisp (E.ns s.point.func) (E.A.idx q)) v := by
    intro q v hq
    have := hw₁ (E.A.idx q)
    rwa [show t.core.read (allocReg (E.A.idx q)) = v from hm.regs q v hq] at this
  obtain ⟨c₂, hr₂, hv₂, hk₂⟩ := run_argLoads hv E.A hfit (hreg₁.trans hm.good.regions) hsaved
    hslots₁ args 0 vals c₁ ha (by rw [hk₁, hm.rsp]) (by omega) hslots
  have hrun : runSeq (saveAll (E.ns s.point.func) ++ argLoads E.A (E.ns s.point.func) 0 args)
      t.core t.memory = some (c₂, m₁) := by
    rw [runSeq_append_of hr₁, hr₂]
  obtain ⟨i₀, is, hcons⟩ : ∃ i₀ is, saveAll (E.ns s.point.func) ++
      argLoads E.A (E.ns s.point.func) 0 args = i₀ :: is := ⟨_, _, rfl⟩
  rw [hcons] at hd hrun
  have hrip : t.core.rip.toNat = E.S.codeBase + o' := by
    rw [hm.rip, hpa, E.rip_toNat hok (by
      have := drop_len hd (by
        rw [List.flatMap_cons, List.length_append]
        have := (Ext.encode_length i₀).1; omega)
      omega)]
  obtain ⟨st₁, good₁, hrip₁⟩ := transGen_runSeq (exit := E.exit) hv hm.good hrip hd hrun
  have hd₁ := drop_after hd
  rw [lenOf_plain] at hd₁
  generalize hla : ((i₀ :: is).flatMap Ext.encode).length = la at hd₁ hrip₁
  have hb1 := drop_len hd₁ (Ext.encode_length _).1
  rw [show (Ext.encode (Ext.Instr.call (rel32 (E.L.func g) (E.pa s.point + la + 5)))).length = 5
    from rfl] at hb1
  have hcode := E.code_lt hok
  have hend := hv.code_end
  -- the CALL
  have hc₂rsp : c₂.read .rsp = BitVec.ofNat 64 B := by
    rw [hk₂ _ (fun i _ h => argRegN_ne_rsp (0 + i) h.symm), hk₁, hm.rsp]
  have hB : B < 2 ^ 64 := by have := hv.stack_end; omega
  obtain ⟨m₃, hpw, hw₃, hwo₃⟩ := push_at hv (hreg₁.trans hm.good.regions) hc₂rsp (by omega)
    (by omega) (c₂.rip + BitVec.ofNat 64 5)
  obtain ⟨og, hog, hogl⟩ := E.func_in_code (fn := E.p.funcs[g]) (List.getElem?_eq_getElem hg)
  have ex := exec_call_ok c₂ m₁ (rel32 (E.L.func g) (E.pa s.point + la + 5))
    (by rw [hpw, hc₂rsp, sub8_eq (by omega) hB])
  have hc₂rip : c₂.rip = BitVec.ofNat 64 (E.pa s.point + la) := by
    apply rip_of_toNat; rw [hrip₁, hpa]
  rw [hc₂rip, ← BitVec.ofNat_add, rel32_ok _ _ (by omega) (by omega), hc₂rsp,
    sub8_eq (by omega) hB] at ex
  have st₂ := rstep_code (exit := E.exit) (t := ⟨c₂, m₁⟩) hv good₁ (by rw [hrip₁]; omega) hd₁ ex
    (by intro h; cases h.1)
  refine ⟨_, TransGen.tail st₁ st₂, ?_⟩
  have hk₂' : ∀ r, (∀ i : Fin 6, r ≠ argReg i) → c₂.read r = t.core.read r := by
    intro r hr
    rw [hk₂ r (fun i hi h => by
      rw [zero_add, argRegN_lt (by omega)] at h; exact hr _ h), hk₁]
  have hB8 : B - 8 + 8 = B := by omega
  have hmem₃ : ∀ x, x < B - 8 ∨ B + 8 * E.ns s.point.func + 72 ≤ x →
      m₃.bytes.get? x = t.memory.bytes.get? x := by
    intro x hx
    rw [hwo₃.2 x (by omega), hout₁ x (by omega)]
  have hret : E.retAddr s.point = E.pa s.point + la + 5 := by
    rw [E.retAddr_call hf, callPrefix, lenOf_plain, hcons, hla]; omega
  have hal := hm.align
  refine ⟨good_of_exec hv good₁ ex, ?_, ?_, by simp, by omega, by omega, rfl, ?_, ?_, ?_⟩
  · simp only [read_rip, State.read_write_other _ _ _ _ (show Reg.r15 ≠ .rsp by decide)]
    rw [hk₂' _ (fun i => (argReg_ne_r15 i).symm), hm.r15]
  · simp only [read_rip, State.read_write_other _ _ _ _ (show Reg.r14 ≠ .rsp by decide)]
    rw [hk₂' _ (fun i => (argReg_ne_r14 i).symm), hm.r14]
  · refine hm.mem.congr fun x hx => hmem₃ x ?_
    simp only [Space.InMem] at hx
    have := hv.stack_mem; have := hm.mem.1
    omega
  · intro j hj
    simp only [read_rip, State.read_write_other _ _ _ _ (argRegN_ne_rsp j)]
    have := hv₂ j hj
    rwa [zero_add] at this
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hret]
      have := hw₃
      rwa [hc₂rip, ← BitVec.ofNat_add] at this
    · rw [hB8]
      exact slotsAt_congr hslots₁ (hi := B + 8 * E.ns s.point.func) le_rfl
        (fun x hx _ => hwo₃.2 x (by omega))
    · rw [hB8]
      refine ⟨fun k => ⟨_, (hw₁ k).of_writesOnly hwo₃ (by omega)⟩,
        fun q v hq => (hsaved q v hq).of_writesOnly hwo₃ (by omega)⟩
    · rw [hB8]
      refine E.chain_congr hm.chain (fun x hx _ => hmem₃ x (.inr ?_))
      have hx' : B + frameSize (E.ns s.point.func) ≤ x := hx
      omega

end Env

end Silmaril.X86.Backend
