module

public import Silmaril.Machine.X86.Lir.Entry.Defs

/-!
# Simulation of a function entry

`Env.sim_entry`: from `Env.Entry` (the machine at the first instruction of a
function, called with the argument values `vals`), the prologue runs to the
entry block of the function with the Lir frame `Frame.empty.writeAll params
vals` represented, or stops at the UD2 of the stack-limit check.
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.Process (Memory)
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine
open Relation

set_option linter.unusedSectionVars false

theorem writeAll_length {R : Type} [DecidableEq R] :
    ∀ (fr : Lir.Frame R) (ls : List (Lir.Loc R)) (vs : List Word) {fr' : Lir.Frame R},
    fr.writeAll ls vs = some fr' → vs.length = ls.length
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, _, h => by simp [Lir.Frame.writeAll] at h
  | _, _ :: _, [], _, h => by simp [Lir.Frame.writeAll] at h
  | fr, l :: ls, v :: vs, _, h => by
    simp only [Lir.Frame.writeAll] at h
    simp [writeAll_length _ ls vs h]

theorem flatMap_three (a b c : Ext.Instr) (R : List Byte) :
    ([a, b, c] : List Ext.Instr).flatMap Ext.encode ++ R =
      Ext.encode a ++ (Ext.encode b ++ (Ext.encode c ++ R)) := by
  simp

theorem toNat_add_ofNat {x : Word} {k : Nat} (h : x.toNat + k < 2 ^ 64) :
    (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt h]

theorem jae2_length : (Ext.encode (.jcc .ae 2)).length = 6 := rfl

theorem argRegN_ne_r11 (j : Nat) : argRegN j ≠ .r11 := by
  unfold argRegN; split
  · rename_i h
    have : ∀ i : Fin 6, argReg i ≠ .r11 := by decide
    exact this _
  · decide

theorem signExtend_two : (2 : BitVec 32).signExtend 64 = BitVec.ofNat 64 2 := by decide

namespace Env

variable {P : Type} (E : Env P) [DecidableEq P]

theorem entryChain_top {e : Nat} {stack : List (Lir.Activation P)} {t : MState}
    (h : E.EntryChain e stack t) : e ≤ E.E0 := by
  cases stack with
  | nil => exact h.1.le
  | cons a rest => have := E.chain_top h.2.2.2; omega

theorem sim_entry (hok : E.Ok) {g : Lir.FuncId} {fn : Lir.Func P} (hg : E.p.func? g = some fn)
    {vals : List Word} {stack : List (Lir.Activation P)} {lm : Lir.Memory} {t : MState} {e : Nat}
    (hent : E.Entry g vals stack lm t e) {fr : Lir.Frame P}
    (hfr : Lir.Frame.empty.writeAll fn.params vals = some fr) :
    ∃ t', TransGen (RStep E.exit) t t' ∧
      (E.Overflow t' ∨ E.Body ⟨⟨g, fn.entry, 0⟩, fr, stack, lm⟩ t' (e - 32 - frameSize (nslots fn))) := by
  have hv := hok.valid
  have fok := funcOk hok.errors hg
  have hneed := fok.frame
  have hF : frameSize (nslots fn) < 2 ^ 31 := by unfold need at hneed; omega
  have hFm := frameSize_mod (nslots fn)
  have hFg := Env.frameSize_ge (nslots fn)
  have htop := E.entryChain_top hent.chain
  have hhi : e + 8 ≤ E.S.stackHi := by have := hok.e0_hi; omega
  have he : e < 2 ^ 64 := by have := hv.stack_end; omega
  have hlen : vals.length = fn.params.length := writeAll_length _ _ _ hfr
  have hcode := E.code_lt hok
  -- the code of the prologue
  obtain ⟨post, hsplit⟩ := prologue_at E.A E.p hg
  have hd := code_drop E.L E.S.codeBase hsplit
  have hpro : prologue E.A g fn = ((([.mov .q (.reg .r11) .rsp, .alu .q .sub (.reg .r11) .r14,
      .aluI .q .cmp (.reg .r11) (BitVec.ofNat 32 (need (nslots fn)))] : List Ext.Instr) ++
      [Ext.Instr.jcc .ae 2, Ext.Instr.ud2]) ++
      pushSeq (nslots fn) ++ stageSeq (nslots fn) 0 fn.params ++
      paramMoves E.A (nslots fn) 0 fn.params).map .plain ++ [.jmp g fn.entry] := rfl
  rw [hpro, encodeAt_append, encodeAt_plain] at hd
  simp only [List.flatMap_append, List.append_assoc, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, encodeAt, AInstr.resolve] at hd
  generalize ho : lenOf ((funcCodes E.A E.p).take g).flatten = o at hd
  have hfa : E.L.func g = E.S.codeBase + o := by rw [← ho]; rfl
  change E.code.drop o = _ at hd
  have hd₀ := hd
  rw [← flatMap_three] at hd₀
  have hbound := drop_len hd (Ext.encode_length _).1
  have hrip : t.core.rip.toNat = E.S.codeBase + o := by
    rw [hent.rip, hfa, E.rip_toNat hok (by omega)]
  -- the first three instructions of the check
  obtain ⟨c₁, hr₁, hk₁, hf₁⟩ := run_check3 t.core t.memory (nslots fn) hent.rsp hent.r14 hent.low he
    hneed
  obtain ⟨st₁, -, hrip₁⟩ := transGen_runSeq (exit := E.exit) hv hent.good hrip hd₀ hr₁
  have hd₁ := drop_after hd₀
  -- JAE over the UD2
  have heval : Ext.Cond.eval c₁.flags .ae =
      some (!(BitVec.ofNat 64 (e - E.S.stackLo)).ult (BitVec.ofNat 64 (need (nslots fn)))) := by
    rw [hf₁]; exact Ext.eval_after_cmp_q _ _ _
  have ex₂ := Ext.exec_jcc c₁ t.memory .ae 2 _ heval
  have st₂ := rstep_code (exit := E.exit) (t := ⟨c₁, t.memory⟩) hv hent.good hrip₁ hd₁ ex₂
    (by intro h; cases h.1)
  have hult : (BitVec.ofNat 64 (e - E.S.stackLo)).ult (BitVec.ofNat 64 (need (nslots fn))) =
      decide (e - E.S.stackLo < need (nslots fn)) := by
    simp only [BitVec.ult, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hult] at st₂
  by_cases hov : e - E.S.stackLo < need (nslots fn)
  · -- stack overflow: stop at the UD2
    simp only [hov, decide_true, Bool.not_true, Bool.false_eq_true, ite_false] at st₂
    have hd₂ := drop_after hd₁
    rw [jae2_length] at hd₂
    have hend := hv.code_end
    have hb2 := drop_len hd₂ (by decide)
    have hrip₂ : (c₁.rip + BitVec.ofNat 64 (Ext.Instr.length (.jcc .ae 2))).toNat =
        E.S.codeBase + (o + ([Ext.Instr.mov .q (.reg .r11) .rsp, .alu .q .sub (.reg .r11) .r14,
          .aluI .q .cmp (.reg .r11) (BitVec.ofNat 32 (need (nslots fn)))].flatMap Ext.encode).length + 6) := by
      rw [toNat_add_ofNat (by rw [hrip₁]; simp only [Ext.Instr.length, jae2_length]; omega), hrip₁]
      rfl
    refine ⟨_, TransGen.tail st₁ st₂, .inl ⟨?_, g, fn, hg, ?_, ?_⟩⟩
    · rw [step_code hv hent.good (t := ⟨{ c₁ with
        rip := c₁.rip + BitVec.ofNat 64 (Ext.Instr.length (.jcc .ae 2)) }, t.memory⟩) hrip₂ hd₂ E.exit]
      rfl
    · simp only
      rw [hrip₂, ovfAddr, hfa, E.ns_eq hg]
      simp only [checkSeq, List.take, List.flatMap_cons, List.flatMap_nil, List.length_append,
        jae2_length]
      omega
    · show (c₁.read .rsp).toNat - E.S.stackLo < need (nslots fn)
      rw [hk₁ _ (by decide), hent.rsp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he]
      exact hov
  · simp only [hov, decide_false, Bool.not_false, ite_true] at st₂
    have hd₂ := drop_after (drop_after hd₁)
    rw [jae2_length, show (Ext.encode Ext.Instr.ud2).length = 2 from rfl] at hd₂
    rw [← List.append_assoc, ← List.flatMap_append, ← List.append_assoc, ← List.flatMap_append]
      at hd₂
    have hend := hv.code_end
    have hpos : 0 < ((pushSeq (nslots fn) ++ stageSeq (nslots fn) 0 fn.params ++
        paramMoves E.A (nslots fn) 0 fn.params).flatMap Ext.encode).length := by
      rw [List.flatMap_append, List.flatMap_append, List.length_append, List.length_append]
      have : 0 < ((pushSeq (nslots fn)).flatMap Ext.encode).length := by
        simp only [pushSeq, List.flatMap_cons, List.length_append]
        have := (Ext.encode_length (.push .rbp)).1
        omega
      omega
    have hb2 := drop_len hd₂ hpos
    generalize hl3 : ([Ext.Instr.mov .q (.reg .r11) .rsp, .alu .q .sub (.reg .r11) .r14,
      .aluI .q .cmp (.reg .r11) (BitVec.ofNat 32 (need (nslots fn)))].flatMap Ext.encode).length = l3
      at hd₂ hrip₁ hb2
    have hq : c₁.rip + BitVec.ofNat 64 (Ext.Instr.length (.jcc .ae 2)) +
        (2 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (E.S.codeBase + (o + l3 + 6 + 2)) := by
      rw [show Ext.Instr.length (.jcc .ae 2) = 6 from rfl, signExtend_two]
      apply BitVec.eq_of_toNat_eq
      have a1 : (c₁.rip + BitVec.ofNat 64 6).toNat = E.S.codeBase + o + l3 + 6 := by
        rw [toNat_add_ofNat (by rw [hrip₁]; omega), hrip₁]
      rw [toNat_add_ofNat (by rw [a1]; omega), a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hq] at st₂
    have hrip₂ : (BitVec.ofNat 64 (E.S.codeBase + (o + l3 + 6 + 2))).toNat =
        E.S.codeBase + (o + l3 + 6 + 2) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    -- the pushes, the staging and the parameter moves
    have hc₁ : ∀ r, r ≠ .r11 →
        ({ c₁ with rip := BitVec.ofNat 64 (E.S.codeBase + (o + l3 + 6 + 2)) } : State).read r =
          t.core.read r := fun r hr => hk₁ r hr
    have hlo : E.S.stackLo + 32 + frameSize (nslots fn) ≤ e := by unfold need at hov; omega
    obtain ⟨c₃, m₃, hr₃, hrsp₃, hk₃, hpush, hreg₃, hout₃⟩ := run_pushSeq hv hent.good.regions
      (c := { c₁ with rip := BitVec.ofNat 64 (E.S.codeBase + (o + l3 + 6 + 2)) })
      (by rw [hc₁ _ (by decide), hent.rsp]) hlo (by omega) hF
    have hfit : Fits E.S (e - 32 - frameSize (nslots fn)) (nslots fn) :=
      ⟨by omega, by omega, hneed⟩
    obtain ⟨c₄, m₄, hr₄, hk₄, hreg₄, hw₄, hout₄⟩ := run_stage hv hfit fn.params
      (by have := fok.params; omega) c₃ m₃ hrsp₃ (hreg₃.trans hent.good.regions)
    obtain ⟨c₅, m₅, hr₅, hregs₅, hslots₅, hk₅, hreg₅, hout₅⟩ := run_paramMoves hv E.A hfit
      fn.params 0 vals Lir.Frame.empty fr c₄ m₄ hfr (by rw [hk₄, hrsp₃])
      (hreg₄.trans (hreg₃.trans hent.good.regions)) (by have := fok.params; omega)
      (fun i hi => by
        have := hw₄ i (by omega)
        rw [hk₃ _ (argRegN_ne_rsp i), hc₁ _ (argRegN_ne_r11 i), hent.args i hi] at this
        simpa using this)
      (fun k hk => param_slot_lt hk)
      (fun q v h => by simp [Lir.Frame.empty] at h) (fun k v _ h => by simp [Lir.Frame.empty] at h)
    have hrun : runSeq (pushSeq (nslots fn) ++ stageSeq (nslots fn) 0 fn.params ++
        paramMoves E.A (nslots fn) 0 fn.params)
        { c₁ with rip := BitVec.ofNat 64 (E.S.codeBase + (o + l3 + 6 + 2)) } t.memory =
        some (c₅, m₅) := by
      rw [runSeq_append_of (runSeq_append_of hr₃ |>.trans hr₄), hr₅]
    obtain ⟨st₃, good₅, hrip₅⟩ := transGen_runSeq (exit := E.exit) hv hent.good
      (t := ⟨{ c₁ with rip := BitVec.ofNat 64 (E.S.codeBase + (o + l3 + 6 + 2)) }, t.memory⟩)
      hrip₂ hd₂ hrun
    have hd₃ := drop_after hd₂
    rw [lenOf_plain] at hd₃
    simp only [List.flatMap_append, List.length_append, jae2_length,
      show (Ext.encode Ext.Instr.ud2).length = 2 from rfl, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] at hd₃
    obtain ⟨ot, hot, hotl⟩ := E.block_in_code hg fok.entry
    simp only [List.flatMap_cons, List.flatMap_nil, List.length_append, List.append_nil] at hl3
    have hrip₅' : c₅.rip.toNat = E.S.codeBase + (o + l3 + 6 + 2) +
        ((pushSeq (nslots fn) ++ stageSeq (nslots fn) 0 fn.params ++
          paramMoves E.A (nslots fn) 0 fn.params).flatMap Ext.encode).length := hrip₅
    simp only [List.flatMap_append, List.length_append] at hrip₅'
    have hb3 := drop_len hd₃ (Ext.encode_length _).1
    have st₄ := E.rstep_jmp hok good₅ (t := ⟨c₅, m₅⟩) (by omega)
      (rip_of_toNat (by rw [hrip₅']; omega)) (by omega) (by omega) hd₃
    refine ⟨_, TransGen.trans st₁ (TransGen.head st₂ (TransGen.tail st₃ st₄)), .inr ?_⟩
    -- the frame
    have hns := E.ns_eq hg
    have hkeepHi : ∀ x, e ≤ x → m₅.bytes.get? x = t.memory.bytes.get? x := by
      intro x hx
      rw [hout₅ x (by omega), hout₄ x (by omega), hout₃ x (by omega)]
    have hkeepLo : ∀ x, x < e - 32 - frameSize (nslots fn) →
        m₅.bytes.get? x = t.memory.bytes.get? x := by
      intro x hx
      rw [hout₅ x (by omega), hout₄ x (by omega), hout₃ x (by omega)]
    have hreg : ∀ r, ¬ Scratch r → (∀ k, r ≠ allocReg k) → r ≠ .rsp → c₅.read r = t.core.read r := by
      intro r hr ha hrsp
      rw [hk₅ r hr ha, hk₄, hk₃ r hrsp, hc₁ r (by rw [not_scratch_iff] at hr; exact hr.2.2.2)]
    have hpush' : Env.Pushed e m₅ (t.core.read .rbp) (t.core.read .rbx) (t.core.read .r12)
        (t.core.read .r13) := by
      have := pushed_congr hpush (by omega) (hi := e) le_rfl
        (fun x hx hx' => by rw [hout₅ x (by omega), hout₄ x (by omega)])
      simpa only [hc₁ _ (show Reg.rbp ≠ .r11 by decide), hc₁ _ (show Reg.rbx ≠ .r11 by decide),
        hc₁ _ (show Reg.r12 ≠ .r11 by decide), hc₁ _ (show Reg.r13 ≠ .r11 by decide)] using this
    have hal := hent.align
    have hneed' : need (nslots fn) = frameSize (nslots fn) + 40 := rfl
    refine ⟨good₅, ?_, ?_, ?_, by omega, by omega, ?_, ?_, hregs₅, by rw [hns]; exact hslots₅, ?_⟩
    · simp only [read_rip]
      rw [hreg _ (by decide) (fun k => (allocReg_ne_r15 k).symm) (by decide), hent.r15]
    · simp only [read_rip]
      rw [hreg _ (by decide) (fun k => (allocReg_ne_r14 k).symm) (by decide), hent.r14]
    · simp only [read_rip]
      rw [hk₅ _ (by decide) (fun k => (allocReg_ne_rsp k).symm), hk₄, hrsp₃]
    · exact congrArg (BitVec.ofNat 64) (layout_block E.A E.p E.S.codeBase _ _)
    · refine hent.mem.congr fun x hx => ?_
      simp only [Space.InMem] at hx
      have := hv.stack_mem; have := hent.mem.1
      by_cases h : x < e - 32 - frameSize (nslots fn)
      · exact hkeepLo x h
      · exact hkeepHi x (by omega)
    · have hc := hent.chain
      cases stack with
      | nil =>
        obtain ⟨he0, hex, hrbp, hrbx, hr12, hr13⟩ := hc
        simp only [Env.Chain, hns]
        refine ⟨by omega, ?_, ?_⟩
        · exact wordAt_congr_range hex (lo := e) (hi := E.E0 + 8) (by omega) le_rfl
            (fun x hx _ => hkeepHi x hx)
        · rw [← hrbp, ← hrbx, ← hr12, ← hr13, ← he0]; exact hpush'
      | cons a rest =>
        obtain ⟨hra, hsl, hsv, hch⟩ := hc
        simp only [Env.Chain, hns]
        have htop' := E.chain_top hch
        have e1 : e - 32 - frameSize (nslots fn) + frameSize (nslots fn) + 32 = e := by omega
        have e2 : e - 32 - frameSize (nslots fn) + frameSize (nslots fn) + 40 = e + 8 := by omega
        refine ⟨⟨_, _, _, _, by rw [e1]; exact hpush'⟩, ?_, ?_, ?_, ?_⟩
        · rw [e1]
          exact wordAt_congr_range hra (lo := e) (hi := E.E0 + 8) le_rfl (by omega)
            (fun x hx _ => hkeepHi x hx)
        · rw [e2]
          exact Env.slotsAt_congr hsl (hi := E.E0 + 8) (by have := Env.frameSize_ge (E.ns a.point.func); omega)
            (fun x hx _ => hkeepHi x (by omega))
        · rw [e2]
          exact E.savedAt_congr hsv (hi := E.E0 + 8) (by omega) (fun x hx _ => hkeepHi x (by omega))
        · rw [e2]
          exact E.chain_congr hch (fun x hx _ => hkeepHi x (by omega))

end Env

end Silmaril.X86.Backend
