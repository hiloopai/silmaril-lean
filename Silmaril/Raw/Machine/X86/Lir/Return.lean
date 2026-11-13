module

public import Silmaril.Machine.X86.Lir.Call.Defs

/-!
# Simulation of returns

The code of a Lir `ret` loads the returned values into `rax rdx`, removes the
frame (`add rsp, F`), restores the four callee-saved registers and executes
RET. `Env.sim_ret` continues into the rest of the caller's call site (reload
the allocatable registers, store the results) and reaches the point after the
call; `Env.sim_halt` shows that at the bottom of the stack RET pops `exit`, so
the machine step is `returned`, with the values in `rax rdx`, the callee-saved
registers restored and the stack pointer above the return address.
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.Process (Memory)
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine
open Relation

set_option linter.unusedSectionVars false

/-- The five instructions of the epilogue before RET. -/
def epi5 (ns : Nat) : List Ext.Instr :=
  [.aluI .q .add (.reg .rsp) (BitVec.ofNat 32 (frameSize ns)), .pop .r13, .pop .r12, .pop .rbx,
    .pop .rbp]

theorem epilogue_eq (ns : Nat) : epilogue ns = epi5 ns ++ [.ret] := rfl

section

variable {S : Space} {n : Nat} (hv : S.Valid n)
include hv

theorem run_epi5 {c : State} {m : Memory} (hreg : m.regions = S.regions n) {B ns : Nat}
    (hrsp : c.read .rsp = BitVec.ofNat 64 B) (hlo : S.stackLo ≤ B)
    (hhi : B + frameSize ns + 32 + 8 ≤ S.stackHi) (hF : frameSize ns < 2 ^ 31)
    {w₀ w₁ w₂ w₃ : Word} (hp : Env.Pushed (B + frameSize ns + 32) m w₀ w₁ w₂ w₃) :
    ∃ c', runSeq (epi5 ns) c m = some (c', m) ∧
      c'.read .rsp = BitVec.ofNat 64 (B + frameSize ns + 32) ∧
      c'.read .rbp = w₀ ∧ c'.read .rbx = w₁ ∧ c'.read .r12 = w₂ ∧ c'.read .r13 = w₃ ∧
      (∀ r, r ≠ .rsp → r ≠ .rbp → r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → c'.read r = c.read r) := by
  obtain ⟨p₀, p₁, p₂, p₃⟩ := hp
  obtain ⟨s₁, h₁, r₁, k₁⟩ := runSeq_addRsp (m := m) hrsp hF
    [.pop .r13, .pop .r12, .pop .rbx, .pop .rbp]
  obtain ⟨s₂, h₂, r₂, v₂, k₂⟩ := runSeq_pop hv hreg r₁ (by omega) (by omega)
    (by rwa [show B + frameSize ns + 32 - 32 = B + frameSize ns by omega] at p₃) .r13 (by decide)
    [.pop .r12, .pop .rbx, .pop .rbp]
  obtain ⟨s₃, h₃, r₃, v₃, k₃⟩ := runSeq_pop hv hreg r₂ (by omega) (by omega)
    (by rwa [show B + frameSize ns + 32 - 24 = B + frameSize ns + 8 by omega] at p₂) .r12 (by decide)
    [.pop .rbx, .pop .rbp]
  obtain ⟨s₄, h₄, r₄, v₄, k₄⟩ := runSeq_pop hv hreg r₃ (by omega) (by omega)
    (by rwa [show B + frameSize ns + 32 - 16 = B + frameSize ns + 8 + 8 by omega] at p₁) .rbx
    (by decide) [.pop .rbp]
  obtain ⟨s₅, h₅, r₅, v₅, k₅⟩ := runSeq_pop hv hreg r₄ (by omega) (by omega)
    (by rwa [show B + frameSize ns + 32 - 8 = B + frameSize ns + 8 + 8 + 8 by omega] at p₀) .rbp
    (by decide) []
  refine ⟨s₅, by rw [epi5, h₁, h₂, h₃, h₄, h₅]; rfl, by rw [r₅], v₅,
    by rw [k₅ _ (by decide) (by decide), v₄],
    by rw [k₅ _ (by decide) (by decide), k₄ _ (by decide) (by decide), v₃],
    by rw [k₅ _ (by decide) (by decide), k₄ _ (by decide) (by decide), k₃ _ (by decide) (by decide), v₂],
    fun r hr h0 h1 h2 h3 => ?_⟩
  rw [k₅ r hr h0, k₄ r hr h1, k₃ r hr h2, k₂ r hr h3, k₁ r hr]

end

theorem flatMap_encode_pos {l : List Ext.Instr} (h : l ≠ []) : 0 < (l.flatMap Ext.encode).length := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h
  rw [List.flatMap_cons, List.length_append]
  have := (Ext.encode_length x).1
  omega

theorem resRegN_cases (i : Nat) : resRegN i = .rax ∨ resRegN i = .rdx := by
  unfold resRegN; split
  · rename_i h
    have : ∀ j : Fin 2, resReg j = .rax ∨ resReg j = .rdx := by decide
    exact this _
  · exact .inl rfl

namespace Env

variable {P : Type} (E : Env P) [DecidableEq P]

theorem ret_errors (hok : E.Ok) {s : Lir.State P} {locs : List (Lir.Loc P)}
    (hf : E.p.fetch s.point = some (.term (.ret locs))) : locs.length ≤ 2 := by
  obtain ⟨fn, b, hfn, hbl, hidx, hterm⟩ := E.fetch_term hf
  have := (funcOk hok.errors hfn).terms b (List.mem_of_getElem? hbl)
  rw [hterm] at this
  by_contra h
  simp only [termErrors] at this
  rw [ite_eq_right h] at this
  cases this

/-- The code of a `ret` up to its RET instruction. -/
theorem ret_prefix (hok : E.Ok) {s : Lir.State P} {t : MState} {B : Nat} (hm : E.Body s t B)
    {locs : List (Lir.Loc P)} {vals : List Word}
    (hf : E.p.fetch s.point = some (.term (.ret locs))) (hvals : s.frame.readAll locs = some vals)
    {w₀ w₁ w₂ w₃ : Word}
    (hp : Pushed (B + frameSize (E.ns s.point.func) + 32) t.memory w₀ w₁ w₂ w₃) :
    ∃ c o rest, TransGen (RStep E.exit) t ⟨c, t.memory⟩ ∧ c.rip.toNat = E.S.codeBase + o ∧
      E.code.drop o = Ext.encode .ret ++ rest ∧
      c.read .rsp = BitVec.ofNat 64 (B + frameSize (E.ns s.point.func) + 32) ∧
      c.read .rbp = w₀ ∧ c.read .rbx = w₁ ∧ c.read .r12 = w₂ ∧ c.read .r13 = w₃ ∧
      (∀ i (h : i < vals.length), c.read (resRegN i) = vals[i]) ∧ vals.length ≤ 2 ∧
      c.read .r14 = t.core.read .r14 ∧ c.read .r15 = t.core.read .r15 := by
  have hv := hok.valid
  obtain ⟨fn, b, hfn, hbl, hidx, hterm⟩ := E.fetch_term hf
  have hns := E.ns_eq hfn
  have hlen := E.ret_errors hok hf
  have hvlen := readAll_length s.frame locs hvals
  obtain ⟨hneed, hhi, hlo⟩ := E.frame_bounds hok hm hfn
  have hfit : Fits E.S B (E.ns s.point.func) := ⟨by omega, by omega, hneed⟩
  have hF : frameSize (E.ns s.point.func) < 2 ^ 31 := by unfold need at hneed; omega
  have hci : s.point.index < (blockChunks E.A s.point.func (nslots fn) b).length := by
    rw [blockChunks_length]; omega
  obtain ⟨o', rest, hpa, hd, hbound⟩ := E.code_at hfn hbl hci
  have hchunk : (blockChunks E.A s.point.func (nslots fn) b)[s.point.index] =
      (retLoads E.A 0 locs ++ epi5 (nslots fn) ++ [Ext.Instr.ret]).map .plain := by
    simp only [hidx, blockChunks_term, hterm, termChunk, epilogue_eq, List.append_assoc]
  rw [hchunk, encodeAt_plain, List.flatMap_append] at hd
  rw [← hns] at hd
  obtain ⟨c₁, hr₁, hv₁, hk₁⟩ := run_retLoads hv E.A hfit hm.good.regions hm.slots locs 0 vals t.core
    hvals hm.rsp hm.regs (by omega)
    (fun k hk => by rw [hns]; exact term_slot_lt hbl (by rw [hterm]; exact hk))
  have hc₁rsp : c₁.read .rsp = BitVec.ofNat 64 B :=
    by rw [hk₁ _ (fun i _ h => resRegN_ne_rsp (0 + i) h.symm), hm.rsp]
  obtain ⟨c₂, hr₂, hrsp₂, h0, h1, h2, h3, hk₂⟩ := run_epi5 hv hm.good.regions hc₁rsp hfit.lo
    (by have := E.chain_top hm.chain; have := hok.e0_hi; omega) hF hp
  have hrun : runSeq (retLoads E.A 0 locs ++ epi5 (E.ns s.point.func)) t.core t.memory =
      some (c₂, t.memory) := by
    rw [runSeq_append_of hr₁, hr₂]
  obtain ⟨i₀, is, hcons⟩ : ∃ i₀ is, retLoads E.A 0 locs ++ epi5 (E.ns s.point.func) = i₀ :: is :=
    List.exists_cons_of_ne_nil (by simp [epi5])
  rw [hcons] at hd hrun
  rw [List.append_assoc] at hd
  have hrip : t.core.rip.toNat = E.S.codeBase + o' := by
    rw [hm.rip, hpa, E.rip_toNat hok (by
      have := drop_len hd (by
        rw [List.flatMap_cons, List.length_append]
        have := (Ext.encode_length i₀).1; omega)
      omega)]
  obtain ⟨st, -, hrip'⟩ := transGen_runSeq (exit := E.exit) hv hm.good hrip hd hrun
  have hkeep : ∀ r, r ≠ .rsp → r ≠ .rbp → r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → r ≠ .rax → r ≠ .rdx →
      c₂.read r = t.core.read r := by
    intro r a b c d e f g
    rw [hk₂ r a b c d e, hk₁ r (fun i _ h => by
      rcases resRegN_cases (0 + i) with h' | h' <;> rw [h'] at h <;> contradiction)]
  have hd₂ := drop_after hd
  refine ⟨c₂, o' + ((i₀ :: is).flatMap Ext.encode).length, rest, st, by rw [hrip']; omega,
    by rw [hd₂]; simp, hrsp₂, h0, h1, h2, h3, fun i hi => ?_, by omega,
    hkeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hkeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  have := hv₁ i hi
  rw [zero_add] at this
  rw [← this]
  rcases resRegN_cases i with h' | h' <;> rw [h'] <;>
    exact hk₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The machine state after the final RET of a program that returned `vals`
with linear memory `lm`: RIP is `exit`, the values are in `rax` and `rdx`, RSP
is just above the return address, the System V callee-saved registers have
their values at entry, and the linear memory is represented. -/
structure Final (vals : List Word) (lm : Lir.Memory) (f : MState) : Prop where
  rip : f.core.rip = E.exit
  vals_len : vals.length ≤ 2
  vals : ∀ i (h : i < vals.length), f.core.read (resRegN i) = vals[i]
  rsp : f.core.read .rsp = BitVec.ofNat 64 (E.E0 + 8)
  rbx : f.core.read .rbx = E.saved .rbx
  rbp : f.core.read .rbp = E.saved .rbp
  r12 : f.core.read .r12 = E.saved .r12
  r13 : f.core.read .r13 = E.saved .r13
  r14 : f.core.read .r14 = BitVec.ofNat 64 E.S.stackLo
  r15 : f.core.read .r15 = BitVec.ofNat 64 E.S.memBase
  mem : MemRel E.S lm f.memory

theorem sim_halt (hok : E.Ok) {s : Lir.State P} {t : MState} {B : Nat} (hm : E.Body s t B)
    {locs : List (Lir.Loc P)} {vals : List Word}
    (hf : E.p.fetch s.point = some (.term (.ret locs))) (hvals : s.frame.readAll locs = some vals)
    (hst : s.stack = []) :
    ∃ t', ReflTransGen (RStep E.exit) t t' ∧
      ∃ final, Ext.step E.exit t' = .returned final ∧ E.Final vals s.mem final := by
  have hv := hok.valid
  have hch := hm.chain
  rw [hst] at hch
  obtain ⟨he0, hex, hp⟩ := hch
  obtain ⟨c, o, rest, st, hrip, hd, hrsp, h0, h1, h2, h3, hvs, hvl, h14, h15⟩ :=
    E.ret_prefix hok hm hf hvals (by rw [he0]; exact hp)
  have hE0 : E.E0 + 8 ≤ E.S.stackHi := hok.e0_hi
  have hpop := pop_at hv hm.good.regions (s := c) (by rw [hrsp, he0]) (by have := hm.low; omega)
    hE0 hex
  have ex := exec_ret_ok c t.memory (v := E.exit) (by rw [hpop, hrsp, he0, add8_eq])
  rw [hrsp, he0, add8_eq] at ex
  refine ⟨_, st.to_reflTransGen,
    ⟨{ c.write .rsp (BitVec.ofNat 64 (E.E0 + 8)) with rip := E.exit }, t.memory⟩, ?_, ?_⟩
  · rw [step_code hv hm.good (t := ⟨c, t.memory⟩) hrip hd E.exit, ex]
    simp
  · refine ⟨rfl, hvl, fun i hi => ?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_, hm.mem⟩
    · simp only [read_rip, State.read_write_other _ _ _ _ (resRegN_ne_rsp i)]; exact hvs i hi
    · simp [h1]
    · simp [h0]
    · simp [h2]
    · simp [h3]
    · simp [h14, hm.r14]
    · simp [h15, hm.r15]

/-- The code after the CALL of a call site, at its return address. -/
theorem call_code {pt : Lir.Point} {g : Lir.FuncId} {args results : List (Lir.Loc P)}
    (hf : E.p.fetch pt = some (.instr (.call g args results))) :
    ∃ o rest, E.retAddr pt = E.S.codeBase + o ∧
      E.code.drop o = (reloadAll (E.ns pt.func) ++ resStores E.A 0 results).flatMap Ext.encode ++
        rest ∧
      E.pa pt.next = E.retAddr pt +
        ((reloadAll (E.ns pt.func) ++ resStores E.A 0 results).flatMap Ext.encode).length := by
  obtain ⟨fn, b, hfn, hbl, hi⟩ := E.fetch_instr hf
  have hlt : pt.index < b.instrs.length := (List.getElem?_eq_some_iff.mp hi).1
  have hns := E.ns_eq hfn
  have hci : pt.index < (blockChunks E.A pt.func (nslots fn) b).length := by
    rw [blockChunks_length]; omega
  obtain ⟨o', rest, hpa, hd, hbound⟩ := E.code_at hfn hbl hci
  have hchunk : (blockChunks E.A pt.func (nslots fn) b)[pt.index] =
      instrChunk E.A (nslots fn) (.call g args results) := by
    rw [blockChunks_instr E.A _ _ b hlt, (List.getElem?_eq_some_iff.mp hi).2]
  rw [hchunk] at hd
  simp only [instrChunk, encodeAt_append, encodeAt_plain, encodeAt, AInstr.resolve, List.append_nil,
    List.append_assoc] at hd
  rw [← hns] at hd
  have hd₂ := drop_after (drop_after hd)
  have h5 : ∀ r, (Ext.encode (.call r)).length = 5 := fun r => rfl
  rw [h5] at hd₂
  refine ⟨_, _, ?_, hd₂, ?_⟩
  · rw [E.retAddr_call hf, callPrefix, lenOf_plain, hpa]; omega
  · have := pointAddr_succ E.A E.p E.S.codeBase hfn hbl hlt
    simp only [pa, Lir.Point.next]
    rw [this, (List.getElem?_eq_some_iff.mp hi).2]
    simp only [instrChunk, lenOf_append, lenOf_plain, lenOf_cons, lenOf_nil, AInstr.len]
    rw [E.retAddr_call hf, callPrefix, lenOf_plain, hns]
    have : E.pa pt = pointAddr E.A E.p E.S.codeBase ⟨pt.func, pt.label, pt.index⟩ := rfl
    rw [this]
    omega

theorem sim_ret (hok : E.Ok) {s : Lir.State P} {t : MState} {B : Nat} (hm : E.Body s t B)
    {locs : List (Lir.Loc P)} {vals : List Word} {a : Lir.Activation P}
    {rest : List (Lir.Activation P)} {g : Lir.FuncId} {args results : List (Lir.Loc P)}
    {fr : Lir.Frame P}
    (hf : E.p.fetch s.point = some (.term (.ret locs))) (hvals : s.frame.readAll locs = some vals)
    (hst : s.stack = a :: rest) (hfa : E.p.fetch a.point = some (.instr (.call g args results)))
    (hw : a.frame.writeAll results vals = some fr) :
    ∃ t', TransGen (RStep E.exit) t t' ∧
      E.Body ⟨a.point.next, fr, rest, s.mem⟩ t' (B + frameSize (E.ns s.point.func) + 40) := by
  have hv := hok.valid
  have hch := hm.chain
  rw [hst] at hch
  obtain ⟨⟨w₀, w₁, w₂, w₃, hp⟩, hra, hsl, hsv, hch⟩ := hch
  have htop := E.chain_top hch
  have hE0 := hok.e0_hi
  obtain ⟨c, o, rest', st, hrip, hd, hrsp, -, -, -, -, hvs, hvl, h14, h15⟩ :=
    E.ret_prefix hok hm hf hvals hp
  -- RET to the call site
  have hpop := pop_at hv hm.good.regions (s := c) hrsp (by have := hm.low; omega) (by omega) hra
  have ex := exec_ret_ok c t.memory (v := BitVec.ofNat 64 (E.retAddr a.point))
    (by rw [hpop, hrsp, add8_eq])
  rw [hrsp, add8_eq] at ex
  obtain ⟨oa, resta, hoa, hda, hnext⟩ := E.call_code hfa
  have hcode := E.code_lt hok
  have hend := hv.code_end
  have hposa : 0 < ((reloadAll (E.ns a.point.func) ++ resStores E.A 0 results).flatMap
      Ext.encode).length := by
    rw [List.flatMap_append, List.length_append]
    have : 0 < ((reloadAll (E.ns a.point.func)).flatMap Ext.encode).length :=
      flatMap_encode_pos (by simp [reloadAll])
    omega
  have hba := drop_len hda hposa
  have hne : ¬ (Ext.Instr.ret = .ret ∧ BitVec.ofNat 64 (E.retAddr a.point) = E.exit) := by
    rintro ⟨-, h⟩
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    have := hok.exit_out
    omega
  have st₂ := rstep_code hv hm.good (t := ⟨c, t.memory⟩) hrip hd ex hne
  -- the rest of the call site: reload the registers and store the results
  obtain ⟨fna, ba, hfna, hbla, hia⟩ := E.fetch_instr hfa
  obtain ⟨-, hresl, -⟩ := E.call_errors hok hfna hbla hia
  have hnsa := E.ns_eq hfna
  have hneeda := (funcOk hok.errors hfna).frame
  rw [← hnsa] at hneeda
  have hB' : B + frameSize (E.ns s.point.func) + 32 + 8 = B + frameSize (E.ns s.point.func) + 40 := rfl
  have hfit' : Fits E.S (B + frameSize (E.ns s.point.func) + 40) (E.ns a.point.func) :=
    ⟨by have := hm.low; omega, by omega, hneeda⟩
  have hc₃rsp : ({ c.write .rsp (BitVec.ofNat 64 (B + frameSize (E.ns s.point.func) + 32 + 8)) with
      rip := BitVec.ofNat 64 (E.retAddr a.point) } : State).read .rsp =
      BitVec.ofNat 64 (B + frameSize (E.ns s.point.func) + 40) := by simp
  obtain ⟨c₄, hr₄, hv₄, hk₄⟩ := run_reloadAll hv hfit' _ t.memory hc₃rsp hm.good.regions hsv.1
  have hregs₄ : ∀ q v, a.frame.regs q = some v → c₄.read (E.A.reg q) = v :=
    fun q v hq => hv₄ (E.A.idx q) v (hsv.2 q v hq)
  obtain ⟨c₅, m₅, hr₅, hregs₅, hslots₅, hk₅, hreg₅, hout₅⟩ := run_resStores hv E.A hfit' results 0
    vals a.frame fr c₄ t.memory hw
    (by rw [hk₄ _ (fun k => (allocReg_ne_rsp k).symm), hc₃rsp]) hm.good.regions (by omega)
    (fun i hi => by
      rw [hk₄ _ (fun k => resRegN_ne_alloc _ k), zero_add]
      simp only [read_rip, State.read_write_other _ _ _ _ (resRegN_ne_rsp i)]
      exact hvs i hi)
    (fun k hk => by rw [hnsa]; exact slot_lt hbla hia (by simp [instrSlots, hk]))
    hregs₄ hsl
  have hrun : runSeq (reloadAll (E.ns a.point.func) ++ resStores E.A 0 results)
      { c.write .rsp (BitVec.ofNat 64 (B + frameSize (E.ns s.point.func) + 32 + 8)) with
        rip := BitVec.ofNat 64 (E.retAddr a.point) } t.memory = some (c₅, m₅) := by
    rw [runSeq_append_of hr₄, hr₅]
  obtain ⟨i₀, is, hcons⟩ : ∃ i₀ is, reloadAll (E.ns a.point.func) ++ resStores E.A 0 results =
      i₀ :: is := List.exists_cons_of_ne_nil (by simp [reloadAll])
  rw [hcons] at hda hrun hnext
  have hrip₃ : (BitVec.ofNat 64 (E.retAddr a.point)).toNat = E.S.codeBase + oa := by
    rw [hoa, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [hcons] at hba; omega)]
  obtain ⟨st₃, good₅, hrip₅⟩ := transGen_runSeq (exit := E.exit) hv hm.good
    (t := ⟨{ c.write .rsp (BitVec.ofNat 64 (B + frameSize (E.ns s.point.func) + 32 + 8)) with
        rip := BitVec.ofNat 64 (E.retAddr a.point) }, t.memory⟩) hrip₃ hda hrun
  refine ⟨_, TransGen.trans st (TransGen.head st₂ st₃), ?_⟩
  have hFa := Env.frameSize_ge (E.ns a.point.func)
  have hal := hm.align
  have hFm := frameSize_mod (E.ns s.point.func)
  refine ⟨good₅, ?_, ?_, ?_, by omega, by have := hm.low; omega, ?_, ?_, hregs₅, hslots₅, ?_⟩
  · rw [hk₅ _ (fun k => (allocReg_ne_r15 k).symm), hk₄ _ (fun k => (allocReg_ne_r15 k).symm)]
    simp [h15, hm.r15]
  · rw [hk₅ _ (fun k => (allocReg_ne_r14 k).symm), hk₄ _ (fun k => (allocReg_ne_r14 k).symm)]
    simp [h14, hm.r14]
  · rw [hk₅ _ (fun k => (allocReg_ne_rsp k).symm), hk₄ _ (fun k => (allocReg_ne_rsp k).symm),
      hc₃rsp]
  · apply rip_of_toNat
    rw [hrip₅, hnext, hoa]
  · refine hm.mem.congr fun x hx => hout₅ x ?_
    simp only [Space.InMem] at hx
    have := hv.stack_mem; have := hm.mem.1; have := hm.low
    omega
  · exact E.chain_congr (f := a.point.func) hch (fun x hx _ => hout₅ x (.inr (le_trans
      (by omega) hx)))

end Env

end Silmaril.X86.Backend
