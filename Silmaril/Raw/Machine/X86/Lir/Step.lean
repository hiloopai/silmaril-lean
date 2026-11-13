module

public import Silmaril.Machine.X86.Lir.Seq.Defs

/-!
# Simulation of operations, jumps, branches and traps

For a Lir state related to the machine by `Env.Body`, one Lir step that runs
an operation, a jump or a branch is matched by at least one machine step to a
state related to the successor (`sim_op`, `sim_jump`, `sim_branch`); a trap is
matched by the UD2 at the current address (`sim_trap`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Silmaril.X86.Backend

open Silmaril.Process (Memory)
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine
open Relation

variable {P : Type}

/-! ## Consequences of a successful check -/

theorem funcErrors_nil {A : Assign P} {p : Lir.Prog P} (h : progErrors A p = []) {f : Lir.FuncId}
    {fn : Lir.Func P} (hf : p.func? f = some fn) : funcErrors p f fn = [] := by
  have hf' : p.funcs[f]? = some fn := hf
  obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp hf'
  simp only [progErrors, List.append_eq_nil_iff, List.flatten_eq_nil_iff] at h
  have := h.1 ((p.funcs.mapIdx (funcErrors p))[f]'(by simpa using hl)) (List.getElem_mem _)
  simpa [he] using this

theorem codeLen_lt {A : Assign P} {p : Lir.Prog P} (h : progErrors A p = []) :
    lenOf (progCode A p) < 2 ^ 31 := by
  have h2 := (List.append_eq_nil_iff.mp h).2
  by_contra hc
  rw [ite_eq_right hc] at h2
  cases h2

structure FuncOk (p : Lir.Prog P) (f : Lir.FuncId) (fn : Lir.Func P) : Prop where
  params : fn.params.length ≤ 6
  entry : fn.entry < fn.blocks.length
  frame : need (nslots fn) < 2 ^ 31
  instrs : ∀ b ∈ fn.blocks, ∀ i ∈ b.instrs, instrErrors p f i = []
  terms : ∀ b ∈ fn.blocks, termErrors fn f b.term = []

theorem funcOk {A : Assign P} {p : Lir.Prog P} (h : progErrors A p = []) {f : Lir.FuncId}
    {fn : Lir.Func P} (hf : p.func? f = some fn) : FuncOk p f fn := by
  have := funcErrors_nil h hf
  simp only [funcErrors, labelErrors, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at this
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
  refine ⟨?_, ?_, ?_, fun b hb i hi => (h4 b hb).1 i hi, fun b hb => (h4 b hb).2⟩
  · by_contra hc; rw [ite_eq_right hc] at h1; cases h1
  · by_contra hc; rw [ite_eq_right hc] at h2; cases h2
  · by_contra hc; rw [ite_eq_right hc] at h3; cases h3

theorem instr_mem {fn : Lir.Func P} {l : Lir.Label} {b : Lir.Block P} (hb : fn.blocks[l]? = some b)
    {k : Nat} {i : Lir.Instr P} (hi : b.instrs[k]? = some i) : b ∈ fn.blocks ∧ i ∈ b.instrs :=
  ⟨List.mem_of_getElem? hb, List.mem_of_getElem? hi⟩

theorem slot_lt {fn : Lir.Func P} {l : Lir.Label} {b : Lir.Block P} (hb : fn.blocks[l]? = some b)
    {k : Nat} {i : Lir.Instr P} (hi : b.instrs[k]? = some i) {n : Nat} (hn : n ∈ instrSlots i) :
    n < nslots fn := by
  apply lt_nslots
  simp only [funcSlots, blockSlots, List.mem_append, List.mem_flatMap]
  exact .inr ⟨b, List.mem_of_getElem? hb, .inl ⟨i, List.mem_of_getElem? hi, hn⟩⟩

theorem term_slot_lt {fn : Lir.Func P} {l : Lir.Label} {b : Lir.Block P}
    (hb : fn.blocks[l]? = some b) {n : Nat} (hn : n ∈ termSlots b.term) : n < nslots fn := by
  apply lt_nslots
  simp only [funcSlots, blockSlots, List.mem_append, List.mem_flatMap]
  exact .inr ⟨b, List.mem_of_getElem? hb, .inr hn⟩

theorem param_slot_lt {fn : Lir.Func P} {n : Nat} (hn : n ∈ locSlots fn.params) :
    n < nslots fn := by
  apply lt_nslots
  simp only [funcSlots, List.mem_append]
  exact .inl hn

theorem mem_locSlots {ls : List (Lir.Loc P)} {n : Nat} (h : Lir.Loc.slot n ∈ ls) : n ∈ locSlots ls := by
  simp only [locSlots, List.mem_filterMap]
  exact ⟨_, h, rfl⟩

/-! ## Code at a program point -/

namespace Env

variable (E : Env P)

theorem func_block {pt : Lir.Point} {b : Lir.Block P}
    (hb : E.p.block? pt.func pt.label = some b) :
    ∃ fn, E.p.func? pt.func = some fn ∧ fn.blocks[pt.label]? = some b := by
  simp only [Lir.Prog.block?, Option.bind_eq_some_iff] at hb
  exact hb

theorem ns_eq {f : Lir.FuncId} {fn : Lir.Func P} (hf : E.p.func? f = some fn) :
    E.ns f = nslots fn := by
  simp [ns, hf]

/-- The code of chunk `pt.index` of a block sits at the address of `pt`. -/
theorem code_at {pt : Lir.Point} {fn : Lir.Func P} {b : Lir.Block P}
    (hf : E.p.func? pt.func = some fn) (hb : fn.blocks[pt.label]? = some b)
    (hi : pt.index < (blockChunks E.A pt.func (nslots fn) b).length) :
    ∃ o rest, E.pa pt = E.S.codeBase + o ∧
      E.code.drop o = encodeAt E.L (E.pa pt) ((blockChunks E.A pt.func (nslots fn) b)[pt.index]) ++
        rest ∧
      o + lenOf ((blockChunks E.A pt.func (nslots fn) b)[pt.index]) ≤ E.code.length := by
  obtain ⟨pre, post, hsplit, haddr⟩ := progCode_at E.A E.p E.S.codeBase hf hb hi
  refine ⟨lenOf pre, encodeAt E.L (E.S.codeBase + lenOf pre +
    lenOf ((blockChunks E.A pt.func (nslots fn) b)[pt.index])) post, haddr.symm, ?_, ?_⟩
  · rw [code, code_drop E.L E.S.codeBase hsplit, haddr]; rfl
  · have := lenOf_le hsplit
    rw [code, encodeAt_length]
    exact this

theorem code_lt (hok : E.Ok) : E.code.length < 2 ^ 31 := by
  rw [code, encodeAt_length]; exact codeLen_lt hok.errors

theorem rip_toNat (hok : E.Ok) {o : Nat} (ho : o ≤ E.code.length) :
    (BitVec.ofNat 64 (E.S.codeBase + o)).toNat = E.S.codeBase + o := by
  have := hok.valid.code_end
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

end Env

end Silmaril.X86.Backend

namespace Silmaril.X86.Backend

open Silmaril.Process (Memory)
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine
open Relation

variable {P : Type}

theorem keeps_rsp (A : Assign P) {c c' : State} {d : P} (hk : Keeps c c' (A.reg d)) :
    c'.read .rsp = c.read .rsp ∧ c'.read .r14 = c.read .r14 ∧ c'.read .r15 = c.read .r15 :=
  ⟨hk _ (by decide) (A.reg_ne_rsp d).symm, hk _ (by decide) (A.reg_ne_r14 d).symm,
    hk _ (by decide) (A.reg_ne_r15 d).symm⟩

theorem regs_set [DecidableEq P] (A : Assign P) {fr : Lir.Frame P} {c c' : State}
    (hr : ∀ q v, fr.regs q = some v → c.read (A.reg q) = v) {d : P} {z : Word}
    (hd : c'.read (A.reg d) = z) (hk : Keeps c c' (A.reg d)) :
    ∀ q v, (fr.set d z).regs q = some v → c'.read (A.reg q) = v := by
  intro q v hq
  simp only [Lir.Frame.regs_set] at hq
  by_cases h : q = d
  · subst h; simp at hq; rw [← hq, hd]
  · rw [ite_eq_right h] at hq
    rw [hk _ (A.not_scratch q) (fun e => h (A.reg_injective e)), hr q v hq]

namespace Env

variable (E : Env P) [DecidableEq P]

/-- What the code of an operation establishes. -/
structure OpPost (s : Lir.State P) (t : MState) (B : Nat) (fr : Lir.Frame P) (lm : Lir.Memory)
    (c : State) (m : Memory) : Prop where
  rsp : c.read .rsp = t.core.read .rsp
  r14 : c.read .r14 = t.core.read .r14
  r15 : c.read .r15 = t.core.read .r15
  regs : ∀ q v, fr.regs q = some v → c.read (E.A.reg q) = v
  slots : SlotsAt fr (E.ns s.point.func) B m
  mem : MemRel E.S lm m
  stack : ∀ x, E.S.InStack x → (x < B ∨ B + 8 * E.ns s.point.func ≤ x) →
    m.bytes.get? x = t.memory.bytes.get? x

theorem opPost_set {s : Lir.State P} {t : MState} {B : Nat} (hm : E.Body s t B) {d : P} {z : Word}
    {c : State} (hd : c.read (E.A.reg d) = z) (hk : Keeps t.core c (E.A.reg d)) :
    E.OpPost s t B (s.frame.set d z) s.mem c t.memory := by
  obtain ⟨h1, h2, h3⟩ := keeps_rsp E.A hk
  exact ⟨h1, h2, h3, regs_set E.A hm.regs hd hk, hm.slots, hm.mem, fun _ _ _ => rfl⟩

theorem frame_bounds (hok : E.Ok) {s : Lir.State P} {t : MState} {B : Nat} (hm : E.Body s t B)
    {fn : Lir.Func P} (hf : E.p.func? s.point.func = some fn) :
    need (E.ns s.point.func) < 2 ^ 31 ∧ B + frameSize (E.ns s.point.func) + 40 ≤ E.S.stackHi ∧
      E.S.stackLo + 8 ≤ B := by
  have := (funcOk hok.errors hf).frame
  rw [← E.ns_eq hf] at this
  exact ⟨this, by have := E.chain_top hm.chain; have := hok.e0_hi; omega, hm.low⟩

theorem run_op (hok : E.Ok) {s : Lir.State P} {t : MState} {B : Nat} (hm : E.Body s t B)
    {fn : Lir.Func P} (hf : E.p.func? s.point.func = some fn)
    {o : Lir.Op P} {fr : Lir.Frame P} {lm : Lir.Memory}
    (hslots : ∀ n ∈ opSlots o, n < E.ns s.point.func)
    (he : o.exec s.frame s.mem = some (fr, lm)) :
    ∃ c m, runSeq (selOp E.A o) t.core t.memory = some (c, m) ∧ E.OpPost s t B fr lm c m := by
  have hv := hok.valid
  obtain ⟨hneed, hhi, hlo⟩ := E.frame_bounds hok hm hf
  have hfs := frameSize_ge (E.ns s.point.func)
  unfold need at hneed
  cases o with
  | const d v =>
    simp only [Lir.Op.exec, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨_, _, runSeq_cons_of (Ext.exec_movabs _ _ _ _) (by intro h; cases h) rfl, ?_⟩
    exact E.opPost_set hm (by simp) (keeps_write _ _ _ _)
  | move d x =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨vx, hx, rfl, rfl⟩ := he
    refine ⟨_, _, runSeq_cons_of (Ext.exec_mov_reg _ _ _ _ _) (by intro h; cases h) rfl, ?_⟩
    exact E.opPost_set hm (by simp [hm.regs x vx hx]) (by
      intro r hr hrd; simp [State.read_write_other _ _ _ _ hrd])
  | unary op d x =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨vx, hx, rfl, rfl⟩ := he
    obtain ⟨c, hr, hd, hk⟩ := run_selUnop t.core t.memory op (E.A.reg d) (E.A.reg x)
    rw [hm.regs x vx hx] at hd
    exact ⟨c, _, hr, E.opPost_set hm hd hk⟩
  | binary op d x y =>
    simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨vx, hx, vy, hy, z, hz, rfl, rfl⟩ := he
    rw [← hm.regs x vx hx, ← hm.regs y vy hy] at hz
    obtain ⟨c, hr, hd, hk⟩ := run_selBinop t.core t.memory op (E.A.reg d) (E.A.reg x)
      (E.A.reg y) (E.A.not_scratch x) (E.A.not_scratch y) hz
    exact ⟨c, _, hr, E.opPost_set hm hd hk⟩
  | load w e d b off =>
    simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨vb, hb, z, hz, rfl, rfl⟩ := he
    rw [← hm.regs b vb hb] at hz
    obtain ⟨c, hr, hd, hk⟩ := run_loadOp hv t.core t.memory hm.good.regions hm.mem hm.r15 w e
      (E.A.reg d) (E.A.reg b) off (E.A.not_scratch b) hz
    exact ⟨c, _, hr, E.opPost_set hm hd hk⟩
  | store w b off x =>
    simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨vb, hb, vx, hx, lm', hst, rfl, rfl⟩ := he
    rw [← hm.regs b vb hb, ← hm.regs x vx hx] at hst
    obtain ⟨c, m, hr, hk, hrel, hout⟩ := run_storeOp hv t.core t.memory hm.good.regions hm.mem
      hm.r15 w (E.A.reg b) (E.A.reg x) off (E.A.not_scratch b) (E.A.not_scratch x) hst
    refine ⟨c, m, hr, hk _ (by decide), hk _ (by decide), hk _ (by decide),
      fun q v hq => by rw [hk _ (E.A.not_scratch q), hm.regs q v hq], ?_, hrel, ?_⟩
    · refine slotsAt_congr hm.slots (hi := B + 8 * E.ns s.point.func) (by omega) ?_
      intro x hx hx'
      apply hout
      simp only [Space.InMem]
      have := hv.stack_mem
      omega
    · intro x hx _
      apply hout
      simp only [Space.InMem]
      simp only [Space.InStack] at hx
      have := hv.stack_mem
      omega
  | slotGet d n =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨v, hn, rfl, rfl⟩ := he
    have hnl := hslots n (by simp [opSlots])
    have hw := hm.slots n v hnl hn
    have ex := stack_load hv hm.good.regions hm.rsp (d := 8 * n) (by omega) (by omega) (by omega)
      (E.A.reg d) hw
    refine ⟨_, _, runSeq_cons_of ex (by intro h; cases h) rfl, ?_⟩
    exact E.opPost_set hm (by simp) (keeps_write _ _ _ _)
  | slotSet n x =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨v, hx, rfl, rfl⟩ := he
    have hnl := hslots n (by simp [opSlots])
    obtain ⟨m, ex, hw, hwo⟩ := stack_store hv hm.good.regions hm.rsp (d := 8 * n) (by omega)
      (by omega) (by omega) (E.A.reg x)
    refine ⟨_, _, runSeq_cons_of ex (by intro h; cases h) rfl, by simp, by simp, by simp,
      fun q v hq => by simpa using hm.regs q v hq, ?_, ?_, ?_⟩
    · intro n' v' hn' hv'
      simp only [Lir.Frame.slots_setSlot] at hv'
      by_cases h : n' = n
      · subst h; simp at hv'; rw [← hv', ← hm.regs x v hx]; exact hw
      · rw [ite_eq_right h] at hv'
        exact (hm.slots n' v' hn' hv').of_writesOnly hwo (by omega)
    · exact hm.mem.congr fun a ha => hwo.2 a (by
        simp only [Space.InMem] at ha; have := hv.stack_mem; omega)
    · intro a _ ha
      exact hwo.2 a (by omega)

theorem selOp_ne_nil (o : Lir.Op P) : selOp E.A o ≠ [] := by
  cases o with
  | unary op d x => cases op <;> simp [selOp, selUnop]
  | binary op d x y => cases op <;> simp [selOp, selBinop, selAlu, selMul, selShift, selDiv, selCmp]
  | _ => simp [selOp]

theorem rip_of_toNat {c : State} {a : Nat} (h : c.rip.toNat = a) : c.rip = BitVec.ofNat 64 a := by
  rw [← h]; simp

/-- The instruction or terminator fetched at a point, located. -/
theorem fetch_instr {pt : Lir.Point} {i : Lir.Instr P}
    (hf : E.p.fetch pt = some (.instr i)) :
    ∃ fn b, E.p.func? pt.func = some fn ∧ fn.blocks[pt.label]? = some b ∧
      b.instrs[pt.index]? = some i := by
  obtain ⟨b, hb, h⟩ := Lir.Prog.fetch_eq_some hf
  obtain ⟨fn, hfn, hbl⟩ := E.func_block hb
  rcases h with ⟨i', hi', he⟩ | ⟨_, he⟩
  · cases he; exact ⟨fn, b, hfn, hbl, hi'⟩
  · cases he

/-- A compiled program has no floating-point instruction (`Error.floatOp`). -/
theorem fetch_ne_fop (hok : E.Ok) {pt : Lir.Point} {op : Lir.FOp} {d x y : P} :
    E.p.fetch pt ≠ some (.instr (.fop op d x y)) := by
  intro hf
  obtain ⟨fn, b, hfn, hbl, hi⟩ := E.fetch_instr hf
  have := (funcOk hok.errors hfn).instrs b (List.mem_of_getElem? hbl) _ (List.mem_of_getElem? hi)
  simp [instrErrors] at this

theorem fetch_term {pt : Lir.Point} {tm : Lir.Term P}
    (hf : E.p.fetch pt = some (.term tm)) :
    ∃ fn b, E.p.func? pt.func = some fn ∧ fn.blocks[pt.label]? = some b ∧
      pt.index = b.instrs.length ∧ b.term = tm := by
  obtain ⟨b, hb, h⟩ := Lir.Prog.fetch_eq_some hf
  obtain ⟨fn, hfn, hbl⟩ := E.func_block hb
  rcases h with ⟨i', hi', he⟩ | ⟨hl, he⟩
  · cases he
  · cases he; exact ⟨fn, b, hfn, hbl, hl, rfl⟩

theorem sim_op (hok : E.Ok) {s : Lir.State P} {t : MState} {B : Nat} (hm : E.Body s t B)
    {o : Lir.Op P} {fr : Lir.Frame P} {lm : Lir.Memory}
    (hf : E.p.fetch s.point = some (.instr (.op o))) (he : o.exec s.frame s.mem = some (fr, lm)) :
    ∃ t', TransGen (RStep E.exit) t t' ∧
      E.Body { s with point := s.point.next, frame := fr, mem := lm } t' B := by
  have hv := hok.valid
  obtain ⟨fn, b, hfn, hbl, hi⟩ := E.fetch_instr hf
  have hlt : s.point.index < b.instrs.length := (List.getElem?_eq_some_iff.mp hi).1
  have fok := funcOk hok.errors hfn
  have hslots : ∀ n ∈ opSlots o, n < E.ns s.point.func := by
    intro n hn; rw [E.ns_eq hfn]; exact slot_lt hbl hi (by simpa [instrSlots] using hn)
  obtain ⟨c, m, hr, post⟩ := E.run_op hok hm hfn hslots he
  have hci : s.point.index < (blockChunks E.A s.point.func (nslots fn) b).length := by
    rw [blockChunks_length]; omega
  obtain ⟨o', rest, hpa, hd, hbound⟩ := E.code_at hfn hbl hci
  have hchunk : (blockChunks E.A s.point.func (nslots fn) b)[s.point.index] =
      (selOp E.A o).map .plain := by
    rw [blockChunks_instr E.A _ _ b hlt, (List.getElem?_eq_some_iff.mp hi).2]; rfl
  rw [hchunk, encodeAt_plain] at hd
  rw [hchunk, lenOf_plain] at hbound
  have hrip : t.core.rip.toNat = E.S.codeBase + o' := by
    rw [hm.rip, hpa, E.rip_toNat hok (by omega)]
  obtain ⟨i₀, is, hcons⟩ := List.exists_cons_of_ne_nil (E.selOp_ne_nil o)
  rw [hcons] at hr hd hbound
  obtain ⟨steps, good, rip'⟩ := transGen_runSeq (exit := E.exit) hv hm.good hrip hd hr
  obtain ⟨hneed, hhi, hlo⟩ := E.frame_bounds hok hm hfn
  have hfs := frameSize_ge (E.ns s.point.func)
  refine ⟨_, steps, ⟨good, by rw [post.r15, hm.r15], by rw [post.r14, hm.r14],
    by rw [post.rsp, hm.rsp], hm.align, hm.low, ?_, post.mem, post.regs, post.slots, ?_⟩⟩
  · apply rip_of_toNat
    rw [rip']
    simp only [pa, Lir.Point.next]
    rw [pointAddr_succ E.A E.p E.S.codeBase hfn hbl hlt, (List.getElem?_eq_some_iff.mp hi).2]
    simp only [instrChunk, lenOf_plain, ← hcons]
    have : E.pa s.point = pointAddr E.A E.p E.S.codeBase ⟨s.point.func, s.point.label, s.point.index⟩ := rfl
    rw [← this, hpa]
  · apply E.chain_congr hm.chain
    intro x hx hx'
    have := E.chain_top hm.chain
    have := hok.e0_hi
    exact post.stack x ⟨by omega, by omega⟩ (by omega)

theorem signExtend_ofInt (d : Int) (h1 : d < 2 ^ 31) (h2 : -(2 ^ 31) ≤ d) :
    (BitVec.ofInt 32 d).signExtend 64 = BitVec.ofInt 64 d := by
  apply BitVec.toInt_inj.mp
  rw [BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_ofInt, BitVec.toInt_ofInt]
  rw [Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega),
    Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)]

/-- A resolved displacement reaches its target. -/
theorem rel32_ok (target next : Nat) (h1 : (target : Int) - next < 2 ^ 31)
    (h2 : -(2 ^ 31) ≤ (target : Int) - next) :
    BitVec.ofNat 64 next + (rel32 target next).signExtend 64 = BitVec.ofNat 64 target := by
  rw [rel32, signExtend_ofInt _ h1 h2, ← BitVec.ofInt_natCast, ← BitVec.ofInt_add,
    ← BitVec.ofInt_natCast]
  congr 1; omega

/-- The address of an existing block lies in the code. -/
theorem block_in_code {f : Lir.FuncId} {fn : Lir.Func P} (hf : E.p.func? f = some fn)
    {l : Lir.Label} (hl : l < fn.blocks.length) :
    ∃ o, E.L.block f l = E.S.codeBase + o ∧ o ≤ E.code.length := by
  have hb : fn.blocks[l]? = some fn.blocks[l] := List.getElem?_eq_getElem hl
  obtain ⟨o, rest, hpa, -, hle⟩ := E.code_at (pt := ⟨f, l, 0⟩) hf hb
    (by rw [blockChunks_length]; simp)
  refine ⟨o, ?_, by omega⟩
  rw [L, layout_block]; exact hpa

theorem jump_rip (hok : E.Ok) {f : Lir.FuncId} {fn : Lir.Func P} (hf : E.p.func? f = some fn)
    {l : Lir.Label} (hl : l < fn.blocks.length) {a : Nat} (ha : a ≤ E.S.codeBase + E.code.length) (hb : E.S.codeBase ≤ a) :
    BitVec.ofNat 64 a + (rel32 (E.L.block f l) a).signExtend 64 =
      BitVec.ofNat 64 (E.pa ⟨f, l, 0⟩) := by
  obtain ⟨o, ho, hle⟩ := E.block_in_code hf hl
  have := E.code_lt hok
  rw [rel32_ok _ _ (by omega) (by omega)]
  congr 1

theorem body_jump {s : Lir.State P} {t : MState} {B : Nat} (hm : E.Body s t B) (l : Lir.Label)
    {c : State} (hc : ∀ r, c.read r = t.core.read r)
    (hrip : c.rip = BitVec.ofNat 64 (E.pa ⟨s.point.func, l, 0⟩)) (hg : Good E.S E.code t.memory) :
    E.Body { s with point := ⟨s.point.func, l, 0⟩ } ⟨c, t.memory⟩ B :=
  ⟨hg, by rw [hc, hm.r15], by rw [hc, hm.r14], by rw [hc, hm.rsp], hm.align, hm.low, hrip, hm.mem,
    fun q v hq => by rw [hc, hm.regs q v hq], hm.slots, hm.chain⟩

theorem drop_after {code : List Byte} {o : Nat} {x rest : List Byte}
    (h : code.drop o = x ++ rest) : code.drop (o + x.length) = rest := by
  rw [← List.drop_drop, h, List.drop_left]

theorem drop_len {code : List Byte} {o : Nat} {x rest : List Byte}
    (h : code.drop o = x ++ rest) (hx : 0 < x.length) : o + x.length ≤ code.length := by
  have := congrArg List.length h
  simp only [List.length_drop, List.length_append] at this
  omega

theorem encode_jcc_length (cc : Ext.Cond) (r : BitVec 32) : (Ext.encode (.jcc cc r)).length = 6 := by
  cases cc <;> rfl

theorem toNat_code (hok : E.Ok) {a o : Nat} (ha : a = E.S.codeBase + o) (ho : o ≤ E.code.length) :
    (BitVec.ofNat 64 a).toNat = E.S.codeBase + o := by
  rw [ha]; exact E.rip_toNat hok ho

/-- A resolved JMP at `a` reaches its target. -/
theorem rstep_jmp (hok : E.Ok) {t : MState} (hg : Good E.S E.code t.memory) {a o : Nat}
    (ha : a = E.S.codeBase + o) (hrip : t.core.rip = BitVec.ofNat 64 a) {target : Nat}
    (hlo : E.S.codeBase ≤ target) (hhi : target ≤ E.S.codeBase + E.code.length) {rest : List Byte}
    (hd : E.code.drop o = Ext.encode (.jmp (rel32 target (a + 5))) ++ rest) :
    RStep E.exit t ⟨{ t.core with rip := BitVec.ofNat 64 target }, t.memory⟩ := by
  have hl5 : (Ext.encode (.jmp (rel32 target (a + 5)))).length = 5 := rfl
  have hlen := drop_len hd (by rw [hl5]; decide)
  have := E.code_lt hok
  have ex := Ext.exec_jmp t.core t.memory (rel32 target (a + 5))
  rw [hrip, show Ext.Instr.length (.jmp (rel32 target (a + 5))) = 5 from rfl, ← BitVec.ofNat_add,
    rel32_ok _ _ (by omega) (by omega)] at ex
  exact rstep_code hok.valid hg (by rw [hrip]; exact E.toNat_code hok ha (by omega)) hd ex
    (by intro h; cases h.1)

/-- A resolved Jcc at `a` with a defined condition. -/
theorem rstep_jcc (hok : E.Ok) {t : MState} (hg : Good E.S E.code t.memory) {a o : Nat}
    (ha : a = E.S.codeBase + o) (hrip : t.core.rip = BitVec.ofNat 64 a) {target : Nat}
    (hlo : E.S.codeBase ≤ target) (hhi : target ≤ E.S.codeBase + E.code.length) {rest : List Byte}
    {cc : Ext.Cond} (hd : E.code.drop o = Ext.encode (.jcc cc (rel32 target (a + 6))) ++ rest)
    {v : Bool} (hv : cc.eval t.core.flags = some v) :
    RStep E.exit t ⟨{ t.core with
      rip := if v then BitVec.ofNat 64 target else BitVec.ofNat 64 (a + 6) }, t.memory⟩ := by
  have hl6 : (Ext.encode (.jcc cc (rel32 target (a + 6)))).length = 6 := encode_jcc_length _ _
  have hlen := drop_len hd (by rw [hl6]; decide)
  have := E.code_lt hok
  have ex := Ext.exec_jcc t.core t.memory cc (rel32 target (a + 6)) v hv
  rw [hrip, show Ext.Instr.length (.jcc cc (rel32 target (a + 6))) = 6 from hl6,
    ← BitVec.ofNat_add, rel32_ok _ _ (by omega) (by omega)] at ex
  refine rstep_code hok.valid hg (by rw [hrip]; exact E.toNat_code hok ha (by omega)) hd ?_
    (by intro h; cases h.1)
  simpa only [Ext.Instr.length, hl6] using ex

theorem sim_jump (hok : E.Ok) {s : Lir.State P} {t : MState} {B : Nat} (hm : E.Body s t B)
    {l : Lir.Label} (hf : E.p.fetch s.point = some (.term (.jump l))) :
    ∃ t', TransGen (RStep E.exit) t t' ∧ E.Body { s with point := ⟨s.point.func, l, 0⟩ } t' B := by
  obtain ⟨fn, b, hfn, hbl, hidx, hterm⟩ := E.fetch_term hf
  have fok := funcOk hok.errors hfn
  have hl : l < fn.blocks.length := by
    have := fok.terms b (List.mem_of_getElem? hbl)
    rw [hterm] at this
    by_contra h; simp [termErrors, labelErrors, h] at this
  have hci : s.point.index < (blockChunks E.A s.point.func (nslots fn) b).length := by
    rw [blockChunks_length]; omega
  obtain ⟨o', rest, hpa, hd, hbound⟩ := E.code_at hfn hbl hci
  have hchunk : (blockChunks E.A s.point.func (nslots fn) b)[s.point.index] =
      [.jmp s.point.func l] := by
    simp only [hidx, blockChunks_term, hterm, termChunk]
  rw [hchunk] at hd
  simp only [encodeAt, AInstr.resolve, List.append_nil] at hd
  obtain ⟨ot, hot, hotl⟩ := E.block_in_code hfn hl
  have st := E.rstep_jmp hok hm.good hpa hm.rip (by omega) (by omega) hd
  exact ⟨_, TransGen.single st, E.body_jump hm l (fun r => rfl)
    (congrArg (BitVec.ofNat 64) (layout_block E.A E.p E.S.codeBase _ _)) hm.good⟩

theorem eval_ne_logic (x : Word) :
    Ext.Cond.eval (Ext.logicFlagsN (x &&& x)) .ne = some (!(x == 0)) := by
  simp [Ext.Cond.eval, Ext.logicFlagsN, Ext.kNot, Ext.isZeroN]

theorem sim_branch (hok : E.Ok) {s : Lir.State P} {t : MState} {B : Nat} (hm : E.Body s t B)
    {c : P} {l₁ l₂ : Lir.Label} {x : Word}
    (hf : E.p.fetch s.point = some (.term (.branch c l₁ l₂))) (hx : s.frame.get c = some x) :
    ∃ t', TransGen (RStep E.exit) t t' ∧
      E.Body { s with point := ⟨s.point.func, if x = 0 then l₂ else l₁, 0⟩ } t' B := by
  have hv := hok.valid
  obtain ⟨fn, b, hfn, hbl, hidx, hterm⟩ := E.fetch_term hf
  have fok := funcOk hok.errors hfn
  have hl : l₁ < fn.blocks.length ∧ l₂ < fn.blocks.length := by
    have := fok.terms b (List.mem_of_getElem? hbl)
    rw [hterm] at this
    simp only [termErrors, labelErrors, List.append_eq_nil_iff] at this
    constructor
    · by_contra h; rw [ite_eq_right h] at this; cases this.1
    · by_contra h; rw [ite_eq_right h] at this; cases this.2
  have hci : s.point.index < (blockChunks E.A s.point.func (nslots fn) b).length := by
    rw [blockChunks_length]; omega
  obtain ⟨o', rest, hpa, hd, hbound⟩ := E.code_at hfn hbl hci
  have hchunk : (blockChunks E.A s.point.func (nslots fn) b)[s.point.index] =
      [.plain (.test .q (.reg (E.A.reg c)) (E.A.reg c)), .jcc .ne s.point.func l₁,
        .jmp s.point.func l₂] := by
    simp only [hidx, blockChunks_term, hterm, termChunk]
  rw [hchunk] at hd
  simp only [encodeAt, AInstr.resolve, AInstr.len, List.append_nil, List.append_assoc] at hd
  generalize hlt : (Ext.encode (.test .q (.reg (E.A.reg c)) (E.A.reg c))).length = lt at hd
  have hvx : t.core.read (E.A.reg c) = x := hm.regs c x hx
  obtain ⟨o₁, ho₁, ho₁l⟩ := E.block_in_code hfn hl.1
  obtain ⟨o₂, ho₂, ho₂l⟩ := E.block_in_code hfn hl.2
  -- the TEST
  obtain ⟨c₁, hr₁, hf₁, hk₁, hip₁⟩ : ∃ c₁, runSeq [.test .q (.reg (E.A.reg c)) (E.A.reg c)]
      t.core t.memory = some (c₁, t.memory) ∧ c₁.flags = Ext.logicFlagsN (x &&& x) ∧
      (∀ r, c₁.read r = t.core.read r) ∧ c₁.rip = t.core.rip + BitVec.ofNat 64 lt :=
    ⟨_, (runSeq_cons_of (Ext.exec_test_reg _ _ _ _ _) (by intro h; cases h) rfl).trans rfl,
      by simp only [Ext.Sz.read_q, hvx]; rfl, fun r => rfl, by rw [← hlt]; rfl⟩
  have hd' := hd
  rw [← hlt] at hd'
  obtain ⟨st₁, -, -⟩ := transGen_runSeq (exit := E.exit) hv hm.good
    (by rw [hm.rip, hpa]; exact E.rip_toNat hok (by
      have := drop_len hd (Ext.encode_length _).1
      omega))
    (by simpa using hd') hr₁
  have hd₁ := drop_after hd'
  rw [hlt] at hd₁
  have hc₁rip : c₁.rip = BitVec.ofNat 64 (E.pa s.point + lt) := by
    rw [hip₁, hm.rip, BitVec.ofNat_add]
  have heval : Ext.Cond.eval c₁.flags .ne = some (!(x == 0)) := by rw [hf₁]; exact eval_ne_logic x
  have st₂ := E.rstep_jcc hok (t := ⟨c₁, t.memory⟩) hm.good (by rw [hpa]; omega) hc₁rip
    (by omega) (by omega) hd₁ heval
  by_cases hz : x = 0
  · simp only [hz, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false] at st₂
    have hd₂ := drop_after hd₁
    rw [encode_jcc_length] at hd₂
    have st₃ := E.rstep_jmp hok (t := ⟨{ c₁ with rip := BitVec.ofNat 64 (E.pa s.point + lt + 6) },
      t.memory⟩) hm.good (by rw [hpa]; omega) rfl
      (by omega) (by omega) hd₂
    refine ⟨_, TransGen.trans st₁ (TransGen.head st₂ (TransGen.single st₃)), ?_⟩
    simp only [hz, ite_true]
    exact E.body_jump hm l₂ (fun r => hk₁ r)
      (congrArg (BitVec.ofNat 64) (layout_block E.A E.p E.S.codeBase _ _)) hm.good
  · have hne : (!(x == 0)) = true := by
      rw [Bool.not_eq_true', beq_eq_false_iff_ne]; exact hz
    rw [hne] at st₂
    refine ⟨_, TransGen.trans st₁ (TransGen.single st₂), ?_⟩
    simp only [hz, ite_false]
    exact E.body_jump hm l₁ (fun r => hk₁ r)
      (congrArg (BitVec.ofNat 64) (layout_block E.A E.p E.S.codeBase _ _)) hm.good

theorem sim_trap (hok : E.Ok) {s : Lir.State P} {t : MState} {B : Nat} (hm : E.Body s t B)
    (hf : E.p.fetch s.point = some (.term .trap)) :
    Ext.step E.exit t = .trapped := by
  have hv := hok.valid
  obtain ⟨fn, b, hfn, hbl, hidx, hterm⟩ := E.fetch_term hf
  have hci : s.point.index < (blockChunks E.A s.point.func (nslots fn) b).length := by
    rw [blockChunks_length]; omega
  obtain ⟨o', rest, hpa, hd, hbound⟩ := E.code_at hfn hbl hci
  have hchunk : (blockChunks E.A s.point.func (nslots fn) b)[s.point.index] = [.plain .ud2] := by
    simp only [hidx, blockChunks_term, hterm, termChunk]
  rw [hchunk] at hd hbound
  simp only [encodeAt, AInstr.resolve, List.append_nil] at hd
  simp only [lenOf_cons, lenOf_nil, AInstr.len] at hbound
  have hrip : t.core.rip.toNat = E.S.codeBase + o' := by
    rw [hm.rip, hpa, E.rip_toNat hok (by omega)]
  rw [step_code hv hm.good hrip hd E.exit]
  rfl

end Env

end Silmaril.X86.Backend
