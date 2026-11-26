module

public import Silmaril.Proofs.X86.Concurrency.Cir.TvCfg.FxX86
public import Silmaril.Proofs.X86.Concurrency.Cir.TvCfg.Sound

/-!
# The translation validation: soundness

The simulation invariant `FInv` is `Inv` with two changes: the
registers agree only **outside the entry's junk registers** (`Agree`), and the entry's **known
values** hold of the CIR registers (`KnOk`).

* `tstep_transfer`: a CIR step of a leaf statement from the x86 registers is also a step from
  the CIR registers, with the same label, when the two agree on every register the statement
  reads. Afterwards they agree outside the junk minus the written register. All of this is on
  CIR, so the per-instruction x86 lemmas (`kind_sound`) are reused unchanged;
* `knOk_step`: the checker's known-value propagation (`postKn`) is sound;
* `fsim_step`, `fsim_run`, `tvFx_steps`: as `sim_step`, `sim_run`, `tvCfg_steps`, with the
  new kinds and the futex call.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.X86.Concurrency.Cir.TvCfg

open Silmaril.X86 (State)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (stepSym)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.TvCfg
open Silmaril.X86.Concurrency.Cir.TvCfg.Fx
open Silmaril.X86.Concurrency.Cir.Tv (XThread fetchAt)
open Silmaril.X86.Concurrency.Cir.Csl (TStep)
open Silmaril.X86.MemoryModel.Litmus (XAct)

/-! ## Agreement and known values -/

/-- The register files agree outside `J`. -/
def Agree (J : List Reg) (r1 r2 : Regs) : Prop := ∀ r, r ∉ J → r1 r = r2 r

/-- The known values hold. -/
def KnOk (kn : List (Reg × Word)) (rs : Regs) : Prop := ∀ p ∈ kn, rs p.1 = p.2

theorem eval_congr : ∀ (e : Expr) {r1 r2 : Regs}, (∀ r ∈ eregs e, r1 r = r2 r) →
    e.eval r1 = e.eval r2
  | .lit _, _, _, _ => rfl
  | .reg r, _, _, h => h r (by simp [eregs])
  | .bin o a b, _, _, h => by
    simp only [Expr.eval]
    rw [eval_congr a (fun r hr => h r (by simp [eregs, hr])),
      eval_congr b (fun r hr => h r (by simp [eregs, hr]))]

theorem avoid_spec {J l : List Reg} (h : avoid J l = true) {r : Reg} (hr : r ∈ l) : r ∉ J := by
  simp only [avoid, List.all_eq_true] at h
  have := h r hr
  simpa using this

theorem agree_on {J l : List Reg} {r1 r2 : Regs} (hA : Agree J r1 r2) (h : avoid J l = true) :
    ∀ r ∈ l, r1 r = r2 r := fun r hr => hA r (avoid_spec h hr)

theorem agree_mono {J J' : List Reg} {r1 r2 : Regs} (hA : Agree J r1 r2) (h : ∀ r ∈ J, r ∈ J') :
    Agree J' r1 r2 := fun r hr => hA r (fun hj => hr (h r hj))

theorem agree_set {J : List Reg} {r1 r2 : Regs} (hA : Agree J r1 r2) (d : Reg) (v : Word) :
    Agree (J.filter (· != d)) (r1.set d v) (r2.set d v) := by
  intro r hr
  simp only [Regs.set]
  split
  · rfl
  · rename_i hrd
    exact hA r (fun hj => hr (List.mem_filter.mpr ⟨hj, by simpa using hrd⟩))

theorem lookup_spec {kn : List (Reg × Word)} {r : Reg} {v : Word} (h : lookup kn r = some v) :
    (r, v) ∈ kn := by
  simp only [lookup, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some hp
  have hr := List.find?_some hp
  simp only [beq_iff_eq] at hr
  subst hr
  exact hm

theorem knOk_lookup {kn : List (Reg × Word)} {rs : Regs} (hk : KnOk kn rs) {r : Reg} {v : Word}
    (h : lookup kn r = some v) : rs r = v := hk _ (lookup_spec h)

theorem constE_sound {kn : List (Reg × Word)} {rs : Regs} (hk : KnOk kn rs) :
    ∀ (e : Expr) {v : Word}, constE kn e = some v → e.eval rs = v
  | .lit _, _, h => by simp only [constE, Option.some.injEq] at h; subst h; rfl
  | .reg r, _, h => by simp only [constE] at h; exact knOk_lookup hk h
  | .bin o a b, v, h => by
    simp only [constE] at h
    split at h
    · rename_i hx
      simp only [Bool.and_eq_true, beq_iff_eq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      simp only [Option.some.injEq] at h
      subst h
      simp [Expr.eval, BinOp.eval]
    · split at h
      · rename_i x y hx hy
        simp only [Option.some.injEq] at h
        subst h
        simp only [Expr.eval, constE_sound hk a hx, constE_sound hk b hy]
      · cases h

theorem knOk_drop {kn : List (Reg × Word)} {rs rs' : Regs} {d : Reg} (hk : KnOk kn rs)
    (h : ∀ r, r ≠ d → rs' r = rs r) : KnOk (dropR kn d) rs' := by
  intro p hp
  simp only [dropR, List.mem_filter, bne_iff_ne, ne_eq] at hp
  rw [h _ hp.2]; exact hk p hp.1

theorem knOk_mono {kn kn' : List (Reg × Word)} {rs : Regs} (hk : KnOk kn rs)
    (h : ∀ p ∈ kn', p ∈ kn) : KnOk kn' rs := fun p hp => hk p (h p hp)

/-! ## Leaf statements -/

/-- The leaf statements the checker emits. -/
def opF : Stmt → Bool
  | .assign .. | .load .. | .store .. | .rmw .. | .futexWait .. | .futexWake .. => true
  | _ => false

theorem rd_demode (a : Stmt) : rdRegs a.demode = rdRegs a := by cases a <;> rfl

theorem wr_demode (a : Stmt) : wrReg a.demode = wrReg a := by cases a <;> rfl

theorem opF_of_demode {a st : Stmt} (h : a.demode = st) (hst : opF st = true) : opF a = true := by
  cases a <;> simp only [Stmt.demode] at h <;> subst h <;> simp_all [opF]

theorem result_congr {r1 r2 : Regs} {sz old : Nat} {x : Word} :
    ∀ (op : RmwOp), (∀ r ∈ (match op with | .cas e => eregs e | _ => []), r1 r = r2 r) →
      op.result r1 sz old x = op.result r2 sz old x
  | .xchg, _ | .fadd, _ | .op _, _ => rfl
  | .cas e, h => by simp only [RmwOp.result]; rw [eval_congr e h]

/-- The registers a leaf step leaves alone. -/
theorem set_ne {rs : Regs} {d r : Reg} {v : Word} (h : r ≠ d) : rs.set d v r = rs r := by
  simp [Regs.set, h]

theorem tstep_keeps {a : Stmt} (ha : opF a = true) {rs : Regs} {o : Option Lab} {a' : Stmt}
    {rs' : Regs} (h : TStep a rs o a' rs') : ∀ r, wrReg a ≠ some r → rs' r = rs r := by
  intro r hr
  cases a <;> simp [opF] at ha <;> cases h <;> simp only [wrReg] at hr
  all_goals first
    | rfl
    | exact set_ne (fun e => hr (by rw [e]))

/-- **Transfer of a leaf step** from registers `r1` to registers `r2` that agree outside `J`,
when the statement reads no register of `J`. -/
theorem tstep_transfer {a : Stmt} (ha : opF a = true) {J : List Reg} {r1 r2 : Regs}
    (hA : Agree J r1 r2) (hrd : ∀ r ∈ rdRegs a, r1 r = r2 r) {o : Option Lab} {a' : Stmt}
    {r1' : Regs} (h : TStep a r1 o a' r1') :
    ∃ r2', TStep a r2 o a' r2' ∧ Agree (postJunk J a) r1' r2' := by
  cases a <;> simp [opF] at ha <;> cases h
  case assign d e =>
    rw [eval_congr e (fun r hr => hrd r (by simpa [rdRegs] using hr))]
    exact ⟨_, .assign, agree_set hA d _⟩
  case load d m sz fl e v hv =>
    rw [eval_congr e (fun r hr => hrd r (by simpa [rdRegs] using hr))]
    exact ⟨_, .load hv, agree_set hA d _⟩
  case store m sz fl e v =>
    rw [eval_congr e (fun r hr => hrd r (by simp [rdRegs, hr])),
      eval_congr v (fun r hr => hrd r (by simp [rdRegs, hr]))]
    exact ⟨_, .store, hA⟩
  case rmw d m sz op e arg old hv =>
    rw [eval_congr e (fun r hr => hrd r (by simp [rdRegs, hr])),
      eval_congr arg (fun r hr => hrd r (by simp [rdRegs, hr])),
      result_congr op (fun r hr => hrd r (by simp only [rdRegs, List.mem_append]; exact Or.inr hr))]
    exact ⟨_, .rmw hv, agree_set hA d _⟩
  case futexWait d e v seen rr hv hr =>
    rw [eval_congr e (fun r hr => hrd r (by simp [rdRegs, hr])),
      eval_congr v (fun r hr => hrd r (by simp [rdRegs, hr]))]
    exact ⟨_, .fwait hv hr, agree_set hA d _⟩
  case futexWake e n q hq =>
    rw [eval_congr e (fun r hr => hrd r (by simp [rdRegs, hr])),
      eval_congr n (fun r hr => hrd r (by simp [rdRegs, hr]))]
    exact ⟨_, .fwake hq, hA⟩

/-- **Known values after a leaf step.** -/
theorem knOk_step {a : Stmt} (ha : opF a = true) {kn : List (Reg × Word)} {rs : Regs}
    (hk : KnOk kn rs) {o : Option Lab} {a' : Stmt} {rs' : Regs} (h : TStep a rs o a' rs') :
    KnOk (postKn kn a) rs' := by
  have hkeep := tstep_keeps ha h
  cases a <;> simp [opF] at ha
  case assign d e =>
    cases h
    simp only [postKn]
    have hdrop : KnOk (dropR kn d) (rs.set d (e.eval rs)) :=
      knOk_drop hk (fun r hr => by simp [Regs.set, hr])
    split
    · rename_i v hv
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simp [Regs.set, constE_sound hk e hv]
      · exact hdrop p hp
    · exact hdrop
  all_goals
    simp only [postKn, wrReg]
    first
    | exact knOk_drop hk (fun r hr => hkeep r (by simp [wrReg]; exact fun e => hr e.symm))
    | exact fun p hp => by rw [hkeep p.1 (by simp [wrReg])]; exact hk p hp

/-! ## Entries -/

/-- **The simulation invariant** at entry `e` with fuel `F`. -/
structure FInv (t : XThread) (e : FEntry) (F : Nat) (s : State) (σ : Stmt) (rs : Regs) : Prop where
  rip : s.rip = t.base + BitVec.ofNat 64 e.off
  regs : Agree e.junk (regsOf s) rs
  kn : KnOk e.kn rs
  zf : ∀ z, e.zf = some z → s.flags.zero = some (truthy (z.eval rs))
  cir : (flat σ).map erase = e.cir.map erase
  bnd : ∀ x ∈ flat σ, bge F x

theorem hasEF_spec {E : List FEntry} {o : Nat} {k : List Stmt} {z : Option Expr}
    {kn : List (Reg × Word)} {junk : List Reg} (h : hasEF E o k z kn junk = true) :
    ∃ e ∈ E, e.off = o ∧ e.cir.map erase = k.map erase ∧ e.zf = z ∧
      (∀ p ∈ e.kn, p ∈ kn) ∧ (∀ r ∈ junk, r ∈ e.junk) := by
  simp only [hasEF, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨e, he, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩⟩ := h
  exact ⟨e, he, h1, lbeq_eq h2, h3, h4, h5⟩

/-- Build the invariant at a successor entry found by `hasEF`. -/
theorem finv_at {t : XThread} {e' : FEntry} {F : Nat} {s' : State} {σ' : Stmt} {rs' : Regs}
    {o : Nat} {k : List Stmt} {zf : Option Expr} {kn : List (Reg × Word)} {junk : List Reg}
    (ho : e'.off = o) (hc : e'.cir.map erase = k.map erase) (hz : e'.zf = zf)
    (hkn : ∀ p ∈ e'.kn, p ∈ kn) (hj : ∀ r ∈ junk, r ∈ e'.junk)
    (hrip : s'.rip = t.base + BitVec.ofNat 64 o) (hag : Agree junk (regsOf s') rs')
    (hk : KnOk kn rs') (hzf : ∀ z, zf = some z → s'.flags.zero = some (truthy (z.eval rs')))
    (hcir : (flat σ').map erase = k.map erase) (hb : ∀ x ∈ flat σ', bge F x) :
    FInv t e' F s' σ' rs' :=
  ⟨by rw [ho]; exact hrip, agree_mono hag hj, knOk_mono hk hkn,
    fun z h => hzf z (hz ▸ h), by rw [hcir, hc], hb⟩

theorem tvFx_parts {t : XThread} {c : FCert} (hc : tvFx t c = true) :
    t.code.length < 2 ^ 64 ∧
    (∀ e ∈ c.entries, e.off ≤ t.code.length ∧ chkEntryF t c.entries e = true) ∧
    hasEF c.entries 0 c.start none [] [] = true ∧ ∀ x ∈ c.start, leafB x = true := by
  simp only [tvFx, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  exact ⟨h1, h2, h3, h4⟩

theorem rip_off {t : XThread} {s : State} {o : Nat} (h : s.rip = t.base + BitVec.ofNat 64 o)
    (ho : o < 2 ^ 64) : (s.rip - t.base).toNat = o := by
  have e : t.base + BitVec.ofNat 64 o - t.base = BitVec.ofNat 64 o := by bv_omega
  rw [h, e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]

/-! ## Inversion of the instruction table -/

theorem fxKindOf_base {i : Atomic9.Instr} {k : Kind} (h : fxKindOf i = some (.base k)) :
    kindOf i = some k := by
  unfold fxKindOf at h
  split at h
  · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h; cases h
  · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h; cases h
  · cases h
  · cases h
  · simp only [Option.map_eq_some_iff, FKind.base.injEq] at h
    obtain ⟨k', hk, rfl⟩ := h; exact hk

theorem kindOf_ne_cas {i : Atomic9.Instr} {x : FKind} (h : (kindOf i).map FKind.base = some x)
    (hx : ∀ k, x ≠ .base k) : False := by
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨k, -, rfl⟩ := h
  exact hx k rfl

theorem fxKindOf_cas {i : Atomic9.Instr} {a : Expr} {src : Reg}
    (h : fxKindOf i = some (.cas a src)) :
    ∃ m, i = .new (.cmpxchg .d true (.mem m) src) ∧ addrX m = some a := by
  unfold fxKindOf at h
  split at h
  · simp only [Option.map_eq_some_iff, FKind.cas.injEq] at h
    obtain ⟨_, hm, rfl, rfl⟩ := h; exact ⟨_, rfl, hm⟩
  · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h; cases h
  · cases h
  · cases h
  · exact (kindOf_ne_cas h (fun _ e => by cases e)).elim

theorem fxKindOf_sub {i : Atomic9.Instr} {a : Expr} {imm : BitVec 32}
    (h : fxKindOf i = some (.lockSub a imm)) :
    ∃ m, i = .new (.lockAluI .d .sub m imm) ∧ addrX m = some a := by
  unfold fxKindOf at h
  split at h
  · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h; cases h
  · simp only [Option.map_eq_some_iff, FKind.lockSub.injEq] at h
    obtain ⟨_, hm, rfl, rfl⟩ := h; exact ⟨_, rfl, hm⟩
  · cases h
  · cases h
  · exact (kindOf_ne_cas h (fun _ e => by cases e)).elim

theorem fxKindOf_mov64 {i : Atomic9.Instr} {d src : Reg} (h : fxKindOf i = some (.mov64 d src)) :
    i = .open9 (.ext8 (.base (.mov .q (.reg d) src))) := by
  unfold fxKindOf at h
  split at h
  · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h; cases h
  · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h; cases h
  · simp only [Option.some.injEq, FKind.mov64.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · cases h
  · exact (kindOf_ne_cas h (fun _ e => by cases e)).elim

theorem fxKindOf_ret {i : Atomic9.Instr} (h : fxKindOf i = some .ret) :
    i = .open9 (.ext8 (.base .ret)) := by
  unfold fxKindOf at h
  split at h
  · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h; cases h
  · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h; cases h
  · cases h
  · rfl
  · exact (kindOf_ne_cas h (fun _ e => by cases e)).elim

theorem kindOf_opF {i : Atomic9.Instr} {st : Stmt} (h : kindOf i = some (.op st)) :
    opF st = true := by
  have := kindOf_op h
  cases st <;> simp_all [opLeaf, opF]

/-! ## The futex call -/

theorem sbeq_wait {a : Stmt} (h : sbeq a waitStmt = true) : a = waitStmt := sbeq_eq h

theorem sbeq_wake {a : Stmt} (h : sbeq a wakeStmt = true) : a = wakeStmt := sbeq_eq h

/-- The registers after a futex call: all but `rax`, `rcx`, `r11` are kept. -/
theorem sys_regs (s : State) (va vc v11 : Word) (fl : Silmaril.X86.Flags) (rip : Word) :
    ∀ r, r ∉ clob → regsOf { (((s.write .rax va).write .rcx vc).write .r11 v11) with
      rip := rip, flags := fl } r = regsOf s r := by
  intro r hr
  simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3⟩ := hr
  show (((s.write .rax va).write .rcx vc).write .r11 v11).read r = s.read r
  rw [State.read_write, State.read_write, State.read_write]
  simp [h1, h2, h3]

/-- The entry a conditional jump reaches (the analogue of `jcc_entry`). -/
theorem jccF_entry {E : List FEntry} {ne : Bool} {tk ft : Nat} {z c : Expr} {kt kf : List Stmt}
    {kn : List (Reg × Word)} {junk : List Reg} (h : jccOkF E ne tk ft z c kt kf kn junk = true)
    (rs : Regs) :
    ∃ e' ∈ E, e'.off = (if truthy (z.eval rs) != ne then tk else ft) ∧
      e'.cir.map erase = (if truthy (c.eval rs) then kt else kf).map erase ∧ e'.zf = none ∧
      (∀ p ∈ e'.kn, p ∈ kn) ∧ (∀ r ∈ junk, r ∈ e'.junk) := by
  simp only [jccOkF, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨rfl, h1⟩, h2⟩ | ⟨⟨rfl, h1⟩, h2⟩
  · cases hz : truthy (c.eval rs) <;> cases ne <;>
      simp only [Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, Bool.bne_false,
        Bool.bne_true, Bool.not_false] at h1 h2 ⊢ <;>
      first
      | exact hasEF_spec h1
      | exact hasEF_spec h2
  · rw [truthy_notE]
    cases hz : truthy (z.eval rs) <;> cases ne <;>
      simp only [Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, Bool.bne_false,
        Bool.bne_true, Bool.not_false] at h1 h2 ⊢ <;>
      first
      | exact hasEF_spec h1
      | exact hasEF_spec h2

/-! ## One step -/

/-- **One x86 step** from an entry is a CIR run of at most one label to an entry. -/
theorem fsim_step {t : XThread} {c : FCert} (hc : tvFx t c = true) {e : FEntry}
    (he : e ∈ c.entries) {F : Nat} {s : State} {σ : Stmt} {rs : Regs}
    (I : FInv t e (F + 1) s σ rs) {acts : List XAct} {s' : State} (hx : FStep t s acts s') :
    ∃ e' ∈ c.entries, ∃ σ' rs', ∃ o : Option Lab, TRun σ rs o.toList σ' rs' ∧
      acts = o.toList.flatMap Lab.acts ∧ FInv t e' F s' σ' rs' := by
  obtain ⟨hlen, hall, -, -⟩ := tvFx_parts hc
  obtain ⟨hoff, hchk⟩ := hall e he
  have hlt : e.off < 2 ^ 64 := Nat.lt_of_le_of_lt hoff hlen
  have hbF : ∀ x ∈ flat σ, bge F x := fun x hx => bge_mono (Nat.le_succ F) (I.bnd x hx)
  have hro := rip_off I.rip hlt
  unfold chkEntryF at hchk
  simp only [Bool.and_eq_true, List.all_eq_true] at hchk
  obtain ⟨hjc, hchk⟩ := hchk
  have hjc' : ∀ x ∈ e.junk, x ∈ clob := fun x hx => by simpa using hjc x hx
  split at hchk
  · -- the end of the code: no step
    rename_i hend
    exfalso
    rcases hx with ⟨dom, outs, hs, -⟩ | ⟨hsys, -⟩
    · have hfe : fetchAt t e.off = none := hend ▸ fetchAt_end t
      have := fetch_of_fetchAt hfe I.rip hlt
      simp [stepSym, this] at hs
    · rw [hro] at hsys
      simp [isSysAt, hend] at hsys
  split at hchk
  · -- a futex call
    rename_i hne hsysAt
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hchk
    obtain ⟨hfn, hchk⟩ := hchk
    rcases hx with ⟨dom, outs, hs, -⟩ | ⟨-, hax, hr10, l, va, vc, v11, fl, hl, hacts, rfl⟩
    · exfalso
      have := fetch_of_fetchAt hfn I.rip hlt
      simp [stepSym, this] at hs
    unfold chkSys at hchk
    split at hchk
    · rename_i a rest hcir
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hchk
      obtain ⟨⟨⟨⟨hav, hlax⟩, hl10⟩, hop⟩, hh⟩ := hchk
      obtain ⟨e', he', ho', hc', hz', hk', hj'⟩ := hasEF_spec hh
      have hag := agree_on I.regs hav
      have hrdi := hag .rdi (by simp)
      have hrdx := hag .rdx (by simp)
      have hrsi := hag .rsi (by simp)
      obtain ⟨a', rest', hfl, ha', hr'⟩ := map_erase_cons (I.cir.trans (by rw [hcir]))
      -- the CIR step of the futex statement, from the CIR registers
      have hstep : ∃ rs', TStep a' rs (some l) .skip rs' ∧ Agree clob (regsOf
          { (((s.write .rax va).write .rcx vc).write .r11 v11) with
            rip := s.rip + BitVec.ofNat 64 2, flags := fl }) rs' ∧
          KnOk (e.kn.filter fun p => !clob.contains p.1) rs' := by
        rcases hop with ⟨hsi, hw⟩ | ⟨hsi, hw⟩
        · have haw := sbeq_wait hw
          subst haw
          have ha'w : a' = waitStmt :=
            erase_eq_leaf ha' (fun _ _ e => by cases e) (fun _ _ _ e => by cases e)
              (fun _ _ _ e => by cases e)
          subst ha'w
          have hsi' : s.read .rsi = 128 := by
            rw [show s.read .rsi = regsOf s .rsi from rfl, hrsi, knOk_lookup I.kn hsi]
          rcases hl with ⟨-, seen, r, hseen, hr, rfl⟩ | ⟨h129, -⟩
          · have e1 : s.read .rdi = rs .rdi := hrdi
            have e2 : s.read .rdx = rs .rdx := hrdx
            rw [e1, e2]
            refine ⟨_, .fwait (d := .rax) (a := .reg .rdi) (v := .reg .rdx) hseen hr, ?_, ?_⟩
            · intro x hx
              rw [sys_regs s va vc v11 fl _ x hx]
              simp only [Regs.set]
              have : x ≠ .rax := by intro e; subst e; simp [clob] at hx
              simp only [this, ite_false]
              exact I.regs x (fun hj => hx (hjc' x hj))
            · intro p hp
              simp only [List.mem_filter] at hp
              have : p.1 ≠ .rax := by
                intro e; have := hp.2; rw [e] at this; simp [clob] at this
              simp only [Regs.set, this, ite_false]
              exact I.kn p hp.1
          · rw [hsi'] at h129; cases h129
        · have haw := sbeq_wake hw
          subst haw
          have ha'w : a' = wakeStmt :=
            erase_eq_leaf ha' (fun _ _ e => by cases e) (fun _ _ _ e => by cases e)
              (fun _ _ _ e => by cases e)
          subst ha'w
          have hsi' : s.read .rsi = 129 := by
            rw [show s.read .rsi = regsOf s .rsi from rfl, hrsi, knOk_lookup I.kn hsi]
          rcases hl with ⟨h128, -⟩ | ⟨-, q, hq, rfl⟩
          · rw [hsi'] at h128; cases h128
          · have e1 : s.read .rdi = rs .rdi := hrdi
            have e2 : s.read .rdx = rs .rdx := hrdx
            rw [e1, e2]
            refine ⟨_, .fwake (a := .reg .rdi) (n := .reg .rdx) hq, ?_, ?_⟩
            · intro x hx
              rw [sys_regs s va vc v11 fl _ x hx]
              exact I.regs x (fun hj => hx (hjc' x hj))
            · intro p hp
              simp only [List.mem_filter] at hp
              exact I.kn p hp.1
      obtain ⟨rs', hst, hagr, hkn⟩ := hstep
      obtain ⟨σ', hrun, hfl'⟩ := head_step hfl hst
      refine ⟨e', he', σ', rs', some l, hrun, by simpa using hacts,
        finv_at ho' hc' hz' hk' hj' ?_ hagr hkn
        (fun z h => by cases h) ?_ ?_⟩
      · show s.rip + BitVec.ofNat 64 2 = _
        exact rip_next I.rip
      · rw [hfl']; simpa [flat] using hr'
      · rw [hfl']; intro x hx
        exact hbF x (by rw [hfl]; exact List.mem_cons_of_mem _ (by simpa [flat] using hx))
    · cases hchk
  · -- a decoded instruction
    rename_i hne hnsys
    rcases hx with ⟨dom, outs, hs, ho⟩ | ⟨hsys, -⟩
    swap
    · exfalso; rw [hro] at hsys; exact hnsys hsys
    split at hchk
    · cases hchk
    rename_i i n hfa
    have hf := fetch_of_fetchAt hfa I.rip hlt
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨-, hchk⟩ := hchk
    split at hchk
    · cases hchk
    · -- an existing form
      rename_i k hk
      have hk' := fxKindOf_base hk
      have hks := kind_sound hk' hf hs ho
      cases k with
      | op st =>
        simp only [chkBase] at hchk
        split at hchk
        · rename_i a rest hcir
          simp only [Bool.and_eq_true] at hchk
          obtain ⟨⟨hab, hav⟩, hh⟩ := hchk
          obtain ⟨e', he', ho', hc', hz', hk2, hj'⟩ := hasEF_spec hh
          have hdm := sbeq_eq hab
          obtain ⟨a', rest', hfl, ha', hr'⟩ := map_erase_cons (I.cir.trans (by rw [hcir]))
          have hopl := kindOf_op hk'
          have haa : a' = a :=
            erase_eq_op ha' (opLeaf_of_demode hdm hopl) (erase_op hdm hopl)
          subst haa
          obtain ⟨o, rs1, hst, hacts, hrip, hregs⟩ := hks a' hdm
          have hopF : opF a' = true := opF_of_demode hdm (kindOf_opF hk')
          have hrd : ∀ r ∈ rdRegs a', regsOf s r = rs r := by
            rw [← rd_demode, hdm]; exact agree_on I.regs hav
          obtain ⟨rs', hst', hag'⟩ := tstep_transfer hopF I.regs hrd hst
          obtain ⟨σ', hrun, hfl'⟩ := head_step hfl hst'
          have hpj : postJunk e.junk a' = postJunk e.junk st := by
            simp only [postJunk, ← wr_demode a', hdm]
          have hpk : KnOk (postKn e.kn st) rs' := by
            have := knOk_step hopF I.kn hst'
            have hpk' : postKn e.kn a' = postKn e.kn st := by
              rw [← hdm]; cases a' <;> rfl
            rwa [hpk'] at this
          refine ⟨e', he', σ', rs', o, hrun, hacts, finv_at ho' hc' hz' hk2 hj' ?_ ?_ hpk
            (fun z h => by cases h) ?_ ?_⟩
          · rw [hrip]; exact rip_next I.rip
          · rw [hregs, ← hpj]; exact hag'
          · rw [hfl']; simpa [flat] using hr'
          · rw [hfl']; intro x hx
            exact hbF x (by rw [hfl]; exact List.mem_cons_of_mem _ (by simpa [flat] using hx))
        · cases hchk
      | flag z =>
        simp only [chkBase, Bool.and_eq_true] at hchk
        obtain ⟨hav, hh⟩ := hchk
        obtain ⟨hacts, hregs, hrip, hzf⟩ := hks
        obtain ⟨e', he', ho', hc', hz', hk2, hj'⟩ := hasEF_spec hh
        refine ⟨e', he', σ, rs, none, .refl, hacts, finv_at ho' hc' hz' hk2 hj' ?_ ?_ I.kn ?_
          I.cir hbF⟩
        · rw [hrip]; exact rip_next I.rip
        · rw [hregs]; exact I.regs
        · intro z' hz; cases hz
          rw [hzf, eval_congr z (agree_on I.regs hav)]
      | skip =>
        simp only [chkBase] at hchk
        obtain ⟨hacts, hregs, hrip⟩ := hks
        obtain ⟨e', he', ho', hc', hz', hk2, hj'⟩ := hasEF_spec hchk
        refine ⟨e', he', σ, rs, none, .refl, hacts, finv_at ho' hc' hz' hk2 hj' ?_ ?_ I.kn
          (fun z h => by cases h) I.cir hbF⟩
        · rw [hrip]; exact rip_next I.rip
        · rw [hregs]; exact I.regs
      | jmp rel =>
        simp only [chkBase] at hchk
        obtain ⟨hacts, hregs, hrip⟩ := hks
        obtain ⟨e', he', ho', hc', hz', hk2, hj'⟩ := hasEF_spec hchk
        refine ⟨e', he', σ, rs, none, .refl, hacts, finv_at ho' hc' hz' hk2 hj' ?_ ?_ I.kn
          (fun z h => by cases h) I.cir hbF⟩
        · rw [hrip]; exact rip_jump I.rip
        · rw [hregs]; exact I.regs
      | jcc ne rel =>
        simp only [chkBase] at hchk
        obtain ⟨hacts, hregs, b, hb, hrip⟩ := hks
        split at hchk
        · rename_i z a rest hzf hcir
          split at hchk
          · rename_i cnd kt kf hbr
            rw [I.zf z hzf, Option.some.injEq] at hb
            subst hb
            obtain ⟨a', rest', hfl, ha', hr'⟩ := map_erase_cons (I.cir.trans (by rw [hcir]))
            obtain ⟨a'', hst, hk1, hbd⟩ :=
              branch_step hbr ha' hr' (F := F) (by rw [← hfl]; exact I.bnd) rs
            obtain ⟨σ', hrun, hfl'⟩ := head_step hfl hst
            obtain ⟨e', he', ho', hc', hz', hk2, hj'⟩ := jccF_entry hchk rs
            refine ⟨e', he', σ', rs, none, hrun, hacts, finv_at ho' hc' hz' hk2 hj' ?_ ?_ I.kn
              (fun z h => by cases h) ?_ ?_⟩
            · rw [hrip]
              split
              · exact rip_jump I.rip
              · exact rip_next I.rip
            · rw [hregs]; exact I.regs
            · rw [hfl', hk1]
            · rw [hfl']; exact hbd
          · cases hchk
        · cases hchk
    · -- lock cmpxchg
      rename_i a src hk
      obtain ⟨m, rfl, hm⟩ := fxKindOf_cas hk
      split at hchk
      · rename_i h rest v hcir hv
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
        obtain ⟨⟨⟨hv32, hav⟩, hab⟩, hh⟩ := hchk
        obtain ⟨e', he', ho', hc', hz', hk2, hj'⟩ := hasEF_spec hh
        have hdm := sbeq_eq hab
        obtain ⟨a', rest', hfl, ha', hr'⟩ := map_erase_cons (I.cir.trans (by rw [hcir]))
        have hcl : opLeaf (casStmt a src) = true := rfl
        have haa : a' = h := erase_eq_op ha' (opLeaf_of_demode hdm hcl) (erase_op hdm hcl)
        subst haa
        have hag := agree_on I.regs hav
        have hraxv : rs .rax = v := knOk_lookup I.kn hv
        have hrax : s.read .rax = v := by
          rw [show s.read .rax = regsOf s .rax from rfl, hag .rax (by simp), hraxv]
        obtain ⟨o, rs1, hst, hacts, hrip, hregs, hzf⟩ :=
          cas_sound hm hf hs ho (by rw [hrax]; exact hv32) hdm
        have hopF : opF a' = true := by rw [← opF_of_demode hdm rfl]
        have hrd : ∀ r ∈ rdRegs a', regsOf s r = rs r := by
          rw [← rd_demode, hdm]
          intro r hr
          apply hag
          simp only [casStmt, rdRegs, eregs, List.mem_append, List.mem_cons, List.mem_singleton,
            List.not_mem_nil, or_false] at hr ⊢
          rcases hr with (hr | hr) | hr <;> simp_all
        obtain ⟨rs', hst', hag'⟩ := tstep_transfer hopF I.regs hrd hst
        obtain ⟨σ', hrun, hfl'⟩ := head_step hfl hst'
        have hpj : postJunk e.junk a' = postJunk e.junk (casStmt a src) := by
          simp only [postJunk, ← wr_demode a', hdm]
        have hpk : KnOk (dropR e.kn .rax) rs' := by
          have := knOk_step hopF I.kn hst'
          have hpk' : postKn e.kn a' = dropR e.kn .rax := by
            rw [← hdm] at hcl
            cases a' <;> simp_all [Stmt.demode, casStmt, postKn, wrReg]
          rwa [hpk'] at this
        refine ⟨e', he', σ', rs', o, hrun, hacts, finv_at ho' hc' hz' hk2 hj' ?_ ?_ hpk ?_ ?_ ?_⟩
        · rw [hrip]; exact rip_next I.rip
        · rw [hregs, ← hpj]; exact hag'
        · intro z hz
          cases hz
          rw [hzf, hrax]
          congr 2
          apply eval_congr
          intro r hr
          simp only [casZ, eregs, List.append_nil, List.mem_singleton] at hr
          subst hr
          apply hag'
          rw [hpj]; simp [postJunk, wrReg, casStmt]
        · rw [hfl']; simpa [flat] using hr'
        · rw [hfl']; intro x hx
          exact hbF x (by rw [hfl]; exact List.mem_cons_of_mem _ (by simpa [flat] using hx))
      · cases hchk
    · -- lock sub
      rename_i a imm hk
      obtain ⟨m, rfl, hm⟩ := fxKindOf_sub hk
      split at hchk
      · rename_i h rest hcir
        split at hchk
        · rename_i d a'' k hdem
          simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hchk
          obtain ⟨⟨⟨⟨hd, rfl⟩, rfl⟩, hav⟩, hh⟩ := hchk
          obtain ⟨e', he', ho', hc', hz', hk2, hj'⟩ := hasEF_spec hh
          obtain ⟨a', rest', hfl, ha', hr'⟩ := map_erase_cons (I.cir.trans (by rw [hcir]))
          have hcl : opLeaf h.demode = true := by rw [hdem]; rfl
          have haa : a' = h := erase_eq_op ha' (opLeaf_of_demode rfl hcl) (erase_op rfl hcl)
          subst haa
          obtain ⟨o, rs1, hst, hacts, hrip, hregs, hkeep, hzf⟩ := lockSub_sound hm hf hs ho hdem
          have hopF : opF a' = true := by rw [← opF_of_demode hdem rfl]
          have hag := agree_on I.regs hav
          have hrd : ∀ r ∈ rdRegs a', regsOf s r = rs r := by
            rw [← rd_demode, hdem]
            intro r hr
            apply hag
            simpa [rdRegs, eregs] using hr
          obtain ⟨rs', hst', hag'⟩ := tstep_transfer hopF I.regs hrd hst
          obtain ⟨σ', hrun, hfl'⟩ := head_step hfl hst'
          have hwr : wrReg a' = some d := by rw [← wr_demode, hdem]; rfl
          have hkeep' := tstep_keeps hopF hst'
          refine ⟨e', he', σ', rs', o, hrun, hacts, finv_at ho' hc' hz' hk2 hj' ?_ ?_
            (knOk_drop I.kn (fun r hr => hkeep' r (by rw [hwr]; exact fun e => hr (by
              cases e; rfl)))) ?_ ?_ ?_⟩
          · rw [hrip]; exact rip_next I.rip
          · intro r hr
            have hrd' : r ≠ d := by
              intro e; subst e; apply hr; split <;> simp_all
            have hrj : r ∉ e.junk := by
              intro hj; apply hr; split
              · exact hj
              · exact List.mem_cons_of_mem _ hj
            rw [hregs, ← hkeep r hrd']
            apply hag'
            simp only [postJunk, hwr, List.mem_filter, not_and]
            exact fun h => absurd h hrj
          · intro z hz
            cases hz
            rw [hzf]
            congr 2
            apply eval_congr
            intro r hr
            simp only [subZ, mask32, eregs, List.append_nil, List.mem_append,
              List.mem_singleton, List.not_mem_nil, or_false] at hr
            subst hr
            apply hag'
            simp [postJunk, hwr]
          · rw [hfl']; simpa [flat] using hr'
          · rw [hfl']; intro x hx
            exact hbF x (by rw [hfl]; exact List.mem_cons_of_mem _ (by simpa [flat] using hx))
        · cases hchk
      · cases hchk
    · -- mov r64, r64
      rename_i d src hk
      have hi := fxKindOf_mov64 hk
      subst hi
      split at hchk
      · rename_i h rest hcir
        simp only [Bool.and_eq_true] at hchk
        obtain ⟨⟨hab, hav⟩, hh⟩ := hchk
        obtain ⟨e', he', ho', hc', hz', hk2, hj'⟩ := hasEF_spec hh
        have hdm := sbeq_eq hab
        subst hdm
        obtain ⟨a', rest', hfl, ha', hr'⟩ := map_erase_cons (I.cir.trans (by rw [hcir]))
        have haa : a' = .assign d (.reg src) := erase_eq_op ha' rfl rfl
        subst haa
        obtain ⟨hacts, hrip, hregs⟩ := mov64_sound hf hs ho
        have hsrc : regsOf s src = rs src := agree_on I.regs hav src (by simp)
        obtain ⟨σ', hrun, hfl'⟩ := head_step hfl (TStep.assign (d := d) (e := .reg src) (rs := rs))
        refine ⟨e', he', σ', _, none, hrun, hacts, finv_at ho' hc' hz' hk2 hj' ?_ ?_
          (knOk_step rfl I.kn .assign) (fun z h => by cases h) ?_ ?_⟩
        · rw [hrip]; exact rip_next I.rip
        · rw [hregs]
          simp only [Expr.eval, hsrc]
          exact agree_set I.regs d _
        · rw [hfl']; simpa [flat] using hr'
        · rw [hfl']; intro x hx
          exact hbF x (by rw [hfl]; exact List.mem_cons_of_mem _ (by simpa [flat] using hx))
      · cases hchk
    · -- ret: no step
      rename_i hk
      have hi := fxKindOf_ret hk
      subst hi
      rw [ret_none hf] at hs
      cases hs

/-! ## Runs -/

/-- **Whole x86 runs** from an entry are CIR runs to an entry. -/
theorem fsim_run {t : XThread} {c : FCert} (hc : tvFx t c = true) {s : State}
    {acc : List (List XAct)} {s' : State} (hr : FRun t s acc s') :
    ∀ {e : FEntry}, e ∈ c.entries → ∀ {F : Nat} {σ : Stmt} {rs : Regs}, acc.length ≤ F →
      FInv t e F s σ rs → ∃ e' ∈ c.entries, ∃ σ' rs', ∃ los : List (Option Lab),
        TRun σ rs (los.filterMap id) σ' rs' ∧
        List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los ∧
        FInv t e' (F - acc.length) s' σ' rs' := by
  induction hr with
  | nil => intro e he F σ rs _ I; exact ⟨e, he, σ, rs, [], .refl, .nil, by simpa using I⟩
  | cons hx _ ih =>
    intro e he F σ rs hF I
    obtain ⟨G, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by simp at hF; omega⟩
    obtain ⟨e₁, he₁, σ₁, rs₁, o₁, hr₁, ha₁, I₁⟩ := fsim_step hc he I hx
    obtain ⟨e₂, he₂, σ₂, rs₂, l₂, hr₂, ha₂, I₂⟩ := ih he₁ (by simp at hF; omega) I₁
    refine ⟨e₂, he₂, σ₂, rs₂, o₁ :: l₂, ?_, .cons ha₁ ha₂, ?_⟩
    · have h := TRun.trans hr₁ hr₂
      cases o₁ <;> simpa using h
    · simpa [Nat.add_sub_add_right] using I₂

/-- **The cores a futex-code run reaches sit at entries** (the `rip` field of `FInv`). -/
theorem tvFx_reach {t : XThread} {c : FCert} (hc : tvFx t c = true) {s0 s : State}
    (h0 : s0.rip = t.base) {acc : List (List XAct)} (hr : FRun t s0 acc s) :
    ∃ e ∈ c.entries, s.rip = t.base + BitVec.ofNat 64 e.off := by
  obtain ⟨-, -, hstart, hleaf⟩ := tvFx_parts hc
  obtain ⟨e0, he0, ho0, hc0, hz0, hk0, -⟩ := hasEF_spec hstart
  have hflat : flat (c.body acc.length) = c.start.map (setB acc.length) := by
    rw [FCert.body, flat_setB, flat_chain hleaf]
  have I0 : FInv t e0 acc.length s0 (c.body acc.length) (regsOf s0) := by
    refine ⟨by rw [h0, ho0]; simp, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
    · intro p hp; exact absurd (hk0 p hp) (by simp)
    · intro z hz; rw [hz0] at hz; cases hz
    · rw [hflat, hc0, List.map_map]; congr 1; funext x; exact erase_setB _ x
    · rw [hflat]; intro x hx
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact bge_setB _ y
  obtain ⟨e', he', σ', rs', los, -, -, I⟩ := fsim_run hc hr he0 (Nat.le_refl _) I0
  exact ⟨e', he', I.rip⟩

/-- **Soundness of the checker, step by step.** -/
theorem tvFx_steps {t : XThread} {c : FCert} (hc : tvFx t c = true) {s0 s : State}
    (h0 : s0.rip = t.base) {acc : List (List XAct)} (hr : FRun t s0 acc s) {L : Nat}
    (hL : acc.length ≤ L) :
    ∃ σ rs, ∃ los : List (Option Lab), TRun (c.body L) (regsOf s0) (los.filterMap id) σ rs ∧
      List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los ∧
      (∀ r, r ∉ clob → regsOf s r = rs r) ∧ (Returned t s → σ = .skip) := by
  obtain ⟨hlen, hall, hstart, hleaf⟩ := tvFx_parts hc
  obtain ⟨e0, he0, ho0, hc0, hz0, hk0, -⟩ := hasEF_spec hstart
  have hflat : flat (c.body L) = c.start.map (setB L) := by
    rw [FCert.body, flat_setB, flat_chain hleaf]
  have I0 : FInv t e0 L s0 (c.body L) (regsOf s0) := by
    refine ⟨by rw [h0, ho0]; simp, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
    · intro p hp; exact absurd (hk0 p hp) (by simp)
    · intro z hz; rw [hz0] at hz; cases hz
    · rw [hflat, hc0, List.map_map]; congr 1; funext x; exact erase_setB L x
    · rw [hflat]; intro x hx
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact bge_setB L y
  obtain ⟨e', he', σ, rs, labs, hrun, hacts, I⟩ := fsim_run hc hr he0 hL I0
  have hjc : ∀ r ∈ e'.junk, r ∈ clob := by
    have := (hall e' he').2
    unfold chkEntryF at this
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at this
    exact this.1
  have hoff' : e'.off < 2 ^ 64 := Nat.lt_of_le_of_lt (hall e' he').1 hlen
  have hregs : ∀ r, r ∉ clob → regsOf s r = rs r :=
    fun r hr => I.regs r (fun hj => hr (hjc r hj))
  by_cases hret : Returned t s
  · have hce : e'.cir = [] := by
      have hck := (hall e' he').2
      unfold chkEntryF at hck
      simp only [Bool.and_eq_true] at hck
      obtain ⟨-, hck⟩ := hck
      rcases hret with hend | ⟨n, hfr⟩
      · have hoff : e'.off = t.code.length := by
          have h2 := congrArg BitVec.toNat
            (show BitVec.ofNat 64 e'.off = BitVec.ofNat 64 t.code.length by
              have h1 : t.base + BitVec.ofNat 64 e'.off =
                  t.base + BitVec.ofNat 64 t.code.length := by
                rw [← I.rip, hend]; rfl
              bv_omega)
          simp only [BitVec.toNat_ofNat] at h2
          rwa [Nat.mod_eq_of_lt hoff', Nat.mod_eq_of_lt hlen] at h2
        simp only [hoff, ↓reduceIte, List.isEmpty_iff] at hck
        exact hck
      · have hfa : fetchAt t e'.off = some (.open9 (.ext8 (.base .ret)), n) := by
          rw [← hfr]; exact (fetch_of_fetchAt rfl I.rip hoff').symm
        split at hck
        · simpa using hck
        split at hck
        · simp [hfa] at hck
        rw [hfa] at hck
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
        obtain ⟨-, hck⟩ := hck
        simpa [fxKindOf] using hck
    have hfn : flat σ = [] := by
      have := I.cir
      rw [hce, List.map_nil, List.map_eq_nil_iff] at this
      exact this
    refine ⟨.skip, rs, labs, ?_, hacts, hregs, fun _ => rfl⟩
    simpa using TRun.trans hrun (skip_of_flat_nil rs hfn)
  · exact ⟨σ, rs, labs, hrun, hacts, hregs, fun h => absurd h hret⟩

end Silmaril.Proofs.X86.Concurrency.Cir.TvCfg
