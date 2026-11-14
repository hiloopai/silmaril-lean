module

public import Silmaril.X86.Concurrency.Cir.Tv.Defs
public import Silmaril.X86.MemoryModel.Litmus.Models.Thms
public import Silmaril.X86.Concurrency.Cir.TvCfg.Defs

/-!
# Translation validation x86 → CIR: soundness

`tvRun_sound`: if the checker accepts a certificate for an x86
thread, then for every value domain whose values fit in 32 bits, every trace the extractor gives
for the bytes is a run of the certificate's CIR thread over the same domain, with the same memory
actions up to `normActs` and the same final registers outside the clobber set.

The pieces:

* runs of straight-line CIR (`Sim`): composition, singletons, and modes (`Sim.demode`);
* bytes: `leBytes w k = natBytes w.toNat k`, and `natBytes` only sees the value modulo
  `2^(8k)`;
* `addrE_eval`: the CIR address is the x86 effective address;
* `chk1_sound`: one instruction, by cases on the supported forms;
* `walk_sound`: induction on the certificate items, following `explore`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Tv

open Silmaril.X86 (State)
open Silmaril.X86.Ext (Sz leBytes leValue)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (stepSym memStep storeStep store8Step rmwStep explore extract
  consStep Trace StepRec valBytes ldVal writeOk readOk initCore)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Tv
open Silmaril.X86.MemoryModel.Litmus (XAct Model outsBy)

/-! ## Straight-line runs -/

/-- `ops` has a run from `rs` with lowered actions `acts` and final registers `rs'`. -/
def Sim (dom : List Nat) (rs : Regs) (ops : List Stmt) (acts : List XAct) (rs' : Regs) : Prop :=
  ∃ p ∈ run dom (chain ops) rs, p.1.flatMap Lab.acts = acts ∧ p.2 = rs'

theorem mem_run_seq {dom : List Nat} {s t : Stmt} {rs : Regs} {p : List Lab × Regs} :
    p ∈ run dom (.seq s t) rs ↔
      ∃ a ∈ run dom s rs, ∃ b ∈ run dom t a.2, p = (a.1 ++ b.1, b.2) := by
  simp only [run, Res.bind, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩

theorem Sim.nil {dom : List Nat} {rs : Regs} : Sim dom rs [] [] rs :=
  ⟨([], rs), by simp [chain, run], rfl, rfl⟩

theorem Sim.cons {dom : List Nat} {rs : Regs} {x : Stmt} {l : List Stmt} {p : List Lab × Regs}
    (hp : p ∈ run dom x rs) {acts : List XAct} {rs' : Regs} (h : Sim dom p.2 l acts rs') :
    Sim dom rs (x :: l) (p.1.flatMap Lab.acts ++ acts) rs' := by
  obtain ⟨q, hq, rfl, rfl⟩ := h
  exact ⟨(p.1 ++ q.1, q.2), mem_run_seq.mpr ⟨p, hp, q, hq, rfl⟩, by simp, rfl⟩

theorem Sim.cons_inv {dom : List Nat} {rs : Regs} {x : Stmt} {l : List Stmt} {acts : List XAct}
    {rs' : Regs} (h : Sim dom rs (x :: l) acts rs') :
    ∃ p ∈ run dom x rs, ∃ acts', Sim dom p.2 l acts' rs' ∧ acts = p.1.flatMap Lab.acts ++ acts' := by
  obtain ⟨q, hq, rfl, rfl⟩ := h
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_run_seq.mp hq
  exact ⟨a, ha, b.1.flatMap Lab.acts, ⟨b, hb, rfl, rfl⟩, by simp⟩

theorem Sim.single {dom : List Nat} {rs : Regs} {x : Stmt} {p : List Lab × Regs}
    (hp : p ∈ run dom x rs) : Sim dom rs [x] (p.1.flatMap Lab.acts) p.2 := by
  have := Sim.cons hp (Sim.nil (dom := dom) (rs := p.2))
  simpa using this

theorem Sim.append {dom : List Nat} {rs r₁ r₂ : Regs} {l₁ l₂ : List Stmt} {a₁ a₂ : List XAct}
    (h₁ : Sim dom rs l₁ a₁ r₁) (h₂ : Sim dom r₁ l₂ a₂ r₂) : Sim dom rs (l₁ ++ l₂) (a₁ ++ a₂) r₂ := by
  induction l₁ generalizing rs a₁ with
  | nil =>
    obtain ⟨q, hq, rfl, rfl⟩ := h₁
    simp only [chain, run, List.mem_singleton] at hq
    subst hq
    simpa using h₂
  | cons x l ih =>
    obtain ⟨p, hp, a', h', rfl⟩ := Sim.cons_inv h₁
    have := Sim.cons hp (ih h')
    simpa using this

theorem run_demode {dom : List Nat} {y : Stmt} {rs : Regs} {p : List Lab × Regs}
    (h : p ∈ run dom y.demode rs) :
    ∃ q ∈ run dom y rs, q.1.flatMap Lab.acts = p.1.flatMap Lab.acts ∧ q.2 = p.2 := by
  cases y with
  | load d m sz fl a =>
    simp only [Stmt.demode, run, List.mem_map] at h
    obtain ⟨v, hv, rfl⟩ := h
    exact ⟨_, List.mem_map_of_mem hv, by simp [Lab.acts], rfl⟩
  | store m sz fl a v =>
    simp only [Stmt.demode, run, List.mem_singleton] at h
    subst h
    exact ⟨_, List.mem_singleton_self _, by simp [Lab.acts], rfl⟩
  | rmw d m sz op a arg =>
    simp only [Stmt.demode, run, List.mem_map] at h
    obtain ⟨v, hv, rfl⟩ := h
    exact ⟨_, List.mem_map_of_mem hv, by simp [Lab.acts], rfl⟩
  | _ => exact ⟨p, h, rfl, rfl⟩

theorem Sim.demode {dom : List Nat} {rs : Regs} {ops : List Stmt} {acts : List XAct} {rs' : Regs}
    (h : Sim dom rs (ops.map Stmt.demode) acts rs') : Sim dom rs ops acts rs' := by
  induction ops generalizing rs acts with
  | nil => simpa using h
  | cons y l ih =>
    obtain ⟨p, hp, a', h', rfl⟩ := Sim.cons_inv h
    obtain ⟨q, hq, hqa, hq2⟩ := run_demode hp
    have := Sim.cons hq (ih (hq2 ▸ h'))
    rwa [hqa] at this

/-! ## Bytes -/

theorem leBytes_eq (w : BitVec 64) (k : Nat) : leBytes w k = natBytes w.toNat k := by
  apply List.ext_getElem
  · simp [natBytes]
  · intro j h₁ h₂
    simp only [leBytes, List.getElem_ofFn, natBytes, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_toNat_eq
    simp [Silmaril.Machine.LittleEndian.wordByte, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, pow_mul]

theorem natBytes_mod (x k : Nat) : natBytes (x % 2 ^ (8 * k)) k = natBytes x k := by
  apply List.ext_getElem
  · simp [natBytes]
  · intro j h₁ h₂
    simp only [natBytes, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    have hk : 2 ^ (8 * k) = 256 ^ j * 256 ^ (k - j) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      simp [natBytes] at h₁
      omega
    rw [hk, Nat.mod_mul_right_div_self]
    simp [natBytes] at h₁
    exact Nat.mod_mod_of_dvd _ (dvd_pow_self 256 (by omega))

theorem valBytes_eq {v k : Nat} (hv : v < 2 ^ 64) : valBytes v k = natBytes v k := by
  rw [valBytes, leBytes_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

theorem ldVal_valBytes (v : Nat) (k : Nat) : ldVal (valBytes v k) = BitVec.ofNat 64 (v % 2 ^ (8 * k)) := by
  simp only [ldVal, valBytes, Silmaril.X86.Ext.leValue_leBytes, BitVec.toNat_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rcases Nat.lt_or_ge k 8 with hk | hk
  · rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 8 * k ≤ 64))]
  · have h1 : v % 2 ^ 64 < 2 ^ (8 * k) :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.mod_eq_of_lt h1, Nat.mod_mod, Nat.mod_mod_of_dvd v (Nat.pow_dvd_pow 2 (by omega : 64 ≤ 8 * k))]

/-! ## Register files, values and addresses -/

theorem Sim.single' {dom : List Nat} {rs rs' : Regs} {x : Stmt} {p : List Lab × Regs}
    {acts : List XAct} (hp : p ∈ run dom x rs) (ha : p.1.flatMap Lab.acts = acts)
    (hr : p.2 = rs') : Sim dom rs [x] acts rs' := by
  subst ha hr; exact Sim.single hp

theorem Regs.set_apply (rs : Regs) (r q : Reg) (v : Word) :
    rs.set r v q = if q = r then v else rs q := rfl

@[simp] theorem Regs.set_self (rs : Regs) (r : Reg) (v : Word) : rs.set r v r = v := by
  simp [Regs.set_apply]

theorem Expr.eval_set {d : Reg} {v : Word} {rs : Regs} :
    ∀ {e : Expr}, d ∉ e.regs → e.eval (rs.set d v) = e.eval rs
  | .lit _, _ => rfl
  | .reg r, h => by
    simp only [Expr.regs, List.mem_singleton] at h
    simp [Expr.eval, Regs.set_apply, Ne.symm h]
  | .bin o a b, h => by
    simp only [Expr.regs, List.mem_append, not_or] at h
    simp [Expr.eval, Expr.eval_set h.1, Expr.eval_set h.2]

theorem addrE_eval {K : List Reg} {nx : Word} {a : XMem} {e : Expr} (h : addrE K nx a = some e)
    {rs : Regs} {s : State} (hr : ∀ r, r ∉ K → s.read r = rs r) {next : Word} (hnx : next = nx) :
    e.eval rs = a.addr s next := by
  unfold addrE at h
  split at h
  · rename_i hb hi
    cases h
    simp [Expr.eval, Silmaril.X86.Ext.Mem.addr, hb, hi]
  · rename_i r hb hi
    split at h
    · cases h
    · rename_i hK
      cases h
      simp [Expr.eval, BinOp.eval, Silmaril.X86.Ext.Mem.addr, hb, hi]
      exact (hr r hK).symm
  · rename_i hb hi
    cases h
    subst hnx
    simp only [Expr.eval, Silmaril.X86.Ext.Mem.addr, hb, hi, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, Option.map_none, Option.getD_none, BitVec.add_zero]
    simp
  · cases h

theorem sz_bytes_ge (sz : Sz) : 4 ≤ sz.bytes := by cases sz <;> decide

theorem sz_bytes_le (sz : Sz) : sz.bytes ≤ 8 := by cases sz <;> decide

/-- A value that fits the size of an access fits in 64 bits. -/
theorem lt64_k (sz : Sz) {v : Nat} (hv : v < 2 ^ (8 * sz.bytes)) : v < 2 ^ 64 :=
  Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by cases sz <;> decide))

theorem pick_mem_k {dom : List Nat} {v k : Nat} (hv : v ∈ dom) (hk : v < 2 ^ (8 * k)) :
    v ∈ pick dom k := by
  simp only [pick, List.mem_filter, decide_eq_true_eq]
  exact ⟨hv, hk⟩

theorem ofNat_toNat_lt (sz : Sz) {v : Nat} (hv : v < 2 ^ (8 * sz.bytes)) :
    (BitVec.ofNat sz.bits v).toNat = v := by
  rw [BitVec.toNat_ofNat, Sz.bits_eq, Nat.mod_eq_of_lt hv]

theorem ofNat_sw (sz : Sz) {v : Nat} (hv : v < 2 ^ (8 * sz.bytes)) :
    (BitVec.ofNat sz.bits v).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, ofNat_toNat_lt sz hv, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt64_k sz hv)]

theorem ldx (sz : Sz) {v : Nat} (hv : v < 2 ^ (8 * sz.bytes)) :
    (ldVal (valBytes v sz.bytes)).setWidth sz.bits = BitVec.ofNat sz.bits v := by
  rw [ldVal_valBytes]
  apply BitVec.eq_of_toNat_eq
  rw [Nat.mod_eq_of_lt hv, BitVec.toNat_setWidth, ofNat_toNat_lt sz hv, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt64_k sz hv), Sz.bits_eq, Nat.mod_eq_of_lt hv]

/-- The bytes of a value at size `k ≤ 8` only see it modulo `2 ^ (8 * k)`. -/
theorem valBytes_mod (v k : Nat) (hk : k ≤ 8) : valBytes (v % 2 ^ (8 * k)) k = valBytes v k := by
  simp only [valBytes, leBytes_eq, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by omega) (by omega))), natBytes_mod, ← natBytes_mod (v % 2 ^ 64),
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 8 * k ≤ 64)), natBytes_mod]

/-- The value of the bytes of `v` at size `k ≤ 8` is `v` modulo `2 ^ (8 * k)`. -/
theorem leValue_valBytes (v : Nat) {k : Nat} (hk : k ≤ 8) :
    leValue (valBytes v k) = v % 2 ^ (8 * k) := by
  rw [valBytes, Silmaril.X86.Ext.leValue_leBytes, BitVec.toNat_ofNat,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 8 * k ≤ 64))]

theorem leBytes_sw (sz : Sz) (x : BitVec sz.bits) :
    leBytes (x.setWidth 64) sz.bytes = natBytes x.toNat sz.bytes := by
  rw [leBytes_eq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by cases sz <;> decide))

theorem natBytes_sw (sz : Sz) (w : BitVec 64) :
    natBytes (w.setWidth sz.bits).toNat sz.bytes = natBytes w.toNat sz.bytes := by
  rw [BitVec.toNat_setWidth, Sz.bits_eq, natBytes_mod]

theorem read_post (s : State) (r q : Reg) (w next : Word) :
    ({ s.write r w with rip := next } : State).read q = if q = r then w else s.read q :=
  State.read_write s r q w

/-! ## Fetch and the two kinds of step -/

theorem fetch_of_fetchAt {t : XThread} {o : Nat} {i : Atomic9.Instr} {n : Nat}
    (hf : fetchAt t o = some (i, n)) {s : State} (hrip : s.rip = t.base + BitVec.ofNat 64 o)
    (ho : o < 2 ^ 64) : t.fetch s = some (i, n) := by
  have h : (s.rip - t.base).toNat = o := by
    have e : t.base + BitVec.ofNat 64 o - t.base = BitVec.ofNat 64 o := by bv_omega
    rw [hrip, e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  unfold Silmaril.X86.Litmus.Thread.fetch
  rw [h]
  exact hf

theorem stepSym_mem {t : XThread} {dom : List Nat} {s : State} {i : Atomic9.Instr} {n : Nat}
    (hf : t.fetch s = some (i, n))
    (hni : (MemEvent.atomic9Accesses i s n).all Litmus.Event.inert = false) :
    stepSym t dom s = memStep t.regions dom i s n := by
  simp [stepSym, hf, hni]

theorem stepSym_inert {t : XThread} {dom : List Nat} {s : State} {i : Atomic9.Instr} {n : Nat}
    (hf : t.fetch s = some (i, n))
    (hin : (MemEvent.atomic9Accesses i s n).all Litmus.Event.inert = true) {c : State}
    {m : Silmaril.Process.Memory} (hx : Atomic9.exec i s t.frame n = .ok c m) :
    stepSym t dom s = some [((MemEvent.atomic9Accesses i s n).map Litmus.Act.inert, c)] := by
  simp [stepSym, hf, hin, hx]

/-! ## The relation -/

theorem mem_drop {l : List Reg} {r q : Reg} : q ∈ drop l r ↔ q ∈ l ∧ q ≠ r := by
  simp [drop]

theorem Rel.mono {K Z K' Z' : List Reg} {rs : Regs} {s : State} (h : Rel K Z rs s)
    (hK : ∀ q, q ∈ K → q ∈ K') (hZ : ∀ q ∈ Z', q ∈ Z) : Rel K' Z' rs s :=
  ⟨fun q hq => h.eq q (fun h' => hq (hK q h')), fun q hq => h.fit q (hZ q hq)⟩

/-- The x86 registers did not change. -/
theorem Rel.same {K Z : List Reg} {rs : Regs} {s s' : State} (h : Rel K Z rs s)
    (hs : ∀ q, s'.read q = s.read q) : Rel K Z rs s' :=
  ⟨fun q hq => (hs q).trans (h.eq q hq), fun q hq => (hs q) ▸ h.fit q hq⟩

/-- Both sides wrote the same value below `2^32` to `r`. -/
theorem Rel.set {K Z : List Reg} {rs : Regs} {s s' : State} (h : Rel K Z rs s) (r : Reg) {v : Nat}
    (hv : v < 2 ^ 32) (hs : ∀ q, s'.read q = if q = r then BitVec.ofNat 64 v else s.read q) :
    Rel (drop K r) (r :: Z) (rs.set r (BitVec.ofNat 64 v)) s' := by
  constructor
  · intro q hq
    rw [hs q, Regs.set_apply]
    split
    · rfl
    · exact h.eq q (fun h' => hq (mem_drop.mpr ⟨h', by assumption⟩))
  · intro q hq
    rw [hs q]
    split
    · simp; omega
    · rcases List.mem_cons.mp hq with rfl | hq
      · contradiction
      · exact h.fit q hq

/-- CIR wrote a scratch register `d`; the x86 registers did not change. -/
theorem Rel.clob {K Z : List Reg} {rs : Regs} {s s' : State} (h : Rel K Z rs s) (d : Reg)
    (w : Word) (hs : ∀ q, s'.read q = s.read q) : Rel (d :: K) (drop Z d) (rs.set d w) s' := by
  constructor
  · intro q hq
    simp only [List.mem_cons, not_or] at hq
    rw [hs q, Regs.set_apply]
    simp only [hq.1, ite_false]
    exact h.eq q hq.2
  · intro q hq
    rw [hs q]
    exact h.fit q (mem_drop.mp hq).1

theorem normActs_single (a : XAct) (h : a.ev.kind ≠ .rmw ∨ a.ev.locked = true) :
    normActs [a] = [a] := by
  rcases h with h | h <;> simp [normActs, Act.norm, h]

theorem Rel.setw {K Z : List Reg} {rs : Regs} {s s' : State} (h : Rel K Z rs s) (r : Reg)
    (w : Word) (hs : ∀ q, s'.read q = if q = r then w else s.read q) :
    Rel (drop K r) (drop Z r) (rs.set r w) s' := by
  constructor
  · intro q hq
    rw [hs q, Regs.set_apply]
    split
    · rfl
    · exact h.eq q (fun h' => hq (mem_drop.mpr ⟨h', by assumption⟩))
  · intro q hq
    rw [hs q]
    simp only [(mem_drop.mp hq).2, ite_false]
    exact h.fit q (mem_drop.mp hq).1

/-- Both sides wrote the same word below `2^32` to `r`. -/
theorem Rel.setW {K Z : List Reg} {rs : Regs} {s s' : State} (h : Rel K Z rs s) (r : Reg)
    (w : Word) (hw : w.toNat < 2 ^ 32) (hs : ∀ q, s'.read q = if q = r then w else s.read q) :
    Rel (drop K r) (r :: Z) (rs.set r w) s' := by
  constructor
  · intro q hq
    rw [hs q, Regs.set_apply]
    split
    · rfl
    · exact h.eq q (fun h' => hq (mem_drop.mpr ⟨h', by assumption⟩))
  · intro q hq
    rw [hs q]
    split
    · exact hw
    · rcases List.mem_cons.mp hq with rfl | hq
      · contradiction
      · exact h.fit q hq

/-- Both sides wrote the same value of an access of size `sz` to `r`: it fits in
32 bits at size `.d`, so `r` joins the fitting set; at `.q` it need not, so `r` leaves it. -/
theorem Rel.setSz {K Z : List Reg} {rs : Regs} {s s' : State} (h : Rel K Z rs s) (sz : Sz)
    (r : Reg) {v : Nat} (hv : v < 2 ^ (8 * sz.bytes))
    (hs : ∀ q, s'.read q = if q = r then BitVec.ofNat 64 v else s.read q) :
    Rel (drop K r) (if sz = .d then r :: Z else drop Z r) (rs.set r (BitVec.ofNat 64 v)) s' := by
  cases sz
  · exact Rel.set h r (by have e : Sz.d.bytes = 4 := rfl; rw [e] at hv; exact hv) hs
  · exact Rel.setw h r _ hs

theorem setSz_sub_rax (sz : Sz) (Z : List Reg) :
    ∀ q ∈ (if sz = .d then Z else drop Z .rax),
      q ∈ (if sz = .d then Silmaril.X86.Reg.rax :: Z else drop Z .rax) := by
  intro q hq
  cases sz
  · exact List.mem_cons_of_mem _ (by simpa using hq)
  · simpa using hq

/-- The value of `szE`. -/
theorem szE_eval (sz : Sz) (e : Expr) (rs : Regs) :
    (szE sz e).eval rs = ((e.eval rs).setWidth sz.bits).setWidth 64 := by
  cases sz
  · apply BitVec.eq_of_toNat_eq
    simp only [szE, Expr.eval, BinOp.eval, mask32, BitVec.toNat_and, BitVec.toNat_setWidth]
    have : (BitVec.ofNat 64 4294967295).toNat = 2 ^ 32 - 1 := by decide
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
    simp [Sz.bits]
    omega
  · simp [szE]

theorem szE_fit (e : Expr) (rs : Regs) : ((szE .d e).eval rs).toNat < 2 ^ 32 := by
  rw [szE_eval]; simp; omega

theorem natBytes_congr {x y k : Nat} (h : x % 2 ^ (8 * k) = y % 2 ^ (8 * k)) :
    natBytes x k = natBytes y k := by
  rw [← natBytes_mod x, h, natBytes_mod]

theorem w_add (x y : BitVec 32) : (x.setWidth 64 + y.setWidth 64).setWidth 32 = x + y := by bv_omega
theorem w_sub (x y : BitVec 32) : (x.setWidth 64 - y.setWidth 64).setWidth 32 = x - y := by bv_omega
theorem w_and (x y : BitVec 32) : (x.setWidth 64 &&& y.setWidth 64).setWidth 32 = x &&& y := by
  ext i hi; simp
theorem w_or (x y : BitVec 32) : (x.setWidth 64 ||| y.setWidth 64).setWidth 32 = x ||| y := by
  ext i hi; simp
theorem w_xor (x y : BitVec 32) : (x.setWidth 64 ^^^ y.setWidth 64).setWidth 32 = x ^^^ y := by
  ext i hi; simp
theorem w64 (f : BitVec 64 → BitVec 64 → BitVec 64) (x y : BitVec 64) :
    f (x.setWidth 64) (y.setWidth 64) = f x y := by simp

/-- A locked ALU operation computed at 64 bits and cut to the operand size is the x86 result. -/
theorem aluI_val (op : Silmaril.X86.AluOp) (o : BinOp) (hb : binOf op = some o) (sz : Sz)
    (x y : BitVec sz.bits) :
    (o.eval (x.setWidth 64) (y.setWidth 64)).setWidth sz.bits =
      Silmaril.X86.Ext.AluOp.resultN op x y := by
  cases op <;> simp [binOf] at hb <;> subst hb <;> cases sz <;>
    simp only [BinOp.eval, Silmaril.X86.Ext.AluOp.resultN]
  all_goals first
    | exact w_add x y | exact w_sub x y | exact w_and x y | exact w_or x y | exact w_xor x y
    | exact w64 (· + ·) x y | exact w64 (· - ·) x y | exact w64 (· &&& ·) x y
    | exact w64 (· ||| ·) x y | exact w64 (· ^^^ ·) x y

/-! ## One instruction -/

theorem any_reads_demode (ops : List Stmt) :
    ops.any Stmt.reads = (ops.map Stmt.demode).any Stmt.reads := by
  induction ops with
  | nil => rfl
  | cons y l ih =>
    simp only [List.any_cons, List.map_cons, ih]
    congr 1
    cases y <;> rfl

/-- The value a read of `k ≤ 8` bytes returns, as CIR sees it: `v` modulo `2^(8k)`.
Either the CIR domain `D` holds the value of the bytes read, or it is the x86 domain and
that domain fits in 32 bits (the original hypothesis of `chk1_sound`). -/
theorem readVal {D dom : List Nat} {ops : List Stmt} {v k : Nat} (hk : 4 ≤ k) (hk8 : k ≤ 8)
    (hv : v ∈ dom) (hr : ops.any Stmt.reads = true)
    (hD : leValue (valBytes v k) ∈ D ∨
      (D = dom ∧ (ops.any Stmt.reads = true → ∀ v ∈ dom, v < 2 ^ 32))) :
    v % 2 ^ (8 * k) ∈ D := by
  rcases hD with h | ⟨rfl, h⟩
  · rwa [leValue_valBytes v hk8] at h
  · rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (h hr v hv) (Nat.pow_le_pow_right (by omega)
      (by omega)))]
    exact hv

set_option linter.unusedSimpArgs false in
/-- **One instruction is sound** (core form): every branch of the symbolic x86
step is a run of the item's CIR statements over `D`, with the same actions up to `normActs`, and
the relation is kept. `D` either holds the values of the branch's reads (`leValue` of the bytes
read, below `2 ^ (8 * size)`, with no other bound), or is the x86 domain fitting in 32 bits. -/
theorem chk1_sound_core {t : XThread} {dom D : List Nat}
    {K Z K' Z' : List Reg} {i : Atomic9.Instr} {ops : List Stmt}
    {nx : Word} (hc : chk1 K Z nx i ops = some (K', Z')) {s : State} {n : Nat}
    (hf : t.fetch s = some (i, n)) (hnx : s.rip + BitVec.ofNat 64 n = nx)
    {rs : Regs} (hrel : Rel K Z rs s) {outs : List (List XAct × State)}
    (hs : stepSym t dom s = some outs) {o : List XAct × State} (ho : o ∈ outs)
    (hD : (∀ a ∈ o.1, a.ev.kind.reads = true → leValue a.rd ∈ D) ∨
      (D = dom ∧ (ops.any Stmt.reads = true → ∀ v ∈ dom, v < 2 ^ 32))) :
    ∃ rs', Sim D rs ops (normActs o.1) rs' ∧ Rel K' Z' rs' o.2 ∧
      o.2.rip = s.rip + BitVec.ofNat 64 n := by
  suffices H : ∃ rs', Sim D rs (ops.map Stmt.demode) (normActs o.1) rs' ∧ Rel K' Z' rs' o.2 ∧
      o.2.rip = s.rip + BitVec.ofNat 64 n by
    obtain ⟨rs', h1, h2⟩ := H
    exact ⟨rs', Sim.demode h1, h2⟩
  unfold chk1 at hc
  split at hc
  case h_1 =>
    -- `mov m, r`
    rename_i sz a src k e r heq
    rw [heq]
    split at hc
    · rename_i hcond
      obtain ⟨rfl, ha, rfl, hsrc⟩ := hcond
      cases hc
      rw [stepSym_mem hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
      simp only [memStep, storeStep] at hs
      split at hs
      · cases hs
        simp only [List.mem_singleton] at ho
        subst ho
        refine ⟨rs, Sim.single' (List.mem_singleton_self _) ?_ rfl, Rel.same hrel (fun _ => rfl), rfl⟩
        rw [normActs_single _ (by simp)]
        simp [Lab.acts, stAct, flavOf, addrE_eval ha hrel.eq hnx, leBytes_sw,
          Sz.read, Expr.eval, Sz.bits_eq, natBytes_mod, hrel.eq r hsrc]
      · cases hs
    · cases hc
  case h_2 =>
    -- `mov m, imm`
    rename_i sz a imm k e c heq
    rw [heq]
    split at hc
    · rename_i hcond
      obtain ⟨rfl, ha, rfl⟩ := hcond
      cases hc
      rw [stepSym_mem hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        MemEvent.atomic9NewAccesses, Atomic9.tag, Atomic9.RM.isMem, MemEvent.aluKind,
        Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
      simp only [memStep, storeStep] at hs
      split at hs
      · cases hs
        simp only [List.mem_singleton] at ho
        subst ho
        refine ⟨rs, Sim.single' (List.mem_singleton_self _) ?_ rfl, Rel.same hrel (fun _ => rfl), rfl⟩
        rw [normActs_single _ (by simp)]
        simp [Lab.acts, stAct, flavOf, addrE_eval ha hrel.eq hnx,
          leBytes_eq, Expr.eval, immW, natBytes_mod]
      · cases hs
    · cases hc
  case h_3 =>
    -- `movb m, imm8`
    rename_i a imm k e c heq
    rw [heq]
    split at hc
    · rename_i hcond
      obtain ⟨rfl, ha, rfl⟩ := hcond
      cases hc
      rw [stepSym_mem hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        MemEvent.atomic9NewAccesses, Atomic9.tag, Atomic9.RM.isMem, MemEvent.aluKind,
        Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
      simp only [memStep, store8Step] at hs
      split at hs
      · cases hs
        simp only [List.mem_singleton] at ho
        subst ho
        refine ⟨rs, Sim.single' (List.mem_singleton_self _) ?_ rfl, Rel.same hrel (fun _ => rfl), rfl⟩
        rw [normActs_single _ (by simp)]
        simp only [Lab.acts, stAct, flavOf, addrE_eval ha hrel.eq hnx,
          leBytes_eq, Expr.eval, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.cons.injEq, and_true]
        congr 2
        have := imm.isLt
        simp; omega
      · cases hs
    · cases hc
  case h_4 =>
    -- `mov r, m`
    rename_i sz dst a d k e heq
    rw [heq]
    split at hc
    · rename_i hcond
      obtain ⟨rfl, ha, rfl⟩ := hcond
      cases hc
      rw [stepSym_mem hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
      simp only [memStep] at hs
      split at hs
      · cases hs
        simp only [List.mem_map] at ho
        obtain ⟨v0, hv0, rfl⟩ := ho
        have hv := readVal (sz_bytes_ge sz) (sz_bytes_le sz) hv0
          (by rw [any_reads_demode, heq]; rfl)
          (hD.imp_left fun h => h _ (List.mem_singleton_self _) rfl)
        rw [← valBytes_mod v0 sz.bytes (sz_bytes_le sz)]
        have h32 : v0 % 2 ^ (8 * sz.bytes) < 2 ^ (8 * sz.bytes) := Nat.mod_lt _ (Nat.two_pow_pos _)
        generalize v0 % 2 ^ (8 * sz.bytes) = v at hv h32 ⊢
        refine ⟨_, Sim.single' (List.mem_map_of_mem (pick_mem_k hv h32)) ?_ rfl,
          Rel.setSz hrel sz d h32 ?_, rfl⟩
        · rw [normActs_single _ (by simp)]
          simp [Lab.acts, ldAct, flavOf, addrE_eval ha hrel.eq hnx,
            valBytes_eq (lt64_k sz h32)]
        · intro q
          simp only [Sz.write, ldx sz h32, ofNat_sw sz h32]
          exact State.read_write _ _ _ _
      · cases hs
    · cases hc
  case h_5 =>
    -- `mov r, imm`
    rename_i sz dst imm d c heq
    rw [heq]
    split at hc
    · rename_i hcond
      obtain ⟨rfl, rfl⟩ := hcond
      cases hc
      rw [stepSym_inert hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv])
        (c := { Sz.write sz s d (imm.signExtend sz.bits) with rip := s.rip + BitVec.ofNat 64 n })
        (m := t.frame) rfl] at hs
      cases hs
      simp only [List.mem_singleton] at ho
      subst ho
      have hpost : ∀ q, ({ Sz.write sz s d (imm.signExtend sz.bits) with
          rip := s.rip + BitVec.ofNat 64 n } : State).read q =
          if q = d then BitVec.ofNat 64 (immW sz imm).toNat else s.read q := by
        intro q
        simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, immW]
        exact State.read_write _ _ _ _
      refine ⟨_, Sim.single' (List.mem_singleton_self _) ?_ rfl, ?_, rfl⟩
      · simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
          MemEvent.extAccesses, MemEvent.rmEv, normActs]
      · split
        · rename_i hc32
          exact Rel.set hrel d hc32 hpost
        · exact Rel.setw hrel d _ hpost
    · cases hc
  case h_6 =>
    -- `inc/dec m` (unlocked): a load and a store
    rename_i sz dec a d k e k' e' op d' heq
    rw [heq]
    generalize hop : (if dec then BinOp.sub else BinOp.add) = op0 at hc
    split at hc
    · rename_i hcond
      obtain ⟨hk, hk', ha, he, hd, hde, ho'⟩ := hcond
      subst hk hk' he hd ho' hop
      cases hc
      rw [stepSym_mem hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        MemEvent.atomic9NewAccesses, Atomic9.tag, Atomic9.RM.isMem, MemEvent.aluKind,
        Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
      simp only [memStep, rmwStep] at hs
      split at hs
      · cases hs
        simp only [List.mem_map] at ho
        obtain ⟨v0, hv0, rfl⟩ := ho
        have hv := readVal (sz_bytes_ge sz) (sz_bytes_le sz) hv0
          (by rw [any_reads_demode, heq]; rfl)
          (hD.imp_left fun h => h _ (List.mem_singleton_self _) rfl)
        rw [← valBytes_mod v0 sz.bytes (sz_bytes_le sz)]
        have h32 : v0 % 2 ^ (8 * sz.bytes) < 2 ^ (8 * sz.bytes) := Nat.mod_lt _ (Nat.two_pow_pos _)
        generalize v0 % 2 ^ (8 * sz.bytes) = v at hv h32 ⊢
        have h1 : (1#sz.bits).setWidth 64 = BitVec.ofNat 64 1 := by cases sz <;> rfl
        have key : ((if dec then BinOp.sub else BinOp.add).eval (BitVec.ofNat 64 v)
            (BitVec.ofNat 64 1)).toNat % 2 ^ (8 * sz.bytes) =
            (if dec then BitVec.ofNat sz.bits v - 1#sz.bits
              else BitVec.ofNat sz.bits v + 1#sz.bits).toNat := by
          cases dec
          · have := aluI_val .add .add rfl sz (BitVec.ofNat sz.bits v) 1#sz.bits
            rw [← ofNat_sw sz h32, ← h1, ← Sz.bits_eq, ← BitVec.toNat_setWidth]
            simp only [Bool.false_eq_true, ite_false, ite_true]
            exact congrArg BitVec.toNat this
          · have := aluI_val .sub .sub rfl sz (BitVec.ofNat sz.bits v) 1#sz.bits
            rw [← ofNat_sw sz h32, ← h1, ← Sz.bits_eq, ← BitVec.toNat_setWidth]
            simp only [Bool.false_eq_true, ite_false, ite_true]
            exact congrArg BitVec.toNat this
        have hl : (([.rd .rlx .wb (e'.eval rs).toNat sz.bytes v], rs.set d' (BitVec.ofNat 64 v)) :
            List Lab × Regs) ∈ run D (.load d' .rlx sz.bytes .wb e') rs :=
          List.mem_map_of_mem (f := fun v => ([Lab.rd .rlx .wb (e'.eval rs).toNat sz.bytes v],
            rs.set d' (BitVec.ofNat 64 v))) (pick_mem_k hv h32)
        have hsim := Sim.cons hl (Sim.single (dom := D)
          (x := .store .rlx sz.bytes .wb e' (.bin (if dec then BinOp.sub else BinOp.add) (.reg d') (.lit 1)))
          (List.mem_singleton_self _))
        refine ⟨_, ?_, Rel.clob hrel d' (BitVec.ofNat 64 v) (fun _ => rfl), rfl⟩
        obtain ⟨p, hp, hpa, hpr⟩ := hsim
        refine ⟨p, hp, ?_, hpr⟩
        rw [hpa]
        simp only [ldx sz h32]
        simp [normActs, Act.norm, Lab.acts, ldAct, stAct, flavOf, run,
          addrE_eval ha hrel.eq hnx, Expr.eval_set hde,
          valBytes_eq (lt64_k sz h32), leBytes_sw, Expr.eval, key, Regs.set_self]
      · cases hs
    · cases hc
  case h_7 =>
    -- `xchg m, r`
    rename_i sz a src d k e r heq
    rw [heq]
    split at hc
    · rename_i hcond
      obtain ⟨hk, ha, hr, hd, hsrc⟩ := hcond
      subst hk hr hd
      cases hc
      rw [stepSym_mem hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        MemEvent.atomic9NewAccesses, Atomic9.tag, Atomic9.RM.isMem, MemEvent.aluKind,
        Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
      simp only [memStep, rmwStep] at hs
      split at hs
      · cases hs
        simp only [List.mem_map] at ho
        obtain ⟨v0, hv0, rfl⟩ := ho
        have hv := readVal (sz_bytes_ge sz) (sz_bytes_le sz) hv0
          (by rw [any_reads_demode, heq]; rfl)
          (hD.imp_left fun h => h _ (List.mem_singleton_self _) rfl)
        rw [← valBytes_mod v0 sz.bytes (sz_bytes_le sz)]
        have h32 : v0 % 2 ^ (8 * sz.bytes) < 2 ^ (8 * sz.bytes) := Nat.mod_lt _ (Nat.two_pow_pos _)
        generalize v0 % 2 ^ (8 * sz.bytes) = v at hv h32 ⊢
        refine ⟨_, Sim.single' (List.mem_map_of_mem (pick_mem_k hv h32)) ?_ rfl,
          Rel.mono (Rel.setSz hrel sz _ h32 ?_) (fun q hq => (mem_drop.mp hq).1) (fun q hq => hq), rfl⟩
        · rw [normActs_single _ (by simp)]
          simp only [ldx sz h32]
          simp [Lab.acts, rmwAct, addrE_eval ha hrel.eq hnx,
            valBytes_eq (lt64_k sz h32), leBytes_sw, Expr.eval, RmwOp.result,
            hrel.eq _ hsrc]
          rw [natBytes_mod, Sz.read, natBytes_sw, hrel.eq _ hsrc]
        · intro q
          simp only [ldx sz h32, Sz.write, ofNat_sw sz h32]
          exact State.read_write _ _ _ _
      · cases hs
    · cases hc
  case h_8 =>
    -- `lock xadd m, r`
    rename_i sz a src d k e r heq
    rw [heq]
    split at hc
    · rename_i hcond
      obtain ⟨hk, ha, hr, hd, hsrc⟩ := hcond
      subst hk hr hd
      cases hc
      rw [stepSym_mem hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        MemEvent.atomic9NewAccesses, Atomic9.tag, Atomic9.RM.isMem, MemEvent.aluKind,
        Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
      simp only [memStep, rmwStep] at hs
      split at hs
      · cases hs
        simp only [List.mem_map] at ho
        obtain ⟨v0, hv0, rfl⟩ := ho
        have hv := readVal (sz_bytes_ge sz) (sz_bytes_le sz) hv0
          (by rw [any_reads_demode, heq]; rfl)
          (hD.imp_left fun h => h _ (List.mem_singleton_self _) rfl)
        rw [← valBytes_mod v0 sz.bytes (sz_bytes_le sz)]
        have h32 : v0 % 2 ^ (8 * sz.bytes) < 2 ^ (8 * sz.bytes) := Nat.mod_lt _ (Nat.two_pow_pos _)
        generalize v0 % 2 ^ (8 * sz.bytes) = v at hv h32 ⊢
        refine ⟨_, Sim.single' (List.mem_map_of_mem (pick_mem_k hv h32)) ?_ rfl,
          Rel.mono (Rel.setSz hrel sz _ h32 ?_) (fun q hq => (mem_drop.mp hq).1) (fun q hq => hq), rfl⟩
        · rw [normActs_single _ (by simp)]
          simp only [ldx sz h32]
          simp [Lab.acts, rmwAct, addrE_eval ha hrel.eq hnx,
            valBytes_eq (lt64_k sz h32), leBytes_sw, Expr.eval, RmwOp.result,
            hrel.eq _ hsrc]
          simp only [Sz.read, BitVec.toNat_setWidth, hrel.eq _ hsrc, Sz.bits_eq, Nat.add_mod_mod]
        · intro q
          simp only [ldx sz h32, Sz.write, ofNat_sw sz h32]
          exact State.read_write _ _ _ _
      · cases hs
    · cases hc
  case h_9 =>
    -- `lock cmpxchg m, r`
    rename_i sz a src d k q e r heq
    rw [heq]
    split at hc
    · rename_i hcond
      obtain ⟨hk, ha, hr, hd, hq, hsrc, hraxK, hfit⟩ := hcond
      subst hk hr hd hq
      cases hc
      rw [stepSym_mem hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        MemEvent.atomic9NewAccesses, Atomic9.tag, Atomic9.RM.isMem, MemEvent.aluKind,
        Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
      simp only [memStep, rmwStep] at hs
      split at hs
      · cases hs
        simp only [List.mem_map] at ho
        obtain ⟨v0, hv0, rfl⟩ := ho
        have hv := readVal (sz_bytes_ge sz) (sz_bytes_le sz) hv0
          (by rw [any_reads_demode, heq]; rfl)
          (hD.imp_left fun h => h _ (List.mem_singleton_self _) rfl)
        rw [← valBytes_mod v0 sz.bytes (sz_bytes_le sz)]
        have h32 : v0 % 2 ^ (8 * sz.bytes) < 2 ^ (8 * sz.bytes) := Nat.mod_lt _ (Nat.two_pow_pos _)
        generalize v0 % 2 ^ (8 * sz.bytes) = v at hv h32 ⊢
        have hrax := hrel.eq .rax hraxK
        have hiff : (Sz.read sz s .rax = BitVec.ofNat sz.bits v) ↔
            v = (rs .rax).toNat % 2 ^ (8 * sz.bytes) := by
          rw [← BitVec.toNat_inj, ofNat_toNat_lt sz h32, Sz.read, BitVec.toNat_setWidth, hrax,
            Sz.bits_eq]
          exact eq_comm
        simp only [ldx sz h32]
        by_cases hacc : Sz.read sz s .rax = BitVec.ofNat sz.bits v
        · have hsr : s.read .rax = BitVec.ofNat 64 v := by
            apply BitVec.eq_of_toNat_eq
            have h1 := congrArg BitVec.toNat hacc
            rw [Sz.read, BitVec.toNat_setWidth, ofNat_toNat_lt sz h32] at h1
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt64_k sz h32), ← h1]
            rcases hfit with rfl | hz
            · exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
            · have := hrel.fit _ hz
              rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le this
                (Nat.pow_le_pow_right (by omega) (by cases sz <;> decide)))]
          simp only [hacc, ite_true]
          refine ⟨_, Sim.single' (List.mem_map_of_mem (pick_mem_k hv h32)) ?_ rfl,
            Rel.mono (Rel.setSz hrel sz .rax h32 ?_) (fun q hq => (mem_drop.mp hq).1)
              (setSz_sub_rax sz Z), by trivial⟩
          · rw [normActs_single _ (by simp)]
            simp [Lab.acts, rmwAct, addrE_eval ha hrel.eq hnx,
              valBytes_eq (lt64_k sz h32), leBytes_sw, Expr.eval, RmwOp.result,
              hrel.eq _ hsrc, (hiff.mp hacc).symm]
            rw [natBytes_mod, Sz.read, natBytes_sw, hrel.eq _ hsrc]
          · intro q
            show s.read q = _
            split
            · subst_vars; exact hsr
            · rfl
        · simp only [hacc, ite_false]
          refine ⟨_, Sim.single' (List.mem_map_of_mem (pick_mem_k hv h32)) ?_ rfl,
            Rel.mono (Rel.setSz hrel sz .rax h32 ?_) (fun q hq => (mem_drop.mp hq).1)
              (setSz_sub_rax sz Z), by trivial⟩
          · rw [normActs_single _ (by simp)]
            have hne : ¬ v = (rs .rax).toNat % 2 ^ (8 * sz.bytes) := fun h => hacc (hiff.mpr h)
            simp [Lab.acts, rmwAct, addrE_eval ha hrel.eq hnx,
              valBytes_eq (lt64_k sz h32), leBytes_sw, Expr.eval, RmwOp.result,
              hne, ofNat_toNat_lt sz h32]
          · intro q
            simp only [Sz.write, ofNat_sw sz h32]
            exact State.read_write _ _ _ _
      · cases hs
    · cases hc
  case h_10 =>
    -- `lock add/sub/and/or/xor m, imm`
    rename_i sz op a imm d k o' e c heq
    rw [heq]
    split at hc
    · rename_i hcond
      obtain ⟨hk, ha, hb, hc'⟩ := hcond
      subst hk hc'
      cases hc
      have hop : op ≠ .cmp := by rintro rfl; simp [binOf] at hb
      rw [stepSym_mem hf (by simp [hop, MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        MemEvent.atomic9NewAccesses, Atomic9.tag, Atomic9.RM.isMem, MemEvent.aluKind,
        Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
      simp only [memStep] at hs
      split at hs
      · cases hs
      simp only [rmwStep] at hs
      split at hs
      · cases hs
        simp only [List.mem_map] at ho
        obtain ⟨v0, hv0, rfl⟩ := ho
        have hv := readVal (sz_bytes_ge sz) (sz_bytes_le sz) hv0
          (by rw [any_reads_demode, heq]; rfl)
          (hD.imp_left fun h => h _ (List.mem_singleton_self _) rfl)
        rw [← valBytes_mod v0 sz.bytes (sz_bytes_le sz)]
        have h32 : v0 % 2 ^ (8 * sz.bytes) < 2 ^ (8 * sz.bytes) := Nat.mod_lt _ (Nat.two_pow_pos _)
        generalize v0 % 2 ^ (8 * sz.bytes) = v at hv h32 ⊢
        have key : (o'.eval (BitVec.ofNat 64 v) (immW sz imm)).toNat %
            2 ^ (8 * sz.bytes) = (Silmaril.X86.Ext.AluOp.resultN op (BitVec.ofNat sz.bits v)
              (imm.signExtend sz.bits)).toNat := by
          rw [← aluI_val op o' hb sz, BitVec.toNat_setWidth, ← Sz.bits_eq, ← ofNat_sw sz h32, immW]
        refine ⟨_, Sim.single' (List.mem_map_of_mem (pick_mem_k hv h32)) ?_ rfl,
          Rel.clob hrel d _ (fun _ => rfl), rfl⟩
        rw [normActs_single _ (by simp)]
        simp only [ldx sz h32]
        simp [Lab.acts, rmwAct, addrE_eval ha hrel.eq hnx,
          valBytes_eq (lt64_k sz h32), leBytes_sw, Expr.eval, RmwOp.result, key]
      · cases hs
    · cases hc
  case h_11 =>
    -- `lock inc/dec m`
    rename_i sz dec a d k o' e heq
    rw [heq]
    generalize hop : (if dec then BinOp.sub else BinOp.add) = op0 at hc
    split at hc
    · rename_i hcond
      obtain ⟨hk, ha, ho'⟩ := hcond
      subst hk ho' hop
      cases hc
      rw [stepSym_mem hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        MemEvent.atomic9NewAccesses, Atomic9.tag, Atomic9.RM.isMem, MemEvent.aluKind,
        Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
      simp only [memStep, rmwStep] at hs
      split at hs
      · cases hs
        simp only [List.mem_map] at ho
        obtain ⟨v0, hv0, rfl⟩ := ho
        have hv := readVal (sz_bytes_ge sz) (sz_bytes_le sz) hv0
          (by rw [any_reads_demode, heq]; rfl)
          (hD.imp_left fun h => h _ (List.mem_singleton_self _) rfl)
        rw [← valBytes_mod v0 sz.bytes (sz_bytes_le sz)]
        have h32 : v0 % 2 ^ (8 * sz.bytes) < 2 ^ (8 * sz.bytes) := Nat.mod_lt _ (Nat.two_pow_pos _)
        generalize v0 % 2 ^ (8 * sz.bytes) = v at hv h32 ⊢
        have h1 : (1#sz.bits).setWidth 64 = BitVec.ofNat 64 1 := by cases sz <;> rfl
        have key : ((if dec then BinOp.sub else BinOp.add).eval (BitVec.ofNat 64 v)
            (BitVec.ofNat 64 1)).toNat % 2 ^ (8 * sz.bytes) =
            (if dec then BitVec.ofNat sz.bits v - 1#sz.bits
              else BitVec.ofNat sz.bits v + 1#sz.bits).toNat := by
          cases dec
          · have := aluI_val .add .add rfl sz (BitVec.ofNat sz.bits v) 1#sz.bits
            rw [← ofNat_sw sz h32, ← h1, ← Sz.bits_eq, ← BitVec.toNat_setWidth]
            simp only [Bool.false_eq_true, ite_false, ite_true]
            exact congrArg BitVec.toNat this
          · have := aluI_val .sub .sub rfl sz (BitVec.ofNat sz.bits v) 1#sz.bits
            rw [← ofNat_sw sz h32, ← h1, ← Sz.bits_eq, ← BitVec.toNat_setWidth]
            simp only [Bool.false_eq_true, ite_false, ite_true]
            exact congrArg BitVec.toNat this
        refine ⟨_, Sim.single' (List.mem_map_of_mem (pick_mem_k hv h32)) ?_ rfl,
          Rel.clob hrel d _ (fun _ => rfl), rfl⟩
        rw [normActs_single _ (by simp)]
        simp only [ldx sz h32]
        simp only [Lab.acts, rmwAct, addrE_eval ha hrel.eq hnx,
          valBytes_eq (lt64_k sz h32), leBytes_sw, Expr.eval, RmwOp.result, key,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
      · cases hs
    · cases hc
  case h_14 =>
    -- fences
    rename_i f f' heq
    rw [heq]
    split at hc
    · rename_i hcond
      subst hcond
      cases hc
      rw [stepSym_inert hf (by simp [MemEvent.atomic9Accesses, MemEvent.atomic9NewAccesses,
        Atomic9.tag, Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])
        (c := { s with rip := s.rip + BitVec.ofNat 64 n }) (m := t.frame) rfl] at hs
      cases hs
      simp only [List.mem_singleton] at ho
      subst ho
      refine ⟨rs, Sim.single' (List.mem_singleton_self _) ?_ rfl, Rel.same hrel (fun _ => rfl), rfl⟩
      simp [MemEvent.atomic9Accesses, MemEvent.atomic9NewAccesses, Atomic9.tag, normActs,
        Act.norm, Lab.acts, fenceAct, Litmus.Act.inert]
    · cases hc
  case h_12 =>
    -- `mov r32, imm32` (`B8+r`)
    rename_i dst imm d c heq
    rw [heq]
    split at hc
    · rename_i hcond
      obtain ⟨rfl, rfl⟩ := hcond
      cases hc
      rw [stepSym_inert hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses])
        (c := { Sz.write .d s d imm with rip := s.rip + BitVec.ofNat 64 n })
        (m := t.frame) rfl] at hs
      cases hs
      simp only [List.mem_singleton] at ho
      subst ho
      refine ⟨_, Sim.single' (List.mem_singleton_self _) ?_ rfl,
        Rel.set hrel d imm.isLt ?_, rfl⟩
      · simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
          MemEvent.extAccesses, normActs]
      · intro q
        have e : BitVec.ofNat 64 imm.toNat = imm.setWidth 64 := by
          apply BitVec.eq_of_toNat_eq; simp
        rw [e]
        exact State.read_write _ _ _ _
    · cases hc
  case h_13 =>
    -- `movabs r64, imm64`
    rename_i dst imm d c heq
    rw [heq]
    split at hc
    · rename_i hcond
      obtain ⟨rfl, rfl⟩ := hcond
      cases hc
      rw [stepSym_inert hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses])
        (c := { s.write d imm with rip := s.rip + BitVec.ofNat 64 n })
        (m := t.frame) rfl] at hs
      cases hs
      simp only [List.mem_singleton] at ho
      subst ho
      have hpost : ∀ q, ({ s.write d imm with rip := s.rip + BitVec.ofNat 64 n } : State).read q =
          if q = d then BitVec.ofNat 64 imm.toNat else s.read q := by
        intro q
        simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
        exact State.read_write _ _ _ _
      refine ⟨_, Sim.single' (List.mem_singleton_self _) ?_ rfl, ?_, rfl⟩
      · simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
          MemEvent.extAccesses, normActs]
      · split
        · rename_i hc32
          exact Rel.set hrel d hc32 hpost
        · exact Rel.setw hrel d _ hpost
    · cases hc
  case h_15 =>
    -- `mov r, r'`
    rename_i sz dst src d e heq
    rw [heq]
    split at hc
    · rename_i hcond
      obtain ⟨rfl, hsrc, rfl⟩ := hcond
      cases hc
      rw [stepSym_inert hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv])
        (c := { Sz.write sz s d (sz.read s src) with rip := s.rip + BitVec.ofNat 64 n })
        (m := t.frame) rfl] at hs
      cases hs
      simp only [List.mem_singleton] at ho
      subst ho
      have hv : (szE sz (.reg src)).eval rs = (sz.read s src).setWidth 64 := by
        rw [szE_eval]; simp [Expr.eval, Sz.read, hrel.eq src hsrc]
      have hpost : ∀ q, ({ Sz.write sz s d (sz.read s src) with
          rip := s.rip + BitVec.ofNat 64 n } : State).read q =
          if q = d then (szE sz (.reg src)).eval rs else s.read q := by
        intro q
        rw [hv]
        exact State.read_write _ _ _ _
      refine ⟨_, Sim.single' (List.mem_singleton_self _) ?_ rfl, ?_, rfl⟩
      · simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
          MemEvent.extAccesses, MemEvent.rmEv, normActs, run]
      · split
        · rename_i hz
          refine Rel.setW hrel d _ ?_ hpost
          rcases hz with rfl | hz
          · exact szE_fit _ _
          · cases sz
            · exact szE_fit _ _
            · have := hrel.fit src hz
              simpa [szE, Expr.eval, hrel.eq src hsrc] using this
        · exact Rel.setw hrel d _ hpost
    · cases hc
  case h_16 =>
    -- `lea r, m`
    rename_i sz dst a d e heq
    rw [heq]
    split at hc
    · rename_i hcond
      obtain ⟨rfl, hae⟩ := hcond
      obtain ⟨e0, ha, rfl⟩ := Option.map_eq_some_iff.mp hae
      cases hc
      rw [stepSym_inert hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses])
        (c := { Sz.write sz s d ((a.addr s (s.rip + BitVec.ofNat 64 n)).setWidth sz.bits) with
          rip := s.rip + BitVec.ofNat 64 n })
        (m := t.frame) rfl] at hs
      cases hs
      simp only [List.mem_singleton] at ho
      subst ho
      have hv : (szE sz e0).eval rs =
          ((a.addr s (s.rip + BitVec.ofNat 64 n)).setWidth sz.bits).setWidth 64 := by
        rw [szE_eval, addrE_eval ha hrel.eq hnx]
      have hpost : ∀ q, ({ Sz.write sz s d ((a.addr s (s.rip + BitVec.ofNat 64 n)).setWidth sz.bits) with
          rip := s.rip + BitVec.ofNat 64 n } : State).read q =
          if q = d then (szE sz e0).eval rs else s.read q := by
        intro q
        rw [hv]
        exact State.read_write _ _ _ _
      refine ⟨_, Sim.single' (List.mem_singleton_self _) ?_ rfl, ?_, rfl⟩
      · simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
          MemEvent.extAccesses, normActs, run]
      · split
        · rename_i hz
          subst hz
          exact Rel.setW hrel d _ (szE_fit _ _) hpost
        · exact Rel.setw hrel d _ hpost
    · cases hc
  case h_17 => cases hc

/-- **One instruction is sound** over a domain of 32-bit values (the earlier form). -/
theorem chk1_sound {t : XThread} {dom : List Nat}
    {K Z K' Z' : List Reg} {i : Atomic9.Instr} {ops : List Stmt}
    (hdom : ops.any Stmt.reads = true → ∀ v ∈ dom, v < 2 ^ 32)
    {nx : Word} (hc : chk1 K Z nx i ops = some (K', Z')) {s : State} {n : Nat}
    (hf : t.fetch s = some (i, n)) (hnx : s.rip + BitVec.ofNat 64 n = nx)
    {rs : Regs} (hrel : Rel K Z rs s) {outs : List (List XAct × State)}
    (hs : stepSym t dom s = some outs) {o : List XAct × State} (ho : o ∈ outs) :
    ∃ rs', Sim dom rs ops (normActs o.1) rs' ∧ Rel K' Z' rs' o.2 ∧
      o.2.rip = s.rip + BitVec.ofNat 64 n :=
  chk1_sound_core hc hf hnx hrel hs ho (.inr ⟨rfl, hdom⟩)

/-- **One instruction is sound for any read value**: no bound on the x86 domain.
The CIR run is over any domain `D` that holds the value of every read of the branch (`leValue`
of the bytes read, so below `2 ^ 32` for a 4-byte read and below `2 ^ 64` for an 8-byte one). -/
theorem chk1_sound_vals {t : XThread} {dom D : List Nat}
    {K Z K' Z' : List Reg} {i : Atomic9.Instr} {ops : List Stmt}
    {nx : Word} (hc : chk1 K Z nx i ops = some (K', Z')) {s : State} {n : Nat}
    (hf : t.fetch s = some (i, n)) (hnx : s.rip + BitVec.ofNat 64 n = nx)
    {rs : Regs} (hrel : Rel K Z rs s) {outs : List (List XAct × State)}
    (hs : stepSym t dom s = some outs) {o : List XAct × State} (ho : o ∈ outs)
    (hD : ∀ a ∈ o.1, a.ev.kind.reads = true → leValue a.rd ∈ D) :
    ∃ rs', Sim D rs ops (normActs o.1) rs' ∧ Rel K' Z' rs' o.2 ∧
      o.2.rip = s.rip + BitVec.ofNat 64 n :=
  chk1_sound_core hc hf hnx hrel hs ho (.inl hD)

/-! ## The walk -/

theorem mapM_mem {α β : Type} {f : α → Option (List β)} :
    ∀ {l : List α} {rss : List (List β)}, l.mapM f = some rss → ∀ {y : β}, y ∈ rss.flatten →
      ∃ x ∈ l, ∃ ys, f x = some ys ∧ y ∈ ys
  | [], rss, h, y, hy => by
    simp at h; subst h; simp at hy
  | x :: l, rss, h, y, hy => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ys, hx, rs, hl, rfl⟩ := h
    simp only [List.flatten_cons, List.mem_append] at hy
    rcases hy with hy | hy
    · exact ⟨x, by simp, ys, hx, hy⟩
    · obtain ⟨x', hx', ys', h', hy'⟩ := mapM_mem hl hy
      exact ⟨x', by simp [hx'], ys', h', hy'⟩

theorem fetchAt_le {t : XThread} {o : Nat} {i : Atomic9.Instr} {n : Nat}
    (h : fetchAt t o = some (i, n)) : o + n ≤ t.code.length := by
  unfold fetchAt at h
  split at h
  · split at h
    · cases h; rename_i hc; exact hc.1
    · cases h
  · cases h

theorem base_ne {b : Word} {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (hne : x ≠ y) :
    b + BitVec.ofNat 64 x ≠ b + BitVec.ofNat 64 y := by
  intro h
  have h' : BitVec.ofNat 64 x = BitVec.ofNat 64 y := by
    have := congrArg (· - b) h
    simpa using this
  have := congrArg BitVec.toNat h'
  simp at this
  omega

theorem base_add {b : Word} (x n : Nat) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 n = b + BitVec.ofNat 64 (x + n) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp

/-- **The walk is sound**, following `explore` step by step. -/
theorem walk_sound {t : XThread} {dom : List Nat} (hlen : t.code.length < 2 ^ 64) :
    ∀ (its : List Item), (its.any (fun it => it.ops.any Stmt.reads) = true → ∀ v ∈ dom, v < 2 ^ 32) →
    ∀ (K Z : List Reg) (o : Nat) (Kf : List Reg), walk t K Z o its = some Kf →
      ∀ (fuel : Nat) (s : State) (rs : Regs), s.rip = t.base + BitVec.ofNat 64 o →
        o ≤ t.code.length → Rel K Z rs s → ∀ trs, explore t dom fuel s = some trs →
          ∀ tr ∈ trs, ∃ rs', Sim dom rs (its.flatMap Item.ops) (normActs tr.acts) rs' ∧
            ∀ r, r ∉ Kf → tr.final.read r = rs' r := by
  intro its
  induction its with
  | nil =>
    intro _ K Z o Kf hw fuel s rs hrip _ hrel trs hx tr htr
    simp only [walk] at hw
    split at hw
    · rename_i ho
      cases hw
      subst ho
      have he : s.rip = t.endRip := hrip
      have hx' : explore t dom fuel s = some [⟨[], s⟩] := by
        cases fuel <;> simp [explore, he]
      rw [hx'] at hx
      cases hx
      simp only [List.mem_singleton] at htr
      subst htr
      exact ⟨rs, by simpa [normActs, Trace.acts] using Sim.nil, hrel.eq⟩
    · cases hw
  | cons it its ih =>
    intro hdom K Z o Kf hw fuel s rs hrip hle hrel trs hx tr htr
    simp only [walk] at hw
    split at hw
    · rename_i i n hfa
      split at hw
      · rename_i hn
        split at hw
        · rename_i K' Z' hc
          have hon := fetchAt_le hfa
          have hf := fetch_of_fetchAt hfa hrip (by omega)
          have hne : s.rip ≠ t.endRip := by
            rw [hrip]
            exact base_ne (by omega) hlen (by omega)
          cases fuel with
          | zero => simp [explore, hne] at hx
          | succ f =>
            simp only [explore, hne, ite_false] at hx
            split at hx
            · cases hx
            · rename_i outs hs
              obtain ⟨rss, hm, rfl⟩ := Option.map_eq_some_iff.mp hx
              obtain ⟨o', ho', ys, hys, hy⟩ := mapM_mem hm htr
              obtain ⟨trs', he, rfl⟩ := Option.map_eq_some_iff.mp hys
              simp only [Silmaril.X86.Litmus.consStep, List.mem_map] at hy
              obtain ⟨tr', htr', rfl⟩ := hy
              obtain ⟨rs1, hsim1, hrel1, hrip1⟩ := chk1_sound (fun h => hdom (by simp [h])) hc hf
                (by rw [hrip, base_add]) hrel hs ho'
              have hrip1' : o'.2.rip = t.base + BitVec.ofNat 64 (o + n) := by
                rw [hrip1, hrip, base_add]
              obtain ⟨rs', hsim2, hfin⟩ :=
                ih (fun h => hdom (by simp [h])) K' Z' (o + n) Kf hw f o'.2 rs1 hrip1' hon hrel1
                  trs' he tr' htr'
              refine ⟨rs', ?_, hfin⟩
              have := Sim.append hsim1 hsim2
              simpa [normActs, Trace.acts] using this
        · cases hw
      · cases hw
    · cases hw

/-! ## The prologue and the whole thread -/

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by cases r <;> simp [allRegs]

theorem Sim.pro {dom : List Nat} :
    ∀ (pro : List (Reg × Nat)) (rs : Regs),
      Sim dom rs (pro.map fun p => .assign p.1 (.lit p.2)) []
        (pro.foldl (fun rs p => rs.set p.1 (BitVec.ofNat 64 p.2)) rs)
  | [], rs => Sim.nil
  | p :: l, rs => by
    have := Sim.cons (dom := dom) (rs := rs) (x := .assign p.1 (.lit p.2))
      (p := ([], rs.set p.1 (BitVec.ofNat 64 p.2))) (by simp [run, Expr.eval])
      (Sim.pro l (rs.set p.1 (BitVec.ofNat 64 p.2)))
    simpa only [List.map_cons, List.foldl_cons, List.flatMap_nil, List.nil_append] using this

/-- **Translation validation is sound**: for every domain of 32-bit values, every trace
extracted from the bytes is a run of the certificate's CIR thread over the same domain, with
the same actions up to `normActs` and the same final registers outside the clobber set. -/
theorem tvRun_sound {t : XThread} {c : Cert} {K : List Reg} (h : tvRun t c = some K)
    {dom : List Nat} (hdom : c.reads = true → ∀ v ∈ dom, v < 2 ^ 32) {fuel : Nat}
    {trs : List Trace} (hx : extract t dom fuel = some trs) :
    ∀ tr ∈ trs, ∃ p ∈ run dom c.body Regs.zero, normActs tr.acts = p.1.flatMap Lab.acts ∧
      ∀ r, r ∉ K → tr.final.read r = p.2 r := by
  intro tr htr
  unfold tvRun at h
  split at h
  · rename_i hok
    obtain ⟨hpro, hlen⟩ := hok
    simp only [proOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hpro
    obtain ⟨hrip, hregs⟩ := hpro
    have hrel : Rel [] (allRegs.filter fun r => decide ((c.proRegs r).toNat < 2 ^ 32))
        c.proRegs t.init := by
      constructor
      · intro r _
        simpa using hregs r (mem_allRegs r)
      · intro r hr
        simp only [List.mem_filter, decide_eq_true_eq] at hr
        have := hregs r (mem_allRegs r)
        rw [this]; exact hr.2
    have hrip0 : t.init.rip = t.base + BitVec.ofNat 64 0 := by simp [hrip]
    obtain ⟨rs', hsim, hfin⟩ := walk_sound hlen c.items hdom [] _ 0 K h fuel t.init c.proRegs
      hrip0 (Nat.zero_le _) hrel trs hx tr htr
    have := Sim.append (Sim.pro (dom := dom) c.pro Regs.zero) hsim
    obtain ⟨p, hp, hpa, hpr⟩ := this
    exact ⟨p, hp, by simpa using hpa.symm, fun r hr => (hfin r hr).trans (by rw [hpr])⟩
  · cases h

/-! ## Access units are blind to `normActs` -/

open Silmaril.X86.MemoryModel.Litmus (threadUnits actUnits accUnits units AxReach Test Final Cond Atom
  finalAx finalOf)

theorem threadUnits_append (i : Nat) :
    ∀ (p : Nat) (l₁ l₂ : List XAct), threadUnits i p (l₁ ++ l₂) =
      threadUnits i p l₁ ++ threadUnits i (p + (threadUnits i p l₁).length) l₂
  | p, [], l₂ => by simp [threadUnits]
  | p, a :: l, l₂ => by
    simp only [List.cons_append, threadUnits, threadUnits_append i _ l l₂, List.append_assoc,
      List.length_append, Nat.add_assoc]

theorem threadUnits_norm (i p : Nat) (a : XAct) :
    threadUnits i p (Act.norm a) = actUnits i p a := by
  unfold Act.norm
  split
  · rename_i h
    obtain ⟨hk, hl⟩ := h
    simp [threadUnits, actUnits, hk, hl]
  · simp [threadUnits]

/-- **Units do not see `normActs`**: an unlocked read-modify-write and its load-then-store have
the same access units. -/
theorem threadUnits_normActs (i : Nat) :
    ∀ (p : Nat) (as : List XAct), threadUnits i p (normActs as) = threadUnits i p as
  | p, [] => rfl
  | p, a :: as => by
    have e : normActs (a :: as) = Act.norm a ++ normActs as := rfl
    rw [e, threadUnits_append, threadUnits_norm, threadUnits_normActs i _ as]
    rfl

/-! ## Choosing CIR traces -/

theorem mapM_id_spec {α : Type} :
    ∀ {l : List (Option α)} {L : List α}, l.mapM id = some L →
      L.length = l.length ∧ ∀ k (h₁ : k < l.length) (h₂ : k < L.length), l[k] = some L[k]
  | [], L, h => by simp at h; subst h; simp
  | x :: l, L, h => by
    rw [List.mapM_cons] at h
    simp only [id, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, L', hl, rfl⟩ := h
    obtain ⟨hlen, hget⟩ := mapM_id_spec hl
    refine ⟨by simp [hlen], ?_⟩
    intro k h₁ h₂
    cases k with
    | zero => simpa using ha
    | succ k => simpa using hget k (by simpa using h₁) (by simpa using h₂)

theorem forall2_pick {α β : Type} {R : Nat → α → β → Prop} :
    ∀ (T : List (List α)) (U : List (List β)) (trs : List α) (i : Nat),
      List.Forall₂ (· ∈ ·) trs T → T.length = U.length →
      (∀ k (h₁ : k < T.length) (h₂ : k < U.length), ∀ a ∈ T[k], ∃ b ∈ U[k], R (i + k) a b) →
      ∃ trs', List.Forall₂ (· ∈ ·) trs' U ∧ trs'.length = trs.length ∧
        ∀ k (h₁ : k < trs.length) (h₂ : k < trs'.length), R (i + k) trs[k] trs'[k]
  | [], U, trs, i, hF, hl, _ => by
    cases hF
    cases U with
    | nil => exact ⟨[], .nil, rfl, fun k h => absurd h (by simp)⟩
    | cons _ _ => simp at hl
  | t :: T, U, trs, i, hF, hl, hR => by
    cases hF with
    | cons ha hF' =>
      rename_i a trs₀
      cases U with
      | nil => simp at hl
      | cons u U =>
        obtain ⟨b, hb, hab⟩ := hR 0 (by simp) (by simp) a ha
        obtain ⟨trs', hF'', hlen, hR'⟩ := forall2_pick T U trs₀ (i + 1) hF' (by simpa using hl)
          (fun k h₁ h₂ a ha => by
            have := hR (k + 1) (by simpa using h₁) (by simpa using h₂) a ha
            simpa [Nat.add_assoc, Nat.add_comm 1 k] using this)
        refine ⟨b :: trs', .cons hb hF'', by simp [hlen], ?_⟩
        intro k h₁ h₂
        cases k with
        | zero => simpa using hab
        | succ k =>
          have := hR' k (by simpa using h₁) (by simpa using h₂)
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

theorem units_congr {trs trs' : List Silmaril.X86.MemoryModel.Litmus.XTrace}
    (hl : trs.length = trs'.length)
    (h : ∀ k (h₁ : k < trs.length) (h₂ : k < trs'.length),
      threadUnits k 0 trs[k].acts = threadUnits k 0 trs'[k].acts) : units trs = units trs' := by
  have : accUnits trs = accUnits trs' := by
    unfold accUnits
    congr 1
    apply List.ext_getElem (by simp [hl])
    intro k h₁ h₂
    simp only [List.getElem_mapIdx]
    exact h k (by simpa using h₁) (by simpa using h₂)
  simp only [units, this]

/-! ## Conditions -/

theorem cond_eval_congr {f f' : Final} :
    ∀ (p : Cond), (∀ a ∈ p.atoms, a.eval f = a.eval f') → p.eval f = p.eval f'
  | .tt, _ => rfl
  | .atom a, h => by simpa [Cond.eval] using h a (by simp [Cond.atoms])
  | .not p, h => by simp [Cond.eval, cond_eval_congr p (by simpa [Cond.atoms] using h)]
  | .and p q, h => by
    simp only [Cond.atoms, List.mem_append] at h
    simp [Cond.eval, cond_eval_congr p (fun a ha => h a (.inl ha)),
      cond_eval_congr q (fun a ha => h a (.inr ha))]
  | .or p q, h => by
    simp only [Cond.atoms, List.mem_append] at h
    simp [Cond.eval, cond_eval_congr p (fun a ha => h a (.inl ha)),
      cond_eval_congr q (fun a ha => h a (.inr ha))]

theorem witness_atoms (t : Test) : t.witness.atoms = t.cond.atoms := by
  unfold Test.witness; split <;> rfl

/-! ## Whole tests -/

theorem xtrace_acts (th : Silmaril.X86.Concurrency.Cir.Thread) (hs : th.spawned = false) (i : Nat)
    (p : List Lab × Regs) : (th.xtrace i p).acts = p.1.flatMap Lab.acts := by
  simp [Thread.xtrace, Thread.acts, Trace.acts, hs]

/-- **Refinement of a validated test**: every x86 behaviour (`AxReach` over the traces of
the bytes) is a CIR behaviour over the same domain with the same value of the witness. -/
theorem TvTest.refines {c : TvTest} (h : c.tvOk = true) (hd : c.domOk = true)
    {T : List (List Silmaril.X86.MemoryModel.Litmus.XTrace)} (hT : c.test.traces = some T)
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop} {f : Final} (hf : AxReach c.test T M f) :
    ∃ f', BehavIn c.prog c.test.domain M f' ∧ c.test.witness.eval f' = c.test.witness.eval f := by
  simp only [TvTest.tvOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hlen, hK⟩ := h
  split at hK
  swap
  · cases hK
  rename_i Ks hKs
  obtain ⟨hKl, hKg⟩ := mapM_id_spec hKs
  obtain ⟨hTl, hTg⟩ := mapM_id_spec hT
  simp only [List.length_mapIdx] at hKl hTl
  obtain ⟨trs, hF, x, hev, hrmw, hwf, hrd, hM, rfl⟩ := hf
  let U := c.prog.traces c.test.domain
  have hUl : U.length = c.test.threads.length := by
    simp [U, Prog.traces, TvTest.prog, hlen]
  -- per thread, a CIR trace with the same units and registers outside the clobbers
  have hpick : ∀ k (h₁ : k < T.length) (h₂ : k < U.length), ∀ a ∈ T[k], ∃ b ∈ U[k],
      threadUnits (0 + k) 0 a.acts = threadUnits (0 + k) 0 b.acts ∧
        ∀ r, r ∉ Ks.getD (0 + k) [] → a.final.read r = b.final.read r := by
    intro k h₁ h₂ a ha
    have hk : k < c.test.threads.length := by omega
    have hx := hTg k (by simpa using hk) (by omega)
    simp only [List.getElem_mapIdx] at hx
    have htv := hKg k (by simpa using hk) (by omega)
    simp only [List.getElem_mapIdx] at htv
    have hkc : k < c.certs.length := by omega
    have hdom : (c.cert k).reads = true → ∀ v ∈ c.test.domain, v < 2 ^ 32 := by
      intro hr
      simp only [TvTest.domOk, Bool.or_eq_true, List.all_eq_true, Bool.not_eq_true',
        decide_eq_true_eq] at hd
      rcases hd with hd | hd
      · have : c.cert k = c.certs[k] := by simp [TvTest.cert, hkc]
        rw [this, hd _ (List.getElem_mem hkc)] at hr
        cases hr
      · exact hd
    obtain ⟨p, hp, hacts, hregs⟩ := tvRun_sound htv hdom hx a ha
    refine ⟨(⟨(c.cert k).body, false⟩ : Silmaril.X86.Concurrency.Cir.Thread).xtrace k p, ?_, ?_, ?_⟩
    · simp only [U, Prog.traces, TvTest.prog, List.getElem_mapIdx, List.getElem_map]
      have : c.cert k = c.certs[k] := by simp [TvTest.cert, hkc]
      rw [← this]
      exact List.mem_map_of_mem hp
    · rw [Nat.zero_add, xtrace_acts _ rfl, ← hacts, threadUnits_normActs]
    · intro r hr
      have : Ks.getD k [] = Ks[k] := by simp [hKl, hk]
      rw [hregs r (by rw [Nat.zero_add] at hr; rwa [← this])]
      rfl
  obtain ⟨trs', hF', hl', hR⟩ := forall2_pick (R := fun k a b =>
    threadUnits k 0 a.acts = threadUnits k 0 b.acts ∧
      ∀ r, r ∉ Ks.getD k [] → a.final.read r = b.final.read r) T U trs 0 hF (by omega) hpick
  have hu : units trs = units trs' := by
    apply units_congr hl'.symm
    intro k h₁ h₂
    have := (hR k h₁ h₂).1
    simpa using this
  refine ⟨finalAx c.test trs' x, ⟨trs', hF', x, hu ▸ hev, hu ▸ hrmw, hwf, hu ▸ hrd, hM, rfl⟩, ?_⟩
  apply cond_eval_congr
  intro a ha
  rw [witness_atoms] at ha
  cases a with
  | mem ad sz v => rfl
  | reg i r bits v =>
    have hav : !(Ks.getD i []).contains r = true := by
      have := List.all_eq_true.mp hK _ ha
      simpa using this
    have hr : r ∉ Ks.getD i [] := by simpa using hav
    simp only [Atom.eval, finalAx, finalOf]
    by_cases hi : i < trs.length
    · have hi' : i < trs'.length := by omega
      rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi']
      simp only [Option.map_some, Option.getD_some]
      rw [(hR i hi hi').2 r (by simpa using hr)]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- A `forbidden` CIR verdict transfers to the bytes. -/
theorem TvTest.forbidden_transfer {c : TvTest} (h : c.tvOk = true) (hd : c.domOk = true)
    {T : List (List Silmaril.X86.MemoryModel.Litmus.XTrace)} (hT : c.test.traces = some T)
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop}
    (hc : Silmaril.X86.MemoryModel.Litmus.Verdict.forbidden.Holds c.test (BehavIn c.prog c.test.domain M)) :
    Silmaril.X86.MemoryModel.Litmus.Verdict.forbidden.Holds c.test (AxReach c.test T M) := by
  rintro ⟨f, hf, hw⟩
  obtain ⟨f', hb, he⟩ := TvTest.refines h hd hT hf
  exact hc ⟨f', hb, he ▸ hw⟩

/-- An `allowed` x86 verdict is an `allowed` CIR verdict. -/
theorem TvTest.allowed_transfer {c : TvTest} (h : c.tvOk = true) (hd : c.domOk = true)
    {T : List (List Silmaril.X86.MemoryModel.Litmus.XTrace)} (hT : c.test.traces = some T)
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop}
    (hc : Silmaril.X86.MemoryModel.Litmus.Verdict.allowed.Holds c.test (AxReach c.test T M)) :
    Silmaril.X86.MemoryModel.Litmus.Verdict.allowed.Holds c.test (BehavIn c.prog c.test.domain M) := by
  obtain ⟨f, hf, hw⟩ := hc
  obtain ⟨f', hb, he⟩ := TvTest.refines h hd hT hf
  exact ⟨f', hb, he ▸ hw⟩

/-- A passing CIR check gives the CIR verdicts. -/
theorem TvTest.cir_of_check {c : TvTest} (h : c.cirCheck = true) :
    (∀ M : Model, (c.verdict M).Holds c.test (BehavIn c.prog c.test.domain M.Holds)) ∧
      ∃ f, BehavIn c.prog c.test.domain Silmaril.X86.MemoryModel.Axiomatic.Exec.Sc f := by
  unfold TvTest.cirCheck at h
  split at h
  · rename_i js hjs
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hsc, htso⟩, hxl⟩, hne⟩ := h
    have hv : ∀ M : Model, c.verdict M = c.test.verdictOf (outsBy js M.sel) := by
      intro M; cases M
      · exact hsc
      · exact htso
      · exact hxl
    refine ⟨fun M => ?_, ?_⟩
    · rw [hv M]
      exact Silmaril.X86.MemoryModel.Litmus.verdictOf_holds fun o =>
        Silmaril.X86.MemoryModel.Litmus.axJudge_spec hjs M o
    · obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ (by simpa using hne)
      obtain ⟨f, hf, _⟩ := (Silmaril.X86.MemoryModel.Litmus.axJudge_spec hjs Model.sc o).mp ho
      exact ⟨f, hf⟩
  · cases h

/-- **Everything a validated test gives.** -/
theorem TvTest.transfer_of_allOk {c : TvTest} (h : c.allOk = true) : c.Transfer := by
  simp only [TvTest.allOk, Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨htv, hd⟩, hc⟩, T, hT⟩ := h
  obtain ⟨hcir, hsc⟩ := TvTest.cir_of_check hc
  refine ⟨⟨T, hT, fun M f hf => TvTest.refines htv hd hT hf⟩, hcir, hsc, ⟨T, hT, ?_⟩,
    ⟨T, hT, fun M hx => TvTest.allowed_transfer htv hd hT hx⟩⟩
  intro M hM
  have := hcir M
  rw [hM] at this
  exact TvTest.forbidden_transfer htv hd hT this

/-! ## Exported pieces (for marked threads) -/

/-- `walk_sound` with `Sim` unfolded. -/
theorem walk_sound_run {t : XThread} {dom : List Nat} (hlen : t.code.length < 2 ^ 64)
    {its : List Item} (hdom : its.any (fun it => it.ops.any Stmt.reads) = true → ∀ v ∈ dom, v < 2 ^ 32)
    {K Z Kf : List Reg} (hw : walk t K Z 0 its = some Kf) {fuel : Nat} {s : State} {rs : Regs}
    (hrip : s.rip = t.base) (hrel : Rel K Z rs s) {trs : List Trace}
    (hx : explore t dom fuel s = some trs) :
    ∀ tr ∈ trs, ∃ p ∈ run dom (chain (its.flatMap Item.ops)) rs,
      p.1.flatMap Lab.acts = normActs tr.acts ∧ ∀ r, r ∉ Kf → tr.final.read r = p.2 r := by
  intro tr htr
  obtain ⟨rs', ⟨p, hp, hpa, hpr⟩, hfin⟩ := walk_sound hlen its hdom K Z 0 Kf hw fuel s rs
    (by simp [hrip]) (Nat.zero_le _) hrel trs hx tr htr
  exact ⟨p, hp, hpa, fun r hr => (hfin r hr).trans (by rw [hpr])⟩

/-- **Refinement of axiomatic behaviours by per-thread choice**: if every trace of thread `k`
in `T` has a trace in `U` with the same access units and the same final registers outside
`Ks[k]`, then every `AxReach` final state over `T` is one over `U` with the same memory and
the same registers outside the `Ks`. -/
theorem axReach_pick {t : Test} {T U : List (List Silmaril.X86.MemoryModel.Litmus.XTrace)}
    {Ks : List (List Reg)} (hl : T.length = U.length)
    (h : ∀ k (h₁ : k < T.length) (h₂ : k < U.length), ∀ a ∈ T[k], ∃ b ∈ U[k],
      threadUnits k 0 a.acts = threadUnits k 0 b.acts ∧
        ∀ r, r ∉ Ks.getD k [] → a.final.read r = b.final.read r)
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop} {f : Final} (hf : AxReach t T M f) :
    ∃ f', AxReach t U M f' ∧ f'.mem = f.mem ∧ ∀ i r, r ∉ Ks.getD i [] → f'.regs i r = f.regs i r := by
  obtain ⟨trs, hF, x, hev, hrmw, hwf, hrd, hM, rfl⟩ := hf
  obtain ⟨trs', hF', hl', hR⟩ := forall2_pick (R := fun k a b =>
    threadUnits k 0 a.acts = threadUnits k 0 b.acts ∧
      ∀ r, r ∉ Ks.getD k [] → a.final.read r = b.final.read r) T U trs 0 hF hl
    (fun k h₁ h₂ a ha => by simpa using h k h₁ h₂ a ha)
  have hu : units trs = units trs' := by
    apply units_congr hl'.symm
    intro k h₁ h₂
    have := (hR k h₁ h₂).1
    simpa using this
  refine ⟨finalAx t trs' x, ⟨trs', hF', x, hu ▸ hev, hu ▸ hrmw, hwf, hu ▸ hrd, hM, rfl⟩, rfl, ?_⟩
  intro i r hr
  simp only [finalAx, finalOf]
  by_cases hi : i < trs.length
  · have hi' : i < trs'.length := by omega
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi']
    simp only [Option.map_some, Option.getD_some]
    rw [(hR i hi hi').2 r (by simpa using hr)]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-! ## Runs of the bytes, not only extracted traces -/

section Runs

open Silmaril.X86.Concurrency.Cir.TvCfg (XStep XRun)

theorem decode_nil' : Atomic9.decode [] = none := by decide

/-- Nothing is fetched at the end of the code. -/
theorem fetch_endRip {t : XThread} {s : State} (hlen : t.code.length < 2 ^ 64)
    (h : s.rip = t.endRip) : t.fetch s = none := by
  have ho : (s.rip - t.base).toNat = t.code.length := by
    have e : t.base + BitVec.ofNat 64 t.code.length - t.base = BitVec.ofNat 64 t.code.length := by
      bv_omega
    rw [h, Silmaril.X86.Litmus.Thread.endRip, e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  simp only [Silmaril.X86.Litmus.Thread.fetch, ho, List.drop_length, List.take_nil,
    decode_nil']

/-- No symbolic step leaves the end of the code. -/
theorem xstep_endRip {t : XThread} (hlen : t.code.length < 2 ^ 64) {s : State}
    {acts : List XAct} {s' : State} (h : XStep t s acts s') (he : s.rip = t.endRip) : False := by
  obtain ⟨dom, outs, hs, -⟩ := h
  simp [stepSym, fetch_endRip hlen he] at hs

/-- **The walk is sound for runs**: every symbolic run (`XRun`, one branch of `stepSym` per
step, for any read values) from a core related to the CIR registers, at the start of the
remaining items, to the end of the code is a run of the items' CIR statements over any domain
`D` that holds the values read (`leValue` of the bytes, no 32-bit bound). -/
theorem walk_xrun {t : XThread} {D : List Nat} (hlen : t.code.length < 2 ^ 64) :
    ∀ (its : List Item) (K Z : List Reg) (o : Nat) (Kf : List Reg), walk t K Z o its = some Kf →
      ∀ (s : State) (rs : Regs) (acc : List (List XAct)) (s' : State),
        s.rip = t.base + BitVec.ofNat 64 o → o ≤ t.code.length → Rel K Z rs s →
        XRun t s acc s' → s'.rip = t.endRip →
        (∀ acts ∈ acc, ∀ a ∈ acts, a.ev.kind.reads = true → leValue a.rd ∈ D) →
        ∃ rs', Sim D rs (its.flatMap Item.ops) (normActs acc.flatten) rs' ∧
          ∀ r, r ∉ Kf → s'.read r = rs' r := by
  intro its
  induction its with
  | nil =>
    intro K Z o Kf hw s rs acc s' hrip _ hrel hx _ _
    simp only [walk] at hw
    split at hw
    · rename_i ho
      cases hw
      subst ho
      have he : s.rip = t.endRip := hrip
      cases hx with
      | nil => exact ⟨rs, by simpa [normActs] using Sim.nil, hrel.eq⟩
      | cons h _ => exact (xstep_endRip hlen h he).elim
    · cases hw
  | cons it its ih =>
    intro K Z o Kf hw s rs acc s' hrip hle hrel hx hend hD
    simp only [walk] at hw
    split at hw
    · rename_i i n hfa
      split at hw
      · rename_i hn
        split at hw
        · rename_i K' Z' hc
          have hon := fetchAt_le hfa
          have hf := fetch_of_fetchAt hfa hrip (by omega)
          have hne : s.rip ≠ t.endRip := by
            rw [hrip]
            exact base_ne (by omega) hlen (by omega)
          cases hx with
          | nil => exact (hne hend).elim
          | @cons _ acts s₁ rest _ h tl =>
            obtain ⟨dom, outs, hs, ho⟩ := h
            obtain ⟨rs1, hsim1, hrel1, hrip1⟩ := chk1_sound_vals (D := D) (o := (acts, s₁)) hc hf
              (by rw [hrip, base_add]) hrel hs ho (hD acts (List.mem_cons_self ..))
            have hrip1' : s₁.rip = t.base + BitVec.ofNat 64 (o + n) := by
              rw [hrip1, hrip, base_add]
            obtain ⟨rs', hsim2, hfin⟩ := ih K' Z' (o + n) Kf hw s₁ rs1 rest s' hrip1' hon hrel1 tl
              hend (fun acts' h' => hD acts' (List.mem_cons_of_mem _ h'))
            refine ⟨rs', ?_, hfin⟩
            have := Sim.append hsim1 hsim2
            simpa [normActs] using this
        · cases hw
      · cases hw
    · cases hw

/-- **The walk reaches only checked instructions**: every core a symbolic run reaches from a
related core at the start of the remaining items, other than the end of the code, sits at an
offset whose instruction `chk1` accepted. -/
theorem walk_reach {t : XThread} (hlen : t.code.length < 2 ^ 64) :
    ∀ (its : List Item) (K Z : List Reg) (o : Nat) (Kf : List Reg), walk t K Z o its = some Kf →
      ∀ (s : State) (rs : Regs) (acc : List (List XAct)) (s' : State),
        s.rip = t.base + BitVec.ofNat 64 o → o ≤ t.code.length → Rel K Z rs s →
        XRun t s acc s' → s'.rip ≠ t.endRip →
        ∃ o' i n K₁ Z₁ ops K₂ Z₂, s'.rip = t.base + BitVec.ofNat 64 o' ∧ o' < t.code.length ∧
          fetchAt t o' = some (i, n) ∧
          chk1 K₁ Z₁ (t.base + BitVec.ofNat 64 (o' + n)) i ops = some (K₂, Z₂) := by
  intro its
  induction its with
  | nil =>
    intro K Z o Kf hw s rs acc s' hrip _ _ hx hne
    simp only [walk] at hw
    split at hw
    · rename_i ho
      subst ho
      have he : s.rip = t.endRip := hrip
      cases hx with
      | nil => exact (hne he).elim
      | cons h _ => exact (xstep_endRip hlen h he).elim
    · cases hw
  | cons it its ih =>
    intro K Z o Kf hw s rs acc s' hrip hle hrel hx hne'
    simp only [walk] at hw
    split at hw
    · rename_i i n hfa
      split at hw
      · rename_i hn
        split at hw
        · rename_i K' Z' hc
          have hon := fetchAt_le hfa
          have hf := fetch_of_fetchAt hfa hrip (by omega)
          cases hx with
          | nil => exact ⟨o, i, n, K, Z, it.ops, K', Z', hrip, by omega, hfa, hc⟩
          | @cons _ acts s₁ rest _ h tl =>
            obtain ⟨dom, outs, hs, ho⟩ := h
            obtain ⟨rs1, -, hrel1, hrip1⟩ := chk1_sound_vals
              (D := ((acts.filter fun a => a.ev.kind.reads).map fun a => leValue a.rd))
              (o := (acts, s₁)) hc hf (by rw [hrip, base_add]) hrel hs ho
              (fun a ha hr => List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, hr⟩, rfl⟩)
            have hrip1' : s₁.rip = t.base + BitVec.ofNat 64 (o + n) := by
              rw [hrip1, hrip, base_add]
            exact ih K' Z' (o + n) Kf hw s₁ rs1 rest s' hrip1' hon hrel1 tl hne'
        · cases hw
      · cases hw
    · cases hw

/-- The prologue's registers stand for the initial core of an accepted thread. -/
theorem rel_init {t : XThread} {c : Cert} (hpro : proOk t c = true) :
    Rel [] (allRegs.filter fun r => decide ((c.proRegs r).toNat < 2 ^ 32)) c.proRegs t.init := by
  simp only [proOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hpro
  obtain ⟨_, hregs⟩ := hpro
  constructor
  · intro r _
    simpa using hregs r (mem_allRegs r)
  · intro r hr
    simp only [List.mem_filter, decide_eq_true_eq] at hr
    have := hregs r (mem_allRegs r)
    rw [this]; exact hr.2

theorem init_rip {t : XThread} {c : Cert} (hpro : proOk t c = true) :
    t.init.rip = t.base + BitVec.ofNat 64 0 := by
  simp only [proOk, Bool.and_eq_true, beq_iff_eq] at hpro
  simp [hpro.1]

/-- **Translation validation is sound for runs**: every symbolic run of the bytes
from the initial core to the end of the code, for **any** values read (no `2 ^ 32` bound), is a
run of the certificate's CIR thread over any domain `D` that holds those values, with the same
actions up to `normActs` and the same final registers outside the clobber set. -/
theorem tvRun_xrun {t : XThread} {c : Cert} {K : List Reg} (h : tvRun t c = some K)
    {acc : List (List XAct)} {s' : State} (hx : XRun t t.init acc s') (he : s'.rip = t.endRip)
    {D : List Nat} (hD : ∀ acts ∈ acc, ∀ a ∈ acts, a.ev.kind.reads = true → leValue a.rd ∈ D) :
    ∃ p ∈ run D c.body Regs.zero, normActs acc.flatten = p.1.flatMap Lab.acts ∧
      ∀ r, r ∉ K → s'.read r = p.2 r := by
  unfold tvRun at h
  split at h
  · rename_i hok
    obtain ⟨hpro, hlen⟩ := hok
    obtain ⟨rs', hsim, hfin⟩ := walk_xrun hlen c.items [] _ 0 K h t.init c.proRegs acc s'
      (init_rip hpro) (Nat.zero_le _) (rel_init hpro) hx he hD
    have := Sim.append (Sim.pro (dom := D) c.pro Regs.zero) hsim
    obtain ⟨p, hp, hpa, hpr⟩ := this
    exact ⟨p, hp, by simpa using hpa.symm, fun r hr => (hfin r hr).trans (by rw [hpr])⟩
  · cases h

theorem mem_actVals {acc : List (List XAct)} {acts : List XAct} (hacts : acts ∈ acc) {a : XAct}
    (ha : a ∈ acts) (hr : a.ev.kind.reads = true) : leValue a.rd ∈ actVals acc :=
  List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_flatten.mpr ⟨acts, hacts, ha⟩, hr⟩, rfl⟩

/-- `tvRun_xrun` over the domain of the values the run read (`actVals`). -/
theorem tvRun_xrun_vals {t : XThread} {c : Cert} {K : List Reg} (h : tvRun t c = some K)
    {acc : List (List XAct)} {s' : State} (hx : XRun t t.init acc s') (he : s'.rip = t.endRip) :
    ∃ p ∈ run (actVals acc) c.body Regs.zero, normActs acc.flatten = p.1.flatMap Lab.acts ∧
      ∀ r, r ∉ K → s'.read r = p.2 r :=
  tvRun_xrun h hx he fun _ hacts _ ha hr => mem_actVals hacts ha hr

/-- **The cores a symbolic run of an accepted thread reaches** sit at checked instructions,
until the end of the code. -/
theorem tvRun_reach {t : XThread} {c : Cert} {K : List Reg} (h : tvRun t c = some K)
    {acc : List (List XAct)} {s' : State} (hx : XRun t t.init acc s') (hne : s'.rip ≠ t.endRip) :
    ∃ o i n K₁ Z₁ ops K₂ Z₂, s'.rip = t.base + BitVec.ofNat 64 o ∧ o < t.code.length ∧
      fetchAt t o = some (i, n) ∧
      chk1 K₁ Z₁ (t.base + BitVec.ofNat 64 (o + n)) i ops = some (K₂, Z₂) := by
  unfold tvRun at h
  split at h
  · rename_i hok
    obtain ⟨hpro, hlen⟩ := hok
    exact walk_reach hlen c.items [] _ 0 K h t.init c.proRegs acc s' (init_rip hpro)
      (Nat.zero_le _) (rel_init hpro) hx hne
  · cases h

/-! ### The 8-byte read and the fitting set -/

/-- **An 8-byte load can leave a value `≥ 2 ^ 32`**: the branch of `mov rax, qword [0x10000]`
reading `2 ^ 32` admits no relation in which `rax` is in the fitting set. Previously
`chk1` put the destination of every load in `Z`, so `chk1_sound` needed the domain below
`2 ^ 32`. -/
theorem q_load_unfit : ∃ outs, stepSym RunEx.qLoad [2 ^ 32] RunEx.qLoad.init = some outs ∧
    ∃ o ∈ outs, ∀ K Z rs, ¬ Rel K (.rax :: Z) rs o.2 := by
  have h : ((stepSym RunEx.qLoad [2 ^ 32] RunEx.qLoad.init).map fun outs =>
      outs.map fun o => (o.2.read .rax).toNat) = some [2 ^ 32] := by decide
  cases hs : stepSym RunEx.qLoad [2 ^ 32] RunEx.qLoad.init with
  | none => rw [hs] at h; simp at h
  | some outs =>
    rw [hs] at h
    simp only [Option.map_some, Option.some.injEq] at h
    match outs, h with
    | [o], h =>
      refine ⟨[o], rfl, o, List.mem_singleton_self _, fun K Z rs hr => ?_⟩
      have h1 := hr.fit .rax (List.mem_cons_self ..)
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
      omega

/-- The `chk1` accepts that load and leaves the fitting set empty. -/
theorem q_load_chk1 : ((RunEx.qLoad.fetch RunEx.qLoad.init).bind fun p =>
    chk1 [] [.rax] (RunEx.qLoad.init.rip + BitVec.ofNat 64 p.2) p.1
      [.load .rax .rlx 8 .wb (.lit 0x10000)]) = some ([], []) := by decide

/-- So the checker refuses a 32-bit `lock cmpxchg` on `rax` after an 8-byte load into it
(the previous checker accepted it, and the run reading `2 ^ 32` then leaves `rax = 2 ^ 32` on
x86 but `0` in CIR) ... -/
theorem qCas_rejected : tvRun RunEx.qCas (RunEx.casCert 8 8) = none := by decide

/-- ... and still accepts it after a 4-byte load. -/
theorem dCas_accepted : tvRun RunEx.dCas (RunEx.casCert 7 4) = some [] := by decide

/-! ### The old checker's certificate is wrong -/

/-- The cmpxchg of `qCas` (at offset 8) passes `chk1` exactly when `rax` is in the fitting set:
the `chk1` leaves `rax` out after the 8-byte load (`q_load_chk1`), the previous checker
put it in, so this item is all that separated the two verdicts on `qCas`. -/
theorem qCas_cas_fit :
    ((fetchAt RunEx.qCas 8).bind fun p => chk1 [] [.rax] (RunEx.qCas.base + BitVec.ofNat 64 (8 + p.2))
      p.1 [.rmw .rax .rlx 4 (.cas (.reg .rax)) (.lit 0x10008) (.reg .rcx)]) = some ([], [.rax]) ∧
    ((fetchAt RunEx.qCas 8).bind fun p => chk1 [] [] (RunEx.qCas.base + BitVec.ofNat 64 (8 + p.2))
      p.1 [.rmw .rax .rlx 4 (.cas (.reg .rax)) (.lit 0x10008) (.reg .rcx)]) = none := by
  decide

/-- Some branch pair of `qCas`, reading `2 ^ 32` then `0`, that ends the code and that no run of
`casCert 8 8` over `[2 ^ 32, 0]` matches on `rax`. -/
def qCasBadB (o1 o2 : List XAct × State) : Bool :=
  decide (o2.2.rip = RunEx.qCas.endRip) &&
    ((o1.1 ++ o2.1).all fun a => !a.ev.kind.reads || decide (leValue a.rd ∈ [2 ^ 32, 0])) &&
    (run [2 ^ 32, 0] (RunEx.casCert 8 8).body Regs.zero).all fun p => decide (p.2 .rax ≠ o2.2.read .rax)

theorem qCas_bad_dec : ((stepSym RunEx.qCas [2 ^ 32] RunEx.qCas.init).getD []).any (fun o1 =>
    ((stepSym RunEx.qCas [0] o1.2).getD []).any fun o2 => qCasBadB o1 o2) = true := by decide

/-- **The certificate the previous checker accepted is unsound**: a symbolic run
of `qCas` to the end of its code, reading `2 ^ 32` then `0`, has no run of `casCert 8 8` over a
domain holding those values with the same final registers. So `tvRun_xrun` is false for any
checker that accepts `(qCas, casCert 8 8)`, and the `chk1` change is needed. -/
theorem qCas_cert_unsound : ∃ acc s', XRun RunEx.qCas RunEx.qCas.init acc s' ∧
    s'.rip = RunEx.qCas.endRip ∧
    (∀ acts ∈ acc, ∀ a ∈ acts, a.ev.kind.reads = true → leValue a.rd ∈ [2 ^ 32, 0]) ∧
    ¬ ∃ p ∈ run [2 ^ 32, 0] (RunEx.casCert 8 8).body Regs.zero,
      normActs acc.flatten = p.1.flatMap Lab.acts ∧ ∀ r, r ∉ ([] : List Reg) → s'.read r = p.2 r := by
  have h := qCas_bad_dec
  cases hs1 : stepSym RunEx.qCas [2 ^ 32] RunEx.qCas.init with
  | none => rw [hs1] at h; simp at h
  | some outs1 =>
    rw [hs1] at h
    simp only [Option.getD_some, List.any_eq_true] at h
    obtain ⟨o1, ho1, h⟩ := h
    cases hs2 : stepSym RunEx.qCas [0] o1.2 with
    | none => rw [hs2] at h; simp at h
    | some outs2 =>
      rw [hs2] at h
      simp only [Option.getD_some] at h
      obtain ⟨o2, ho2, h⟩ := h
      simp only [qCasBadB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
      obtain ⟨⟨hrip, hrd⟩, hrun⟩ := h
      refine ⟨[o1.1, o2.1], o2.2, .cons ⟨_, _, hs1, ho1⟩ (.cons ⟨_, _, hs2, ho2⟩ .nil), hrip,
        ?_, ?_⟩
      · intro acts hacts a ha hr
        have := hrd a (by simp at hacts; rcases hacts with rfl | rfl <;> simp [ha])
        simpa [hr] using this
      · rintro ⟨p, hp, -, hk⟩
        exact hrun p hp (hk .rax (by simp)).symm

end Runs

end Silmaril.Proofs.X86.Concurrency.Cir.Tv
