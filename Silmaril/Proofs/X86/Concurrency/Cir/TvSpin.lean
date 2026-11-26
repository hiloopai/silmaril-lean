module

public import Silmaril.X86.Concurrency.Cir.Tv.Spin.Defs
public import Silmaril.X86.Concurrency.Cir.Tv.Thms

/-!
# Translation validation of spin loops: soundness

The x86 facts are the symbolic steps of the extractor (`stepSym`) on the
four instruction shapes of a spin and on `nop`, computed by unfolding the executor
(`stepSym_load`, `stepSym_test`, `stepSym_cmp`, `stepSym_jcc`, `stepSym_nop`), and the flag
facts that make `jcc` jump exactly when the CIR condition holds (`jump_iff`). `spin_sound`
follows `exploreT` around the loop, one CIR iteration per x86 iteration; `pwalk_sound`
composes the pieces with the exported `walk_sound`; `STest.refines` lifts to tests with
`axReach_pick`.

Generic list and run lemmas are copied from the `TvMarked` proofs (another topic's
proof module, which may not be imported).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.TvSpin

open Silmaril.X86 (State)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (Trace StepRec explore stepSym consStep readOk valBytes ldVal)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Tv
open Silmaril.X86.MemoryModel.Litmus (XAct XTrace Model threadUnits AxReach Final Atom)

/-! ## Runs (copied) -/

theorem mem_run_seq {dom : List Nat} {s t : Stmt} {rs : Regs} {p : List Lab × Regs} :
    p ∈ run dom (.seq s t) rs ↔
      ∃ a ∈ run dom s rs, ∃ b ∈ run dom t a.2, p = (a.1 ++ b.1, b.2) := by
  simp only [run, Res.bind, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩

theorem run_chain_append {dom : List Nat} :
    ∀ (l₁ l₂ : List Stmt) {rs : Regs} {p q : List Lab × Regs},
      p ∈ run dom (chain l₁) rs → q ∈ run dom (chain l₂) p.2 →
        (p.1 ++ q.1, q.2) ∈ run dom (chain (l₁ ++ l₂)) rs
  | [], l₂, rs, p, q, hp, hq => by
    simp only [chain, run, List.mem_singleton] at hp
    subst hp
    simpa using hq
  | x :: l, l₂, rs, p, q, hp, hq => by
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_run_seq.mp hp
    have := run_chain_append l l₂ hb hq
    simp only [List.cons_append, chain]
    exact mem_run_seq.mpr ⟨a, ha, _, this, by simp⟩

theorem run_pro {dom : List Nat} :
    ∀ (pro : List (Reg × Nat)) (rs : Regs),
      ([], pro.foldl (fun rs p => rs.set p.1 (BitVec.ofNat 64 p.2)) rs) ∈
        run dom (chain (pro.map fun p => .assign p.1 (.lit p.2))) rs
  | [], rs => by simp [chain, run]
  | p :: l, rs => by
    simp only [List.map_cons, chain, List.foldl_cons]
    exact mem_run_seq.mpr ⟨([], rs.set p.1 (BitVec.ofNat 64 p.2)), by simp [run, Expr.eval], _,
      run_pro l _, by simp⟩

theorem run_chain_one {dom : List Nat} {x : Stmt} {rs : Regs} {p : List Lab × Regs}
    (h : p ∈ run dom x rs) : p ∈ run dom (chain [x]) rs := by
  simp only [chain]
  exact mem_run_seq.mpr ⟨p, h, ([], p.2), by simp [run], by simp⟩

theorem normActs_append (a b : List XAct) : normActs (a ++ b) = normActs a ++ normActs b := by
  simp [normActs]

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

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by cases r <;> simp [allRegs]

/-- A trace of a `mapM`-explored step list comes from one branch. -/
theorem mem_explored {g : State → Option (List Trace)}
    {outs : List (List Silmaril.X86.Litmus.Act × State)} {trs : List Trace}
    (h : (outs.mapM fun o => (g o.2).map (consStep o.1 o.2)).map List.flatten = some trs)
    {tr : Trace} (htr : tr ∈ trs) :
    ∃ o ∈ outs, ∃ trs', g o.2 = some trs' ∧ ∃ tr' ∈ trs',
      tr = ⟨⟨o.1, o.2⟩ :: tr'.steps, tr'.final⟩ := by
  obtain ⟨rss, hm, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨o, ho, ys, hys, hy⟩ := mapM_mem hm htr
  obtain ⟨trs', hg, rfl⟩ := Option.map_eq_some_iff.mp hys
  obtain ⟨tr', htr', rfl⟩ := List.mem_map.mp hy
  exact ⟨o, ho, trs', hg, tr', htr', rfl⟩

/-! ## Bytes and values (as in the proofs) -/

theorem leBytes_eq (w : BitVec 64) (k : Nat) :
    Silmaril.X86.Ext.leBytes w k = natBytes w.toNat k := by
  apply List.ext_getElem
  · simp [natBytes, Silmaril.X86.Ext.leBytes]
  · intro j h₁ h₂
    simp only [Silmaril.X86.Ext.leBytes, List.getElem_ofFn, natBytes, List.getElem_map,
      List.getElem_range]
    apply BitVec.eq_of_toNat_eq
    simp [Silmaril.Machine.LittleEndian.wordByte, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, pow_mul]

theorem valBytes_eq {v k : Nat} (hv : v < 2 ^ 64) : valBytes v k = natBytes v k := by
  rw [valBytes, leBytes_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

theorem ldVal4 (v : Nat) :
    (ldVal (valBytes v 4)).setWidth 32 = BitVec.ofNat 32 v := by
  simp only [ldVal, valBytes, Silmaril.X86.Ext.leValue_leBytes, BitVec.toNat_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem sw32 {v : Nat} (hv : v < 2 ^ 32) : (BitVec.ofNat 32 v).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-! ## Symbolic steps -/

theorem fetch_at {t : XThread} {s : State} {o : Nat} (h : s.rip = t.base + BitVec.ofNat 64 o)
    (ho : o < 2 ^ 64) : t.fetch s = fetchAt t o := by
  have : (s.rip - t.base).toNat = o := by rw [h]; simp; omega
  simp only [Silmaril.X86.Litmus.Thread.fetch, fetchAt, this]; rfl

theorem stepSym_nop {t : XThread} {dom : List Nat} {s : State} {k : Fin 15} {n : Nat}
    (hf : t.fetch s = some (.open9 (.ext8 (.base (.nop k))), n)) :
    stepSym t dom s = some [([], { s with rip := s.rip + BitVec.ofNat 64 n })] := by
  simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
    MemEvent.extAccesses, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire]

theorem stepSym_test {t : XThread} {dom : List Nat} {s : State} {r : Reg} {n : Nat}
    (hf : t.fetch s = some (.open9 (.ext8 (.base (.test .d (.reg r) r))), n)) :
    stepSym t dom s = some [([], { s with
      flags := Silmaril.X86.Ext.logicFlagsN
        ((Silmaril.X86.Ext.Sz.d.read s r) &&& (Silmaril.X86.Ext.Sz.d.read s r)),
      rip := s.rip + BitVec.ofNat 64 n })] := by
  simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
    MemEvent.extAccesses, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    MemEvent.rmEv, Silmaril.X86.Ext.readRM, Option.map]

theorem stepSym_cmp {t : XThread} {dom : List Nat} {s : State} {r : Reg} {k : BitVec 8} {n : Nat}
    (hf : t.fetch s = some (.open9 (.ext8 (.base (.aluI8 .d .cmp (.reg r) k))), n)) :
    stepSym t dom s = some [([], { s with
      flags := Silmaril.X86.Ext.subFlagsN (Silmaril.X86.Ext.Sz.d.read s r) (k.signExtend 32),
      rip := s.rip + BitVec.ofNat 64 n })] := by
  simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
    MemEvent.extAccesses, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    MemEvent.rmEv, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.AluOp.flagsN]

theorem stepSym_jcc {t : XThread} {dom : List Nat} {s : State} {cc : Silmaril.X86.Ext.Cond}
    {rel : BitVec 8} {n : Nat} {b : Bool}
    (hf : t.fetch s = some (.open9 (.ext8 (.base (.jcc8 cc rel))), n))
    (hb : cc.eval s.flags = some b) :
    stepSym t dom s = some [([], { s with
      rip := if b then s.rip + BitVec.ofNat 64 n + rel.signExtend 64
        else s.rip + BitVec.ofNat 64 n })] := by
  simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
    MemEvent.extAccesses, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext.exec, hb]
  cases b <;> simp

theorem addr_abs {mo : Silmaril.X86.Ext.Mem} (hb : mo.base = .none) (hi : mo.index = none)
    (s : State) (nx : Silmaril.X86.Word) : mo.addr s nx = mo.disp.signExtend 64 := by
  obtain ⟨b, i, d, h⟩ := mo
  simp only at hb hi; subst hb; subst hi
  simp [Silmaril.X86.Ext.Mem.addr]

theorem stepSym_load {t : XThread} {dom : List Nat} {s : State} {r : Reg}
    {mo : Silmaril.X86.Ext.Mem} {n a : Nat}
    (hf : t.fetch s = some (.open9 (.ext8 (.base (.load .d r mo))), n)) (hb : mo.base = .none)
    (hi : mo.index = none) (ha : (mo.disp.signExtend 64).toNat = a)
    (hr : readOk t.regions a 4 = true) :
    stepSym t dom s = some (dom.map fun v =>
      ([⟨⟨.load, a, 4, false⟩, .plain, valBytes v 4, []⟩],
        { Silmaril.X86.Ext.Sz.d.write s r ((ldVal (valBytes v 4)).setWidth 32) with
          rip := s.rip + BitVec.ofNat 64 n })) := by
  simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
    MemEvent.extAccesses, MemEvent.memEv, Silmaril.X86.Litmus.memStep, addr_abs hb hi, ha,
    Silmaril.X86.Litmus.Event.inert, MemEvent.Kind.reads, hr, Silmaril.X86.Ext.Sz.bytes]

/-! ## Addresses -/

theorem endRip_ne {t : XThread} {o : Nat} (ho : o < t.code.length) (hl : t.code.length < 2 ^ 64) :
    t.base + BitVec.ofNat 64 o ≠ t.endRip := by
  intro h
  simp only [Silmaril.X86.Litmus.Thread.endRip] at h
  have := congrArg BitVec.toNat (add_left_cancel h)
  simp at this
  omega

theorem endRip_eq {t : XThread} : t.base + BitVec.ofNat 64 t.code.length = t.endRip := rfl

/-! ## Flags and conditions -/

theorem truthy_ne {rs : Regs} {r : Reg} {v k : Nat} (_hv : v < 2 ^ 32) (hk : k < 2 ^ 32)
    (h : rs r = BitVec.ofNat 64 v) :
    truthy ((Expr.bin .ne (.reg r) (.lit k)).eval rs) = decide (v ≠ k) := by
  simp only [Expr.eval, BinOp.eval, h, truthy]
  by_cases e : v = k
  · subst e; simp
  · have : BitVec.ofNat 64 v ≠ BitVec.ofNat 64 k := by
      intro h'; have := congrArg BitVec.toNat h'; simp at this; omega
    simp [this, e]

theorem truthy_eq {rs : Regs} {r : Reg} {v k : Nat} (_hv : v < 2 ^ 32) (hk : k < 2 ^ 32)
    (h : rs r = BitVec.ofNat 64 v) :
    truthy ((Expr.bin .eq (.reg r) (.lit k)).eval rs) = decide (v = k) := by
  simp only [Expr.eval, BinOp.eval, h, truthy]
  by_cases e : v = k
  · subst e; simp
  · have : BitVec.ofNat 64 v ≠ BitVec.ofNat 64 k := by
      intro h'; have := congrArg BitVec.toNat h'; simp at this; omega
    simp [this, e]

theorem truthy_ltu {rs : Regs} {r : Reg} {v k : Nat} (hv : v < 2 ^ 32) (hk : k < 2 ^ 33)
    (h : rs r = BitVec.ofNat 64 v) :
    truthy ((Expr.bin .ltu (.reg r) (.lit k)).eval rs) = decide (v < k) := by
  simp only [Expr.eval, BinOp.eval, h, truthy, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : v < 2 ^ 64), Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
  by_cases e : v < k <;> simp [e]

theorem isZero32 {v k : Nat} (hv : v < 2 ^ 32) (hk : k < 2 ^ 32) :
    Silmaril.X86.Ext.isZeroN (BitVec.ofNat 32 v - BitVec.ofNat 32 k) = decide (v = k) := by
  simp only [Silmaril.X86.Ext.isZeroN]
  by_cases e : v = k
  · subst e; simp
  · have : BitVec.ofNat 32 v - BitVec.ofNat 32 k ≠ 0#32 := by
      intro h'
      have := congrArg BitVec.toNat (sub_eq_zero.mp h')
      simp at this; omega
    simp [this, e]

theorem ult32 {v k : Nat} (hv : v < 2 ^ 32) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 32 v).ult (BitVec.ofNat 32 k) = decide (v < k) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_decide]
  omega

/-- After `cmp $k, r`, `jcc` jumps exactly when the CIR condition holds. -/
theorem jump_cmp {cc : Silmaril.X86.Ext.Cond} {r : Reg} {k : Nat} {c : Expr}
    (hc : spinCond cc r k = some c) (hk : k < 128) {v : Nat} (hv : v < 2 ^ 32) {rs : Regs}
    (hrs : rs r = BitVec.ofNat 64 v) :
    cc.eval (Silmaril.X86.Ext.subFlagsN (BitVec.ofNat 32 v) (BitVec.ofNat 32 k)) =
      some (truthy (c.eval rs)) := by
  have hz := isZero32 hv (by omega : k < 2 ^ 32)
  have hu := ult32 hv (by omega : k < 2 ^ 32)
  cases cc <;> simp only [spinCond, Option.some.injEq, reduceCtorEq] at hc <;> subst hc <;>
    simp only [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.kNot,
      Silmaril.X86.Ext.kOr, Silmaril.X86.Ext.subBorrowN_eq, hz, hu, Option.map_some]
  · rw [truthy_ltu hv (by omega) hrs]
  · rw [truthy_eq hv (by omega) hrs]
  · rw [truthy_ne hv (by omega) hrs]; simp
  · rw [truthy_ltu hv (by omega) hrs]
    by_cases h1 : v < k
    · simp [h1]; omega
    · by_cases h2 : v = k
      · subst h2; simp
      · simp [h1, h2]; omega

/-- After `test r, r`, `jcc` jumps exactly when the CIR condition (with `k = 0`) holds. -/
theorem jump_test {cc : Silmaril.X86.Ext.Cond} {r : Reg} {c : Expr}
    (hc : spinCond cc r 0 = some c) {v : Nat} (hv : v < 2 ^ 32) {rs : Regs}
    (hrs : rs r = BitVec.ofNat 64 v) :
    cc.eval (Silmaril.X86.Ext.logicFlagsN (BitVec.ofNat 32 v &&& BitVec.ofNat 32 v)) =
      some (truthy (c.eval rs)) := by
  have hz : Silmaril.X86.Ext.isZeroN (BitVec.ofNat 32 v &&& BitVec.ofNat 32 v) = decide (v = 0) := by
    have := isZero32 hv (by omega : 0 < 2 ^ 32)
    simpa using this
  cases cc <;> simp only [spinCond, Option.some.injEq, reduceCtorEq] at hc <;> subst hc <;>
    simp only [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.kNot,
      Silmaril.X86.Ext.kOr, hz, Option.map_some]
  · rw [truthy_ltu hv (by omega) hrs]; simp
  · rw [truthy_eq hv (by omega) hrs]
  · rw [truthy_ne hv (by omega) hrs]; simp
  · rw [truthy_ltu hv (by omega) hrs]
    by_cases h2 : v = 0
    · subst h2; simp
    · simp [h2]

theorem sx8 : ∀ kb : BitVec 8, kb.toNat < 128 → kb.signExtend 32 = BitVec.ofNat 32 kb.toNat := by
  decide

/-! ## Spin pieces -/

/-- What a passing `spinOk` says about the bytes. -/
structure SpinFacts (t : XThread) (r : Reg) (a : Nat) (c : Expr) : Prop where
  load : ∃ mo, fetchAt t 0 = some (.open9 (.ext8 (.base (.load .d r mo))), 7) ∧
    mo.base = .none ∧ mo.index = none ∧ (mo.disp.signExtend 64).toNat = a
  read : readOk t.regions a 4 = true
  small : t.code.length < 2 ^ 32
  rest : ∃ k m cc rel, spinCond cc r k = some c ∧ k < 128 ∧
    ((k = 0 ∧ fetchAt t 7 = some (.open9 (.ext8 (.base (.test .d (.reg r) r))), m)) ∨
      (∃ kb : BitVec 8, kb.toNat = k ∧
        fetchAt t 7 = some (.open9 (.ext8 (.base (.aluI8 .d .cmp (.reg r) kb))), m))) ∧
    fetchAt t (7 + m) = some (.open9 (.ext8 (.base (.jcc8 cc rel))), 2) ∧
    7 + m + 2 = t.code.length ∧
    t.base + BitVec.ofNat 64 (7 + m + 2) + rel.signExtend 64 = t.base

theorem spinOk_facts {t : XThread} {r : Reg} {a : Nat} {c : Expr} (h : spinOk t r a c = true) :
    SpinFacts t r a c := by
  unfold spinOk at h
  split at h
  · rename_i r' mo hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hr, hb⟩, hi⟩, ha⟩, hread⟩, hsmall⟩, hrest⟩ := h
    subst hr
    refine ⟨⟨mo, hl, hb, hi, ha⟩, hread, hsmall, ?_⟩
    split at hrest
    · rename_i k m hcmp
      split at hrest
      · rename_i cc rel hj
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
        obtain ⟨⟨hlen, htg⟩, hc⟩ := hrest
        unfold spinCmp at hcmp
        split at hcmp
        · rename_i r1 r2 m' hf
          split at hcmp
          · rename_i hrr
            obtain ⟨rfl, rfl⟩ := hrr
            simp only [Option.some.injEq, Prod.mk.injEq] at hcmp
            obtain ⟨rfl, rfl⟩ := hcmp
            exact ⟨0, m', cc, rel, hc, by omega, .inl ⟨rfl, hf⟩, hj, hlen, htg⟩
          · cases hcmp
        · rename_i r1 kb m' hf
          split at hcmp
          · rename_i hrr
            obtain ⟨rfl, hk⟩ := hrr
            simp only [Option.some.injEq, Prod.mk.injEq] at hcmp
            obtain ⟨rfl, rfl⟩ := hcmp
            exact ⟨kb.toNat, m', cc, rel, hc, hk, .inr ⟨kb, rfl, hf⟩, hj, hlen, htg⟩
          · cases hcmp
        · cases hcmp
      · simp at hrest
    · simp at hrest
  · cases h

theorem exploreT_zero {t : XThread} {dom : List Nat} {s : State} (h : s.rip ≠ t.endRip) :
    exploreT t dom 0 s = some [] := by
  unfold exploreT; simp [h]

theorem exploreT_succ {t : XThread} {dom : List Nat} {f : Nat} {s : State} (h : s.rip ≠ t.endRip) :
    exploreT t dom (f + 1) s = match stepSym t dom s with
      | none => none
      | some outs => (outs.mapM fun o => (exploreT t dom f o.2).map (consStep o.1 o.2)).map
          List.flatten := by
  conv => lhs; unfold exploreT
  simp only [h, ite_false]
  rfl

theorem exploreT_end {t : XThread} {dom : List Nat} {f : Nat} {s : State} (h : s.rip = t.endRip) :
    exploreT t dom f s = some [⟨[], s⟩] := by
  unfold exploreT; simp [h]

/-- The load action of a spin. -/
def ldA (a v : Nat) : XAct := ⟨⟨.load, a, 4, false⟩, .plain, valBytes v 4, []⟩

theorem read_loaded (s : State) (r : Reg) (v : Nat) (y : Silmaril.X86.Word) :
    Silmaril.X86.Ext.Sz.d.read
      { Silmaril.X86.Ext.Sz.d.write s r ((ldVal (valBytes v 4)).setWidth 32) with rip := y } r =
      BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  simp [Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Sz.write, ldVal, valBytes,
    Silmaril.X86.Ext.leValue_leBytes]

theorem regs_loaded (s : State) (r q : Reg) {v : Nat} (hv : v < 2 ^ 32) :
    (Silmaril.X86.Ext.Sz.d.write s r ((ldVal (valBytes v 4)).setWidth 32)).read q =
      if q = r then BitVec.ofNat 64 v else s.read q := by
  by_cases h : q = r
  · subst h
    simp only [Silmaril.X86.Ext.Sz.write, Silmaril.X86.State.read_write_same, ite_true]
    apply BitVec.eq_of_toNat_eq
    simp [ldVal, valBytes, Silmaril.X86.Ext.leValue_leBytes]
    omega
  · simp [Silmaril.X86.Ext.Sz.write, h]

/-- **One round of a spin**: a load of some `v`, the compare, and the jump, which is taken
exactly when the CIR condition holds; then either the loop is left (`tr` is that round) or it
starts again at the load with `3` less fuel. -/
theorem spin_round {t : XThread} {r : Reg} {a : Nat} {c : Expr} (hF : SpinFacts t r a c)
    {dom : List Nat} (hdom : ∀ v ∈ dom, v < 2 ^ 32) (rs : Regs) {f : Nat} {s : State}
    (hs : s.rip = t.base) {trs : List Trace} (hx : exploreT t dom f s = some trs) {tr : Trace}
    (htr : tr ∈ trs) :
    ∃ v ∈ dom, ∃ f' s3, f = f' + 3 ∧
      (∀ q, s3.read q = if q = r then BitVec.ofNat 64 v else s.read q) ∧
      ((truthy (c.eval (rs.set r (BitVec.ofNat 64 v))) = false ∧ tr.acts = [ldA a v] ∧
          tr.final = s3) ∨
        (truthy (c.eval (rs.set r (BitVec.ofNat 64 v))) = true ∧ s3.rip = t.base ∧
          ∃ trs', exploreT t dom f' s3 = some trs' ∧ ∃ tr' ∈ trs',
            tr.acts = ldA a v :: tr'.acts ∧ tr.final = tr'.final)) := by
  obtain ⟨⟨mo, hl, hb, hi, ha⟩, hread, hsmall, k, m, cc, rel, hc, hk, hcmp, hj, hlen, htg⟩ := hF
  have hlen64 : t.code.length < 2 ^ 64 := by omega
  have hrip0 : s.rip = t.base + BitVec.ofNat 64 0 := by simp [hs]
  have hne0 : s.rip ≠ t.endRip := hrip0 ▸ endRip_ne (by omega) hlen64
  cases f with
  | zero => rw [exploreT_zero hne0] at hx; cases hx; simp at htr
  | succ f1 =>
  rw [exploreT_succ hne0, stepSym_load ((fetch_at hrip0 (by omega)).trans hl) hb hi ha hread] at hx
  simp only at hx
  obtain ⟨o, ho, trs1, hx1, tr1, htr1, rfl⟩ := mem_explored hx htr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ho
  have hv32 := hdom v hv
  simp only at hx1
  set s1 : State := { Silmaril.X86.Ext.Sz.d.write s r ((ldVal (valBytes v 4)).setWidth 32) with
    rip := s.rip + BitVec.ofNat 64 7 } with hs1
  have hrip1 : s1.rip = t.base + BitVec.ofNat 64 7 := by simp [s1, hs]
  have hne1 : s1.rip ≠ t.endRip := hrip1 ▸ endRip_ne (by omega) hlen64
  have hx1' : exploreT t dom f1 s1 = some trs1 := hx1
  cases f1 with
  | zero => rw [exploreT_zero hne1] at hx1'; cases hx1'; simp at htr1
  | succ f2 =>
  -- the compare
  have hrd := read_loaded s r v (s.rip + BitVec.ofNat 64 7)
  obtain ⟨fl, hstep2, hfl⟩ : ∃ fl, stepSym t dom s1 =
      some [([], { s1 with flags := fl, rip := s1.rip + BitVec.ofNat 64 m })] ∧
      cc.eval fl = some (truthy (c.eval (rs.set r (BitVec.ofNat 64 v)))) := by
    rcases hcmp with ⟨rfl, hf⟩ | ⟨kb, rfl, hf⟩
    · refine ⟨_, stepSym_test ((fetch_at hrip1 (by omega)).trans hf), ?_⟩
      rw [hrd]
      exact jump_test hc hv32 (by simp [Regs.set])
    · refine ⟨_, stepSym_cmp ((fetch_at hrip1 (by omega)).trans hf), ?_⟩
      rw [hrd, sx8 kb hk]
      exact jump_cmp hc hk hv32 (by simp [Regs.set])
  rw [exploreT_succ hne1, hstep2] at hx1'
  simp only at hx1'
  obtain ⟨o2, ho2, trs2, hx2, tr2, htr2, rfl⟩ := mem_explored hx1' htr1
  simp only [List.mem_singleton] at ho2
  subst ho2
  simp only at hx2
  set s2 : State := { s1 with flags := fl, rip := s1.rip + BitVec.ofNat 64 m } with hs2
  have hrip2 : s2.rip = t.base + BitVec.ofNat 64 (7 + m) := by
    simp [s2, hrip1, BitVec.ofNat_add, add_assoc]
  have hne2 : s2.rip ≠ t.endRip := hrip2 ▸ endRip_ne (by omega) hlen64
  have hx2' : exploreT t dom f2 s2 = some trs2 := hx2
  cases f2 with
  | zero => rw [exploreT_zero hne2] at hx2'; cases hx2'; simp at htr2
  | succ f3 =>
  set b := truthy (c.eval (rs.set r (BitVec.ofNat 64 v))) with hbdef
  have hstep3 := stepSym_jcc (dom := dom) ((fetch_at hrip2 (by omega)).trans hj) (b := b) hfl
  rw [exploreT_succ hne2, hstep3] at hx2'
  simp only at hx2'
  obtain ⟨o3, ho3, trs3, hx3, tr3, htr3, rfl⟩ := mem_explored hx2' htr2
  simp only [List.mem_singleton] at ho3
  subst ho3
  simp only at hx3
  have hregs3 : ∀ q, ({ s2 with rip := if b then s2.rip + BitVec.ofNat 64 2 + rel.signExtend 64
      else s2.rip + BitVec.ofNat 64 2 } : State).read q =
        if q = r then BitVec.ofNat 64 v else s.read q := by
    intro q
    show (Silmaril.X86.Ext.Sz.d.write s r ((ldVal (valBytes v 4)).setWidth 32)).read q = _
    exact regs_loaded s r q hv32
  have hnext : s2.rip + BitVec.ofNat 64 2 = t.endRip := by
    rw [hrip2, ← endRip_eq, ← hlen, add_assoc, ← BitVec.ofNat_add]
  refine ⟨v, hv, f3, _, by omega, hregs3, ?_⟩
  cases hbv : b
  · left
    refine ⟨hbdef.symm.trans hbv, ?_, ?_⟩ <;>
    · simp only [hbv, Bool.false_eq_true, ite_false] at hx3
      rw [exploreT_end hnext] at hx3
      cases hx3
      simp only [List.mem_singleton] at htr3
      subst htr3
      simp [Silmaril.X86.Litmus.Trace.acts, ldA]
  · right
    refine ⟨hbdef.symm.trans hbv, ?_, trs3, by simpa [hbv] using hx3, tr3, htr3, ?_, rfl⟩
    · simp only [ite_true]
      rw [hnext, ← htg, ← endRip_eq, ← hlen]
    · simp [Silmaril.X86.Litmus.Trace.acts, ldA]

theorem ldA_acts {a v : Nat} (hv : v < 2 ^ 32) (m : Mode) :
    (Lab.rd m .wb a 4 v).acts = normActs [ldA a v] := by
  simp [Lab.acts, ldAct, normActs, Act.norm, ldA, flavOf, valBytes_eq (by omega : v < 2 ^ 64)]

theorem run_load {dom : List Nat} {r : Reg} {m : Mode} {a v : Nat} (ha : a < 2 ^ 64)
    (hv : v ∈ dom) (hv32 : v < 2 ^ 32) (rs : Regs) :
    ([Lab.rd m .wb a 4 v], rs.set r (BitVec.ofNat 64 v)) ∈
      run dom (.load r m 4 .wb (.lit a)) rs := by
  simp only [run, List.mem_map, pick, List.mem_filter, decide_eq_true_eq, Expr.eval,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  exact ⟨v, ⟨hv, by omega⟩, rfl⟩

theorem set_read {s3 s : State} {rs : Regs} {K : List Reg} {r : Reg} {v : Nat}
    (h3 : ∀ q, s3.read q = if q = r then BitVec.ofNat 64 v else s.read q)
    (hrel : ∀ q, q ∉ K → s.read q = rs q) :
    ∀ q, q ∉ K → s3.read q = rs.set r (BitVec.ofNat 64 v) q := by
  intro q hq
  rw [h3 q]
  simp only [Regs.set]
  split
  · rfl
  · exact hrel q hq

/-- **A spin piece is sound**: every trace `exploreT` gives with fuel at most `3 (n + 1)` is a
run of the CIR spin with bound `n`, with the same actions and registers. -/
theorem spin_sound {t : XThread} {r : Reg} {a : Nat} {c : Expr} (hF : SpinFacts t r a c)
    {dom : List Nat} (hdom : ∀ v ∈ dom, v < 2 ^ 32) (mo : Mode) {K : List Reg} :
    ∀ (n f : Nat), f ≤ 3 * (n + 1) → ∀ (s : State) (rs : Regs), s.rip = t.base →
      (∀ q, q ∉ K → s.read q = rs q) → ∀ trs, exploreT t dom f s = some trs → ∀ tr ∈ trs,
        ∃ p ∈ run dom (spinStmt n r mo a c) rs, p.1.flatMap Lab.acts = normActs tr.acts ∧
          ∀ q, q ∉ K → tr.final.read q = p.2 q := by
  have ha : a < 2 ^ 64 := by
    obtain ⟨mo', _, _, _, ha⟩ := hF.load
    rw [← ha]; exact BitVec.isLt _
  have hlen : 0 < t.code.length := by
    obtain ⟨_, _, _, _, _, _, _, _, hl, _⟩ := hF.rest; omega
  have hlen64 : t.code.length < 2 ^ 64 := by have := hF.small; omega
  intro n
  induction n with
  | zero =>
    intro f hf s rs hs hrel trs hx tr htr
    obtain ⟨v, hv, f', s3, rfl, h3, hcase⟩ := spin_round hF hdom rs hs hx htr
    have hv32 := hdom v hv
    rcases hcase with ⟨hc, hacts, hfin⟩ | ⟨_, hs3, trs', hx', tr', htr', _, _⟩
    · refine ⟨([.rd mo .wb a 4 v], rs.set r (BitVec.ofNat 64 v)), ?_, ?_, ?_⟩
      · refine mem_run_seq.mpr ⟨_, run_load ha hv hv32 rs, ([], rs.set r (BitVec.ofNat 64 v)), ?_,
          by simp⟩
        simp [run, iter, hc]
      · simp [hacts, ldA_acts hv32]
      · rw [hfin]; exact set_read h3 hrel
    · have hf' : f' = 0 := by omega
      subst hf'
      rw [exploreT_zero (by rw [hs3]; simpa using endRip_ne (o := 0) hlen hlen64)] at hx'
      cases hx'; simp at htr'
  | succ n ih =>
    intro f hf s rs hs hrel trs hx tr htr
    obtain ⟨v, hv, f', s3, rfl, h3, hcase⟩ := spin_round hF hdom rs hs hx htr
    have hv32 := hdom v hv
    rcases hcase with ⟨hc, hacts, hfin⟩ | ⟨hc, hs3, trs', hx', tr', htr', hacts, hfin⟩
    · refine ⟨([.rd mo .wb a 4 v], rs.set r (BitVec.ofNat 64 v)), ?_, ?_, ?_⟩
      · refine mem_run_seq.mpr ⟨_, run_load ha hv hv32 rs, ([], rs.set r (BitVec.ofNat 64 v)), ?_,
          by simp⟩
        simp [run, iter, hc]
      · simp [hacts, ldA_acts hv32]
      · rw [hfin]; exact set_read h3 hrel
    · obtain ⟨p, hp, hpa, hpr⟩ := ih f' (by omega) s3 _ hs3 (set_read h3 hrel) trs' hx' tr' htr'
      refine ⟨([.rd mo .wb a 4 v] ++ p.1, p.2), ?_, ?_, ?_⟩
      · refine mem_run_seq.mpr ⟨_, run_load ha hv hv32 rs, p, ?_, by simp⟩
        simp only [run, iter, hc, ite_true]
        exact hp
      · rw [hacts]
        simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          hpa, ldA_acts hv32 mo]
        simp [normActs]
      · rw [hfin]; exact hpr

/-! ## Pads -/

theorem explore_end {t : XThread} {dom : List Nat} {f : Nat} {s : State} (h : s.rip = t.endRip) :
    explore t dom f s = some [⟨[], s⟩] := by
  unfold explore; simp [h]

theorem explore_zero {t : XThread} {dom : List Nat} {s : State} (h : s.rip ≠ t.endRip) :
    explore t dom 0 s = none := by
  unfold explore; simp [h]

theorem explore_succ {t : XThread} {dom : List Nat} {f : Nat} {s : State} (h : s.rip ≠ t.endRip) :
    explore t dom (f + 1) s = match stepSym t dom s with
      | none => none
      | some outs => (outs.mapM fun o => (explore t dom f o.2).map (consStep o.1 o.2)).map
          List.flatten := by
  conv => lhs; unfold explore
  simp only [h, ite_false]
  rfl

/-- **A pad piece is sound**: one `nop`, no action, registers unchanged. -/
theorem pad_sound {t : XThread} (h : padOk t = true) (hlen : t.code.length < 2 ^ 64)
    {dom : List Nat} {fuel : Nat} {s : State} (hs : s.rip = t.base) {trs : List Trace}
    (hx : explore t dom fuel s = some trs) :
    ∀ tr ∈ trs, tr.acts = [] ∧ ∀ q, tr.final.read q = s.read q := by
  unfold padOk at h
  split at h
  · rename_i k n hf
    simp only [decide_eq_true_eq] at h
    obtain ⟨hn, rfl⟩ := h
    have hrip0 : s.rip = t.base + BitVec.ofNat 64 0 := by simp [hs]
    have hne : s.rip ≠ t.endRip := hrip0 ▸ endRip_ne hn hlen
    cases fuel with
    | zero => rw [explore_zero hne] at hx; cases hx
    | succ f =>
      rw [explore_succ hne, stepSym_nop ((fetch_at hrip0 (by omega)).trans hf)] at hx
      have hend : ({ s with rip := s.rip + BitVec.ofNat 64 t.code.length } : State).rip =
          t.endRip := by simp [hs, endRip_eq]
      simp only [List.mapM_cons, List.mapM_nil, explore_end hend] at hx
      simp at hx
      subst hx
      intro tr htr
      simp [consStep] at htr
      subst htr
      exact ⟨by simp [Silmaril.X86.Litmus.Trace.acts], fun q => rfl⟩
  · cases h

/-! ## Pieces -/

theorem catTr_acts (a b : Trace) : (catTr a b).acts = a.acts ++ b.acts := by
  simp [catTr, Silmaril.X86.Litmus.Trace.acts]

theorem sub_base (th : SThread) (lo hi : Nat) : (th.sub lo hi).base = th.base + BitVec.ofNat 64 lo :=
  rfl

/-- **The pieces are sound**: every trace of `pexplore` is a run of the pieces' statements. -/
theorem pwalk_sound (th : SThread) {dom : List Nat} (hdom : ∀ v ∈ dom, v < 2 ^ 32) (fuel n : Nat) :
    ∀ (ps : List SPiece) (o : Nat) (K Z Kf : List Reg), pwalk th o ps K Z = some Kf →
      ∀ (s : State) (rs : Regs), s.rip = th.base + BitVec.ofNat 64 o → Rel K Z rs s →
        ∀ trs, pexplore th dom fuel n o ps s = some trs → ∀ tr ∈ trs,
          ∃ p ∈ run dom (chain (ps.flatMap (SPiece.ops n))) rs,
            p.1.flatMap Lab.acts = normActs tr.acts ∧ ∀ q, q ∉ Kf → tr.final.read q = p.2 q
  | [], o, K, Z, Kf, hw, s, rs, _, hrel, trs, hx, tr, htr => by
    simp only [pwalk] at hw
    split at hw
    · cases hw
      simp only [pexplore, Option.some.injEq] at hx
      subst hx
      simp only [List.mem_singleton] at htr
      subst htr
      exact ⟨([], rs), by simp [chain, run], by simp [normActs, Silmaril.X86.Litmus.Trace.acts],
        fun q hq => hrel.eq q hq⟩
    · cases hw
  | p :: ps, o, K, Z, Kf, hw, s, rs, hs, hrel, trs, hx, tr, htr => by
    simp only [pwalk] at hw
    split at hw
    swap
    · cases hw
    rename_i hcond
    obtain ⟨_, hlen⟩ := hcond
    simp only [pexplore] at hx
    obtain ⟨trs0, hx0, hrest⟩ := Option.bind_eq_some_iff.mp hx
    obtain ⟨rss, hm, rfl⟩ := Option.map_eq_some_iff.mp hrest
    obtain ⟨tr0, htr0, ys, hys, hy⟩ := mapM_mem hm htr
    obtain ⟨ys', hys', rfl⟩ := Option.map_eq_some_iff.mp hys
    obtain ⟨tr1, htr1, rfl⟩ := List.mem_map.mp hy
    -- the piece itself
    have hs' : s.rip = (th.sub o (o + p.len)).base := by rw [sub_base]; exact hs
    obtain ⟨K', p0, hp0, hpa0, hpr0, hw'⟩ : ∃ K' : List Reg, ∃ p0 ∈ run dom (chain (p.ops n)) rs,
        p0.1.flatMap Lab.acts = normActs tr0.acts ∧ (∀ q, q ∉ K' → tr0.final.read q = p0.2 q) ∧
        pwalk th (o + p.len) ps K' [] = some Kf := by
      cases p with
      | seg its =>
        simp only at hw hx0
        split at hw
        · rename_i K' hwalk
          obtain ⟨p0, hp0, hpa, hpr⟩ := walk_sound hlen (fun _ => hdom) hwalk hs' hrel hx0 tr0 htr0
          exact ⟨K', p0, hp0, hpa, hpr, hw⟩
        · cases hw
      | pad len =>
        simp only at hw hx0
        split at hw
        · rename_i hpad
          obtain ⟨hacts, hregs⟩ := pad_sound hpad hlen hs' hx0 tr0 htr0
          refine ⟨K, ([], rs), by simp [SPiece.ops, chain, run], by simp [hacts, normActs], ?_, hw⟩
          intro q hq; rw [hregs]; exact hrel.eq q hq
        · cases hw
      | spin len r m a c =>
        simp only at hw hx0
        split at hw
        · rename_i hspin
          obtain ⟨p0, hp0, hpa, hpr⟩ := spin_sound (spinOk_facts hspin) hdom m n (3 * (n + 1))
            (le_refl _) s rs hs' hrel.eq trs0 hx0 tr0 htr0
          exact ⟨K, p0, run_chain_one hp0, hpa, hpr, hw⟩
        · cases hw
    -- the rest
    have hrel' : Rel K' [] p0.2 { tr0.final with rip := th.base + BitVec.ofNat 64 (o + p.len) } :=
      ⟨fun q hq => hpr0 q hq, fun _ h => by simp at h⟩
    obtain ⟨p1, hp1, hpa1, hpr1⟩ := pwalk_sound th hdom fuel n ps (o + p.len) K' [] Kf hw' _ p0.2
      rfl hrel' ys' hys' tr1 htr1
    refine ⟨(p0.1 ++ p1.1, p1.2), ?_, ?_, ?_⟩
    · have := run_chain_append (p.ops n) (ps.flatMap (SPiece.ops n)) hp0 hp1
      simpa [List.flatMap_cons] using this
    · simp only [List.flatMap_append, hpa0, hpa1, catTr_acts, normActs_append]
    · intro q hq; simp only [catTr]; exact hpr1 q hq

/-! ## Threads -/

/-- **A spin-validated thread is sound**: every x86 trace (spins retrying at most `n` times) is
a run of the CIR thread with spin bound `n` over the same domain, with the same actions up to
`normActs` and the same final registers outside the clobber set. -/
theorem stvRun_sound {th : SThread} {c : SCert} {K : List Reg} (h : stvRun th c = some K)
    {dom : List Nat} (hdom : ∀ v ∈ dom, v < 2 ^ 32) {fuel n : Nat} {trs : List Trace}
    (hx : pexplore th dom fuel n 0 c.pieces th.init = some trs) :
    ∀ tr ∈ trs, ∃ p ∈ run dom (c.body n) Regs.zero,
      p.1.flatMap Lab.acts = normActs tr.acts ∧ ∀ q, q ∉ K → tr.final.read q = p.2 q := by
  unfold stvRun at h
  dsimp only at h
  split at h
  · rename_i hok
    obtain ⟨hrip, hregs⟩ := hok
    simp only [List.all_eq_true, beq_iff_eq] at hregs
    let pc : Cert := ⟨c.pro, []⟩
    have hrel : Rel [] (allRegs.filter fun r => decide ((pc.proRegs r).toNat < 2 ^ 32))
        pc.proRegs th.init := by
      constructor
      · intro r _; exact hregs r (mem_allRegs r)
      · intro r hr
        simp only [List.mem_filter, decide_eq_true_eq] at hr
        rw [hregs r (mem_allRegs r)]; exact hr.2
    intro tr htr
    obtain ⟨p, hp, hpa, hpr⟩ := pwalk_sound th hdom fuel n c.pieces 0 [] _ K h th.init pc.proRegs
      (by simp [hrip]) hrel trs hx tr htr
    have hrun := run_chain_append (c.pro.map fun p => .assign p.1 (.lit p.2))
      (c.pieces.flatMap (SPiece.ops n)) (run_pro (dom := dom) c.pro Regs.zero) hp
    exact ⟨_, hrun, by simpa using hpa, hpr⟩
  · cases h

/-! ## Tests -/

theorem cond_avoids {cond : Silmaril.X86.MemoryModel.Litmus.Cond} {Ks : List (List Reg)}
    (h : condAvoids cond Ks = true) {f f' : Final} (hm : f'.mem = f.mem)
    (hr : ∀ i r, r ∉ Ks.getD i [] → f'.regs i r = f.regs i r) {w : Silmaril.X86.MemoryModel.Litmus.Cond}
    (hw : w.atoms = cond.atoms) : w.eval f' = w.eval f := by
  apply cond_eval_congr
  intro a ha
  rw [hw] at ha
  cases a with
  | mem ad sz v => simp [Atom.eval, hm]
  | reg i r bits v =>
    have hav : !(Ks.getD i []).contains r = true := by
      have := List.all_eq_true.mp h _ ha
      simpa using this
    have hr' : r ∉ Ks.getD i [] := by simpa using hav
    simp [Atom.eval, hr i r hr']

/-- **Refinement of a spin-validated test**, for every spin bound `n`. -/
theorem STest.refines {c : STest} (h : c.tvOk = true) (hd : c.domOk = true) {n : Nat}
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop} {f : Final} (hf : c.XBehav n M f) :
    ∃ f', BehavIn (c.prog n) c.dom M f' ∧ c.test.witness.eval f' = c.test.witness.eval f := by
  obtain ⟨T, hT, hf⟩ := hf
  simp only [STest.tvOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hlen, hK⟩ := h
  split at hK
  swap
  · cases hK
  rename_i Ks hKs
  obtain ⟨hKl, hKg⟩ := mapM_id_spec hKs
  obtain ⟨hTl, hTg⟩ := mapM_id_spec hT
  simp only [List.length_mapIdx] at hKl hTl
  have hdom : ∀ v ∈ c.dom, v < 2 ^ 32 := by
    simpa [STest.domOk] using hd
  let U := (c.prog n).traces c.dom
  have hUl : U.length = c.threads.length := by simp [U, Prog.traces, STest.prog]
  obtain ⟨f', hf', hmem, hregs⟩ := axReach_pick (t := (c.prog n).memTest) (U := U) (Ks := Ks)
    (by omega) (fun k h₁ h₂ a ha => by
      have hk : k < c.threads.length := by omega
      have hx := hTg k (by simpa using hk) (by omega)
      simp only [List.getElem_mapIdx] at hx
      have htv := hKg k (by simpa using hk) (by omega)
      simp only [List.getElem_mapIdx] at htv
      obtain ⟨p, hp, hacts, hregs⟩ := stvRun_sound htv hdom hx a ha
      refine ⟨(⟨(c.cert k).body n, false⟩ : Thread).xtrace k p, ?_, ?_, ?_⟩
      · simp only [U, Prog.traces, STest.prog, List.getElem_mapIdx]
        exact List.mem_map_of_mem hp
      · rw [← threadUnits_normActs, ← hacts]
        simp [Thread.xtrace, Thread.acts, Silmaril.X86.Litmus.Trace.acts]
      · intro r hr
        have : Ks.getD k [] = Ks[k] := by simp [hKl, hk]
        rw [hregs r (by rwa [← this])]
        rfl) hf
  exact ⟨f', hf', cond_avoids hK hmem hregs (witness_atoms c.test)⟩

end Silmaril.Proofs.X86.Concurrency.Cir.TvSpin
