module

public import Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Sw

/-!
# The seqlock on TSO, for any writes and readers (`Task.seqlockTso`)

Proved with the single-writer logic `Sw`. The writer owns the three seqlock words, reader `j`
owns its two output cells. The protocol invariant is that the writer's log is a prefix of its
**intended log** `wlog`: per write `j`, the stores `seq := 2j+1`, `a := ws[j].1`,
`b := ws[j].2`, `seq := 2j+2`.

After `f` of the writer's stores have reached memory, memory holds `seqAt f`, `aAt f`, `bAt f`
(`cells_wlog`). A reader's four loads read memory (TSO: a reader buffers only its own cells) at
flush counts `fQ ≤ fA ≤ fB ≤ fR`, because flushing is monotone and the reader's loads are
performed in order. If the two reads of `seq` agree and are even, the flush count did not move
(`seqAt f` is even exactly at multiples of `4`, and strictly grows between them, as the
`2 ^ 31` bound on the number of writes rules out wrap-around): the data words were read at the
same flush count `4j`, where they are the pair of write `j` (`snap_ok`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Seq

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Prim
open Silmaril.X86.Concurrency.Cir.Prim.Clients
open Silmaril.X86.Concurrency.Cir.TvCfg (setB notE mask32)
open Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Sw

/-! ## The writer's intended log -/

section Pure

variable (s : Nat) (ws : List (Nat × Nat))

/-- The `j`-th written pair. -/
def pr (j : Nat) : Nat × Nat := ws.getD j (0, 0)

/-- The `n`-th store of the writer. -/
def wEnt (n : Nat) : Nat × Nat :=
  if n % 4 = 0 then (s, 2 * (n / 4) + 1)
  else if n % 4 = 1 then (s + 4, (pr ws (n / 4)).1)
  else if n % 4 = 2 then (s + 8, (pr ws (n / 4)).2)
  else (s, 2 * (n / 4) + 2)

/-- The writer's first `f` stores. -/
def wlog (f : Nat) : List (Nat × Nat) := (List.range f).map (wEnt s ws)

/-- `seq` after `f` stores. -/
def seqAt (f : Nat) : Nat := if f % 4 = 0 then f / 2 else 2 * (f / 4) + 1

/-- `a` after `f` stores. -/
def aAt (f : Nat) : Nat := if f < 2 then 0 else (pr ws ((f - 2) / 4)).1

/-- `b` after `f` stores. -/
def bAt (f : Nat) : Nat := if f < 3 then 0 else (pr ws ((f - 3) / 4)).2

theorem wlog_succ (f : Nat) : wlog s ws (f + 1) = wlog s ws f ++ [wEnt s ws f] := by
  simp [wlog, List.range_succ]

theorem take_wlog {f n : Nat} (h : n ≤ f) : (wlog s ws f).take n = wlog s ws n := by
  rw [wlog, wlog, ← List.map_take, List.take_range, Nat.min_eq_left h]

variable {s ws}

/-- **Memory after `f` writer stores.** -/
theorem cells_wlog {init : Heap} (h0 : init s = some 0) (h4 : init (s + 4) = some 0)
    (h8 : init (s + 8) = some 0) (f : Nat) :
    cellAfter init (wlog s ws f) s = some (seqAt f) ∧
    cellAfter init (wlog s ws f) (s + 4) = some (aAt ws f) ∧
    cellAfter init (wlog s ws f) (s + 8) = some (bAt ws f) := by
  induction f with
  | zero => simp [wlog, cellAfter, lastV, h0, h4, h8, seqAt, aAt, bAt]
  | succ f ih =>
    obtain ⟨ih0, ih4, ih8⟩ := ih
    rw [wlog_succ, cellAfter_snoc, cellAfter_snoc, cellAfter_snoc]
    have hm : f % 4 = 0 ∨ f % 4 = 1 ∨ f % 4 = 2 ∨ f % 4 = 3 := by omega
    rcases hm with hm | hm | hm | hm
    · simp only [wEnt, hm, ite_true]
      refine ⟨?_, ?_, ?_⟩
      · simp only [seqAt]; congr 1; split <;> omega
      · rw [ite_f (by omega), ih4]; congr 1; simp only [aAt]
        by_cases hf : f < 2
        · rw [ite_t hf, ite_t (by omega)]
        · rw [ite_f hf, ite_f (by omega), show (f + 1 - 2) / 4 = (f - 2) / 4 by omega]
      · rw [ite_f (by omega), ih8]; congr 1; simp only [bAt]
        by_cases hf : f < 3
        · rw [ite_t hf, ite_t (by omega)]
        · rw [ite_f hf, ite_f (by omega), show (f + 1 - 3) / 4 = (f - 3) / 4 by omega]
    · simp only [wEnt, hm, show (1 : Nat) ≠ 0 by decide, ite_true, ite_false]
      refine ⟨?_, ?_, ?_⟩
      · rw [ite_f (by omega), ih0]; congr 1; simp only [seqAt]; split <;> split <;> omega
      · simp only [aAt]; congr 1
        rw [ite_f (by omega), show (f + 1 - 2) / 4 = f / 4 by omega]
      · rw [ite_f (by omega), ih8]; congr 1; simp only [bAt]
        by_cases hf : f < 3
        · rw [ite_t hf, ite_t (by omega)]
        · rw [ite_f hf, ite_f (by omega), show (f + 1 - 3) / 4 = (f - 3) / 4 by omega]
    · simp only [wEnt, hm, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide,
        ite_true, ite_false]
      refine ⟨?_, ?_, ?_⟩
      · rw [ite_f (by omega), ih0]; congr 1; simp only [seqAt]; split <;> split <;> omega
      · rw [ite_f (by omega), ih4]; congr 1; simp only [aAt]
        rw [ite_f (by omega), ite_f (by omega), show (f + 1 - 2) / 4 = (f - 2) / 4 by omega]
      · simp only [bAt]; congr 1
        rw [ite_f (by omega), show (f + 1 - 3) / 4 = f / 4 by omega]
    · simp only [wEnt, hm, show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide,
        show (3 : Nat) ≠ 2 by decide, ite_false]
      refine ⟨?_, ?_, ?_⟩
      · simp only [seqAt, ite_true]; congr 1; split <;> omega
      · rw [ite_f (by omega), ih4]; congr 1; simp only [aAt]
        rw [ite_f (by omega), ite_f (by omega), show (f + 1 - 2) / 4 = (f - 2) / 4 by omega]
      · rw [ite_f (by omega), ih8]; congr 1; simp only [bAt]
        rw [ite_f (by omega), ite_f (by omega), show (f + 1 - 3) / 4 = (f - 3) / 4 by omega]

theorem seqAt_le (f : Nat) : seqAt f ≤ f / 2 + 1 := by
  simp only [seqAt]; split <;> omega

/-- **The snapshot check**: equal, even reads of `seq` around the data reads mean the data
words were read at one flush count `4j`, where they hold write `j`'s pair. -/
theorem snap_ok {fQ fA fB fR : Nat} (h1 : fQ ≤ fA) (h2 : fA ≤ fB) (h3 : fB ≤ fR)
    (h4 : fR ≤ 4 * ws.length) (he : seqAt fQ % 2 = 0) (hq : seqAt fQ = seqAt fR) :
    ∃ p ∈ (0, 0) :: ws, aAt ws fA = p.1 ∧ bAt ws fB = p.2 := by
  have hQ : fQ % 4 = 0 := by
    simp only [seqAt] at he; split at he
    · assumption
    · omega
  have hR : fR = fQ := by
    simp only [seqAt, hQ, ite_true] at hq
    split at hq <;> omega
  have hA : fA = fQ := by omega
  have hB : fB = fQ := by omega
  rw [hA, hB]
  by_cases h0 : fQ = 0
  · subst h0; exact ⟨(0, 0), List.mem_cons_self, by simp [aAt], by simp [bAt]⟩
  · refine ⟨pr ws (fQ / 4 - 1), List.mem_cons_of_mem _ ?_, ?_, ?_⟩
    · simp only [pr]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    · simp only [aAt]; rw [ite_f (by omega), show (fQ - 2) / 4 = fQ / 4 - 1 by omega]
    · simp only [bAt]; rw [ite_f (by omega), show (fQ - 3) / 4 = fQ / 4 - 1 by omega]

end Pure

/-! ## The protocol -/

section Proto

variable (s : Nat) (ws : List (Nat × Nat)) (outs : List Nat)

/-- **Ownership**: the writer (thread `0`) owns the seqlock words, reader `j + 1` its output
pair. -/
def own (t c : Nat) : Prop :=
  (t = 0 ∧ (c = s ∨ c = s + 4 ∨ c = s + 8)) ∨
  (∃ j, j < outs.length ∧ t = j + 1 ∧ (c = outs.getD j 0 ∨ c = outs.getD j 0 + 4))

/-- **The protocol invariant**: the writer's log is a prefix of its intended log. -/
def gp (g : W) : Prop := ∃ f, f ≤ 4 * ws.length ∧ g.log 0 = wlog s ws f

/-- The postconditions: reader `t` has logged the two stores of a written pair. -/
def post (t : Nat) (_ : Regs) (g : W) : Prop :=
  t = 0 ∨ ∃ p ∈ (0, 0) :: ws, g.log t = [(outs.getD (t - 1) 0, p.1), (outs.getD (t - 1) 0 + 4, p.2)]

/-- The writer's statement. -/
def writer (L : Nat) : Stmt := Tv.chain (ws.map fun p => Tv.chain [.assign .rsi (.lit p.1),
  .assign .rdx (.lit p.2), SeqWrite.cert.body L])

theorem gp_flush (g : W) (t : Nat) (h : gp s ws g) : gp s ws (g.flush t) := h

end Proto

theorem seqWrite_body (L : Nat) : SeqWrite.cert.body L = Tv.chain [SeqWrite.ld, SeqWrite.odd,
    SeqWrite.even, SeqWrite.stOdd, SeqWrite.stA, SeqWrite.stB, SeqWrite.stEven] := rfl

theorem set_apply (rs : Regs) (r q : Reg) (v : Word) :
    (rs.set r v) q = if q = r then v else rs q := rfl

/-! ## The writer -/

section Writer

variable {s : Nat} {ws : List (Nat × Nat)} {outs : List Nat} {init : Heap}

theorem own_w {c : Nat} (h : c = s ∨ c = s + 4 ∨ c = s + 8) : own s outs 0 c := Or.inl ⟨rfl, h⟩

theorem wEnt0 (i : Nat) : wEnt s ws (4 * i) = (s, 2 * i + 1) := by
  simp only [wEnt]; rw [ite_t (by omega)]; congr 2; omega

theorem wEnt1 (i : Nat) : wEnt s ws (4 * i + 1) = (s + 4, (pr ws i).1) := by
  simp only [wEnt]; rw [ite_f (by omega), ite_t (by omega)]; congr 3; omega

theorem wEnt2 (i : Nat) : wEnt s ws (4 * i + 2) = (s + 8, (pr ws i).2) := by
  simp only [wEnt]; rw [ite_f (by omega), ite_f (by omega), ite_t (by omega)]; congr 3; omega

theorem wEnt3 (i : Nat) : wEnt s ws (4 * i + 3) = (s, 2 * i + 2) := by
  simp only [wEnt]; rw [ite_f (by omega), ite_f (by omega), ite_f (by omega)]; congr 2; omega

theorem gp_push {g : W} {f : Nat} (hg : g.log 0 = wlog s ws f) (hf : f < 4 * ws.length)
    {e : Nat × Nat} (he : e = wEnt s ws f) :
    gp s ws (g.push 0 e) ∧ (g.push 0 e).log 0 = wlog s ws (f + 1) := by
  have : (g.push 0 e).log 0 = wlog s ws (f + 1) := by rw [push_log, hg, he, wlog_succ]
  exact ⟨⟨f + 1, by omega, this⟩, this⟩

/-- The four stores of `seq_write`. -/
theorem write_stores (hs : s + 12 < 2 ^ 64) (hlen : ws.length < 2 ^ 31) {i : Nat}
    (hi : i < ws.length)
    {Q : Regs → W → Prop} {rs : Regs} (hrdi : rs .rdi = BitVec.ofNat 64 s)
    (hrsi : rs .rsi = BitVec.ofNat 64 (pr ws i).1) (hrdx : rs .rdx = BitVec.ofNat 64 (pr ws i).2)
    (hrax : rs .rax = BitVec.ofNat 64 (2 * i + 2)) (hrcx : rs .rcx = BitVec.ofNat 64 (2 * i + 1))
    (hp1 : (pr ws i).1 < 2 ^ 32) (hp2 : (pr ws i).2 < 2 ^ 32)
    (k : ∀ g', g'.log 0 = wlog s ws (4 * i + 4) →
      TSafe (own s outs) init (gp s ws) 0 Q .skip rs g')
    (g : W) (hg : g.log 0 = wlog s ws (4 * i)) :
    TSafe (own s outs) init (gp s ws) 0 Q
      (Tv.chain [SeqWrite.stOdd, SeqWrite.stA, SeqWrite.stB, SeqWrite.stEven]) rs g := by
  have h2i : 2 * i + 2 < 2 ^ 32 := by
    have : (2 : Nat) ^ 32 = 2 * 2 ^ 31 := by decide
    omega
  have hs' : s < 2 ^ 64 := by omega
  have ha : ∀ d, d ≤ 8 → ((at_ .rdi d).eval rs).toNat = s + d := fun d hd =>
    eval_at d hrdi (by omega)
  simp only [Tv.chain]
  refine tsafe_seq_store _ (stab_log _) ?_ ?_ hg
  · rw [ha 0 (by omega)]; exact own_w (Or.inl rfl)
  intro g hg _ _
  rw [ha 0 (by omega), eval_reg_mod hrcx (by omega), Nat.add_zero]
  obtain ⟨hgp, hl⟩ := gp_push hg (by omega) (wEnt0 i).symm
  refine ⟨hgp, ?_⟩
  refine tsafe_seq_store _ (stab_log _) ?_ ?_ hl
  · rw [ha 4 (by omega)]; exact own_w (Or.inr (Or.inl rfl))
  intro g hg _ _
  rw [ha 4 (by omega), eval_reg_mod hrsi hp1]
  obtain ⟨hgp, hl⟩ := gp_push hg (by omega) (wEnt1 i).symm
  refine ⟨hgp, ?_⟩
  refine tsafe_seq_store _ (stab_log _) ?_ ?_ hl
  · rw [ha 8 (by omega)]; exact own_w (Or.inr (Or.inr rfl))
  intro g hg _ _
  rw [ha 8 (by omega), eval_reg_mod hrdx hp2]
  obtain ⟨hgp, hl⟩ := gp_push hg (by omega) (wEnt2 i).symm
  refine ⟨hgp, ?_⟩
  refine tsafe_seq_store _ (stab_log _) ?_ ?_ hl
  · rw [ha 0 (by omega)]; exact own_w (Or.inl rfl)
  intro g hg _ _
  rw [ha 0 (by omega), eval_reg_mod hrax (by omega), Nat.add_zero]
  obtain ⟨hgp, hl⟩ := gp_push hg (by omega) (wEnt3 i).symm
  exact ⟨hgp, k _ hl⟩

/-- One `seq_write` call: from log `wlog (4i)`, the writer ends with log `wlog (4i + 4)`. -/
theorem write_one (hU : ∀ t u c, own s outs t c → own s outs u c → t = u)
    (hs : s + 12 < 2 ^ 64) (hws : ∀ p ∈ ws, p.1 < 2 ^ 32 ∧ p.2 < 2 ^ 32)
    (hlen : ws.length < 2 ^ 31) (h0 : init s = some 0) (h4 : init (s + 4) = some 0)
    (h8 : init (s + 8) = some 0) (L i : Nat) (hi : i < ws.length)
    {Q : Regs → W → Prop} (rs : Regs) (g : W) (hrdi : rs .rdi = BitVec.ofNat 64 s)
    (hg : g.log 0 = wlog s ws (4 * i))
    (k : ∀ rs' g', rs' .rdi = BitVec.ofNat 64 s → g'.log 0 = wlog s ws (4 * i + 4) →
      TSafe (own s outs) init (gp s ws) 0 Q .skip rs' g') :
    TSafe (own s outs) init (gp s ws) 0 Q
      (Tv.chain [.assign .rsi (.lit (pr ws i).1), .assign .rdx (.lit (pr ws i).2),
        SeqWrite.cert.body L]) rs g := by
  have hp : pr ws i ∈ ws := by
    simp only [pr]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem _
  obtain ⟨hp1, hp2⟩ := hws _ hp
  have h2i : 2 * i + 2 < 2 ^ 32 := by
    have : (2 : Nat) ^ 32 = 2 * 2 ^ 31 := by decide
    omega
  simp only [Tv.chain, seqWrite_body]
  apply tsafe_seq_assign
  apply tsafe_seq_assign
  apply tsafe_seq
  -- `mov eax, [rdi]`
  refine tsafe_seq_load (fun g => g.log 0 = wlog s ws (4 * i)) (stab_log _) ?_ hg
  intro g v hg _ _ _ hrd
  have hs' : s < 2 ^ 64 := by omega
  simp only [eval_at', set_apply, hrdi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs', Nat.add_zero,
    reduceCtorEq, ite_false] at hrd
  have hv := rdOk_own hU (own_w (Or.inl rfl)) hrd
  rw [hg, (cells_wlog h0 h4 h8 _).1] at hv
  have hv : v = 2 * i := by
    simp only [Option.some.injEq, seqAt] at hv; rw [ite_t (by omega)] at hv; omega
  subst hv
  apply tsafe_seq_assign
  apply tsafe_seq_assign
  refine write_stores hs hlen hi (rs := _) ?_ ?_ ?_ ?_ ?_ hp1 hp2
    (fun g' hl => tsafe_skip_of (k _ g' ?_ hl)) g hg
  · simp [set_apply, hrdi]
  · simp [set_apply, Expr.eval]
  · simp [set_apply, Expr.eval]
  · apply bv_eq_ofNat (by omega)
    simp only [set_apply, reduceCtorEq, ite_true, ite_false, Expr.eval, toNat_mask32, op32,
      BinOp.eval, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · apply bv_eq_ofNat (by omega)
    simp only [set_apply, reduceCtorEq, ite_true, ite_false, Expr.eval, toNat_mask32,
      BinOp.eval, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · simp [set_apply, hrdi]

/-- The writer is safe, for every loop bound. -/
theorem writer_safe (hU : ∀ t u c, own s outs t c → own s outs u c → t = u)
    (hs : s + 12 < 2 ^ 64) (hws : ∀ p ∈ ws, p.1 < 2 ^ 32 ∧ p.2 < 2 ^ 32)
    (hlen : ws.length < 2 ^ 31) (h0 : init s = some 0) (h4 : init (s + 4) = some 0)
    (h8 : init (s + 8) = some 0) (L : Nat) (rs : Regs) (hrdi : rs .rdi = BitVec.ofNat 64 s) :
    TSafe (own s outs) init (gp s ws) 0 (post ws outs 0) (writer ws L) rs W.zero := by
  refine tsafe_chain (fun i rs g => rs .rdi = BitVec.ofNat 64 s ∧ g.log 0 = wlog s ws (4 * i))
    _ 0 (fun i hi rs g h => ?_) (fun rs g _ => tsafe_skip (fun _ _ _ _ _ _ => Or.inl rfl)
      (Or.inl rfl)) rs W.zero ⟨hrdi, rfl⟩
  simp only [List.length_map] at hi
  simp only [Nat.zero_add, List.getElem_map] at h ⊢
  have hpi : ws[i] = pr ws i := by
    simp only [pr]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  rw [hpi]
  exact write_one hU hs hws hlen h0 h4 h8 L i hi rs g h.1 h.2 (fun rs' g' h1 h2 =>
    tsafe_skip (fun _ _ _ h r _ => ⟨h.1, r.1.trans h.2⟩)
      ⟨h1, by rw [h2, show 4 * (i + 1) = 4 * i + 4 by omega]⟩)

end Writer

/-! ## The readers -/

/-- The context of a reader proof. -/
structure Ctx (s : Nat) (ws : List (Nat × Nat)) (outs : List Nat) (init : Heap) (t : Nat) :
    Prop where
  hU : ∀ t u c, own s outs t c → own s outs u c → t = u
  hs : s + 12 < 2 ^ 64
  hlen : ws.length < 2 ^ 31
  hws : ∀ p ∈ ws, p.1 < 2 ^ 32 ∧ p.2 < 2 ^ 32
  h0 : init s = some 0
  h4 : init (s + 4) = some 0
  h8 : init (s + 8) = some 0
  ht : t ≠ 0

section Reader

variable {s : Nat} {ws : List (Nat × Nat)} {outs : List Nat} {init : Heap} {t o : Nat}

/-- The reader's fixed registers and empty log. -/
def base (s o t : Nat) (rs : Regs) (g : W) : Prop :=
  rs .rdi = BitVec.ofNat 64 s ∧ rs .rsi = BitVec.ofNat 64 o ∧ g.log t = []

/-- After the first read of `seq`. -/
def A1 (s o t : Nat) (ws : List (Nat × Nat)) (rs : Regs) (g : W) : Prop :=
  base s o t rs g ∧ ∃ fQ, fQ ≤ g.fl 0 ∧ fQ ≤ 4 * ws.length ∧ rs .rax = BitVec.ofNat 64 (seqAt fQ)

/-- After the read of `a`. -/
def A2 (s o t : Nat) (ws : List (Nat × Nat)) (rs : Regs) (g : W) : Prop :=
  base s o t rs g ∧ ∃ fQ fA, fQ ≤ fA ∧ fA ≤ g.fl 0 ∧ fA ≤ 4 * ws.length ∧
    rs .rax = BitVec.ofNat 64 (seqAt fQ) ∧ rs .rcx = BitVec.ofNat 64 (aAt ws fA)

/-- After the read of `b`. -/
def A3 (s o t : Nat) (ws : List (Nat × Nat)) (rs : Regs) (g : W) : Prop :=
  base s o t rs g ∧ ∃ fQ fA fB, fQ ≤ fA ∧ fA ≤ fB ∧ fB ≤ g.fl 0 ∧ fB ≤ 4 * ws.length ∧
    rs .rax = BitVec.ofNat 64 (seqAt fQ) ∧ rs .rcx = BitVec.ofNat 64 (aAt ws fA) ∧
    rs .rdx = BitVec.ofNat 64 (bAt ws fB)

/-- After the second read of `seq`, with the first one even. -/
def A4 (s o t : Nat) (ws : List (Nat × Nat)) (rs : Regs) (g : W) : Prop :=
  base s o t rs g ∧ ∃ fQ fA fB fR, fQ ≤ fA ∧ fA ≤ fB ∧ fB ≤ fR ∧ fR ≤ g.fl 0 ∧
    fR ≤ 4 * ws.length ∧ seqAt fQ % 2 = 0 ∧
    rs .rax = BitVec.ofNat 64 (seqAt fQ) ∧ rs .rcx = BitVec.ofNat 64 (aAt ws fA) ∧
    rs .rdx = BitVec.ofNat 64 (bAt ws fB) ∧ rs .r8 = BitVec.ofNat 64 (seqAt fR)

theorem base_stab {Gp : W → Prop} (rs : Regs) : Stab Gp t (base s o t rs) :=
  fun _ _ h r _ => ⟨h.1, h.2.1, r.1.trans h.2.2⟩

theorem A1_stab {Gp : W → Prop} (rs : Regs) : Stab Gp t (A1 s o t ws rs) :=
  fun g g' ⟨hb, fQ, h1, h2, h3⟩ r hg =>
    ⟨base_stab rs g g' hb r hg, fQ, h1.trans (r.2.2.1 0), h2, h3⟩

theorem A2_stab {Gp : W → Prop} (rs : Regs) : Stab Gp t (A2 s o t ws rs) :=
  fun g g' ⟨hb, fQ, fA, h1, h2, h3, h4, h5⟩ r hg =>
    ⟨base_stab rs g g' hb r hg, fQ, fA, h1, h2.trans (r.2.2.1 0), h3, h4, h5⟩

theorem A3_stab {Gp : W → Prop} (rs : Regs) : Stab Gp t (A3 s o t ws rs) :=
  fun g g' ⟨hb, fQ, fA, fB, h1, h2, h3, h4, h5, h6, h7⟩ r hg =>
    ⟨base_stab rs g g' hb r hg, fQ, fA, fB, h1, h2, h3.trans (r.2.2.1 0), h4, h5, h6, h7⟩

theorem A4_stab {Gp : W → Prop} (rs : Regs) : Stab Gp t (A4 s o t ws rs) :=
  fun g g' ⟨hb, fQ, fA, fB, fR, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ r hg =>
    ⟨base_stab rs g g' hb r hg, fQ, fA, fB, fR, h1, h2, h3, h4.trans (r.2.2.1 0), h5, h6, h7, h8,
      h9, h10⟩

/-- A reader's load of a seqlock word reads memory at the writer's current flush count. -/
theorem rd_step (X : Ctx s ws outs init t) {dst : Reg} {m : Mode} {d : Nat}
    (hd : d = 0 ∨ d = 4 ∨ d = 8) {Q : Regs → W → Prop} {rs : Regs}
    (hrdi : rs .rdi = BitVec.ofNat 64 s) (P : W → Prop) (hP : Stab (gp s ws) t P)
    (k : ∀ g v, P g → g.fl 0 ≤ 4 * ws.length →
      cellAfter init (wlog s ws (g.fl 0)) (s + d) = some v →
      TSafe (own s outs) init (gp s ws) t Q .skip (rs.set dst (BitVec.ofNat 64 v)) g)
    {g : W} (hg : P g) :
    TSafe (own s outs) init (gp s ws) t Q (.load dst m 4 .wb (at_ .rdi d)) rs g := by
  refine tsafe_load P hP (fun g v hp hgp hw _ hrd => ?_) hg
  rw [eval_at d hrdi (by have := X.hs; omega)] at hrd
  have h := rdOk_other X.hU (own_w (by omega)) (Ne.symm X.ht) hrd
  obtain ⟨f, hf, hl⟩ := hgp
  have hfl : g.fl 0 ≤ f := by have := hw 0; rw [hl] at this; simpa [wlog] using this
  rw [hl, take_wlog _ _ hfl] at h
  exact k g v hp (hfl.trans hf) h

theorem seqAt_lt (hlen : ws.length < 2 ^ 31) {f : Nat} (hf : f ≤ 4 * ws.length) :
    seqAt f < 2 ^ 32 := by
  have := seqAt_le f
  have : (2 : Nat) ^ 32 = 2 * 2 ^ 31 := by decide
  omega

theorem pr_lt (X : Ctx s ws outs init t) (j : Nat) :
    (pr ws j).1 < 2 ^ 32 ∧ (pr ws j).2 < 2 ^ 32 := by
  simp only [pr]
  rw [List.getD_eq_getElem?_getD]
  cases h : ws[j]? with
  | none => simp
  | some p => exact X.hws p (List.mem_of_getElem? h)

theorem aAt_lt (X : Ctx s ws outs init t) (f : Nat) : aAt ws f < 2 ^ 32 := by
  simp only [aAt]; split
  · decide
  · exact (pr_lt X _).1

theorem bAt_lt (X : Ctx s ws outs init t) (f : Nat) : bAt ws f < 2 ^ 32 := by
  simp only [bAt]; split
  · decide
  · exact (pr_lt X _).2

end Reader

theorem even_of {rs : Regs} {x : Nat} (h : truthy ((notE SeqRead.zEven).eval rs) = false)
    (hx : rs .rax = BitVec.ofNat 64 x) (hx' : x < 2 ^ 64) : x % 2 = 0 := by
  rw [truthy_notE, SeqRead.zEven, truthy_eq] at h
  simp only [Bool.not_eq_false', decide_eq_true_eq] at h
  simp only [Expr.eval, BinOp.eval, hx] at h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx', Nat.and_one_is_mod] at this
  simpa using this

theorem eq_of {rs : Regs} {x y : Nat} (h : truthy ((notE (zCmp .r8 .rax)).eval rs) = false)
    (hx : rs .r8 = BitVec.ofNat 64 x) (hy : rs .rax = BitVec.ofNat 64 y) (hx' : x < 2 ^ 32)
    (hy' : y < 2 ^ 32) : x = y := by
  rw [truthy_notE] at h
  simp only [zCmp, r32, truthy_eq, Bool.not_eq_false', decide_eq_true_eq] at h
  have := congrArg BitVec.toNat h
  rw [toNat_mask32, toNat_mask32] at this
  simp only [Expr.eval, hx, hy, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega : x < 2 ^ 64), Nat.mod_eq_of_lt (by omega : y < 2 ^ 64),
    Nat.mod_eq_of_lt hx', Nat.mod_eq_of_lt hy'] at this
  exact this

section Steps

variable {s : Nat} {ws : List (Nat × Nat)} {outs : List Nat} {init : Heap} {t o : Nat}
  {Q : Regs → W → Prop}

theorem ldQ_k (X : Ctx s ws outs init t) {rs : Regs} (P : W → Prop) (hP : Stab (gp s ws) t P)
    (hb : ∀ g, P g → base s o t rs g)
    (k : ∀ g v, A1 s o t ws (rs.set .rax (BitVec.ofNat 64 v)) g →
      TSafe (own s outs) init (gp s ws) t Q .skip (rs.set .rax (BitVec.ofNat 64 v)) g)
    {g : W} (hg : P g) : TSafe (own s outs) init (gp s ws) t Q SeqRead.ldQ rs g := by
  obtain ⟨hrdi, _, _⟩ := hb g hg
  refine rd_step X (Or.inl rfl) hrdi P hP (fun g v hp hf hc => k g v ?_) hg
  obtain ⟨h1, h2, h3⟩ := hb g hp
  rw [Nat.add_zero, (cells_wlog X.h0 X.h4 X.h8 _).1, Option.some.injEq] at hc
  exact ⟨⟨by simp [set_apply, h1], by simp [set_apply, h2], h3⟩, g.fl 0, Nat.le_refl _, hf,
    by simp [set_apply, hc]⟩

theorem ldA_k (X : Ctx s ws outs init t) {rs : Regs}
    (k : ∀ g v, A2 s o t ws (rs.set .rcx (BitVec.ofNat 64 v)) g →
      TSafe (own s outs) init (gp s ws) t Q .skip (rs.set .rcx (BitVec.ofNat 64 v)) g)
    {g : W} (hg : A1 s o t ws rs g) : TSafe (own s outs) init (gp s ws) t Q SeqRead.ldA rs g := by
  refine rd_step X (Or.inr (Or.inl rfl)) hg.1.1 _ (A1_stab rs) (fun g v hp hf hc => k g v ?_) hg
  obtain ⟨⟨h1, h2, h3⟩, fQ, hq1, hq2, hq3⟩ := hp
  rw [(cells_wlog X.h0 X.h4 X.h8 _).2.1, Option.some.injEq] at hc
  exact ⟨⟨by simp [set_apply, h1], by simp [set_apply, h2], h3⟩, fQ, g.fl 0, hq1, Nat.le_refl _,
    hf, by simp [set_apply, hq3], by simp [set_apply, hc]⟩

theorem ldB_k (X : Ctx s ws outs init t) {rs : Regs}
    (k : ∀ g v, A3 s o t ws (rs.set .rdx (BitVec.ofNat 64 v)) g →
      TSafe (own s outs) init (gp s ws) t Q .skip (rs.set .rdx (BitVec.ofNat 64 v)) g)
    {g : W} (hg : A2 s o t ws rs g) : TSafe (own s outs) init (gp s ws) t Q SeqRead.ldB rs g := by
  refine rd_step X (Or.inr (Or.inr rfl)) hg.1.1 _ (A2_stab rs) (fun g v hp hf hc => k g v ?_) hg
  obtain ⟨⟨h1, h2, h3⟩, fQ, fA, hq1, hq2, hq3, hq4, hq5⟩ := hp
  rw [(cells_wlog X.h0 X.h4 X.h8 _).2.2, Option.some.injEq] at hc
  exact ⟨⟨by simp [set_apply, h1], by simp [set_apply, h2], h3⟩, fQ, fA, g.fl 0, hq1, hq2,
    Nat.le_refl _, hf, by simp [set_apply, hq4], by simp [set_apply, hq5], by simp [set_apply, hc]⟩

theorem ldR_k (X : Ctx s ws outs init t) {rs : Regs}
    (he : truthy ((notE SeqRead.zEven).eval rs) = false)
    (k : ∀ g v, A4 s o t ws (rs.set .r8 (BitVec.ofNat 64 v)) g →
      TSafe (own s outs) init (gp s ws) t Q .skip (rs.set .r8 (BitVec.ofNat 64 v)) g)
    {g : W} (hg : A3 s o t ws rs g) : TSafe (own s outs) init (gp s ws) t Q SeqRead.ldR rs g := by
  refine rd_step X (Or.inl rfl) hg.1.1 _ (A3_stab rs) (fun g v hp hf hc => k g v ?_) hg
  obtain ⟨⟨h1, h2, h3⟩, fQ, fA, fB, hq1, hq2, hq3, hq4, hq5, hq6, hq7⟩ := hp
  rw [Nat.add_zero, (cells_wlog X.h0 X.h4 X.h8 _).1, Option.some.injEq] at hc
  have hev := even_of he hq5 (by have := seqAt_lt X.hlen (show fQ ≤ 4 * ws.length by omega); omega)
  exact ⟨⟨by simp [set_apply, h1], by simp [set_apply, h2], h3⟩, fQ, fA, fB, g.fl 0, hq1, hq2,
    hq3, Nat.le_refl _, hf, hev, by simp [set_apply, hq5], by simp [set_apply, hq6],
    by simp [set_apply, hq7], by simp [set_apply, hc]⟩

/-- `ldQ; ldA; ldB` from any state with the base registers, ending in `A3`. -/
theorem snap_k (X : Ctx s ws outs init t) {rs : Regs} (P : W → Prop) (hP : Stab (gp s ws) t P)
    (hb : ∀ g, P g → base s o t rs g)
    (k : ∀ rs g, A3 s o t ws rs g → TSafe (own s outs) init (gp s ws) t Q .skip rs g)
    {g : W} (hg : P g) :
    TSafe (own s outs) init (gp s ws) t Q (.seq SeqRead.ldQ (.seq SeqRead.ldA SeqRead.ldB)) rs g :=
  tsafe_seq (ldQ_k X P hP hb (fun _ _ h => tsafe_skip_of (tsafe_seq (ldA_k X (fun _ _ h =>
    tsafe_skip_of (ldB_k X (fun _ _ h => k _ _ h) h)) h))) hg)

/-- The inner loop `while (seq odd) snap`, from `A3`, exits in `A3` with `seq` even. -/
theorem inner_k (X : Ctx s ws outs init t) (L : Nat)
    (k : ∀ rs g, A3 s o t ws rs g → truthy ((notE SeqRead.zEven).eval rs) = false →
      TSafe (own s outs) init (gp s ws) t Q .skip rs g)
    {rs : Regs} {g : W} (hg : A3 s o t ws rs g) :
    TSafe (own s outs) init (gp s ws) t Q (.loop L (notE SeqRead.zEven)
      (.seq SeqRead.ldQ (.seq SeqRead.ldA SeqRead.ldB))) rs g :=
  tsafe_loop (A3 s o t ws) A3_stab (fun rs _ h _ => snap_k X _ (A3_stab rs) (fun _ h => h.1)
    (fun _ _ h => tsafe_skip (fun rs => A3_stab rs) h) h) k L rs g hg

end Steps

theorem seqRead_body (L : Nat) : SeqRead.cert.body L = Tv.chain [SeqRead.ldQ, SeqRead.ldA,
    SeqRead.ldB, .loop L (notE SeqRead.zEven) (.seq SeqRead.ldQ (.seq SeqRead.ldA SeqRead.ldB)),
    SeqRead.ldR, .loop L (notE (zCmp .r8 .rax))
      (.seq (.seq SeqRead.ldQ (.seq SeqRead.ldA SeqRead.ldB))
        (.seq (.loop L (notE SeqRead.zEven) (.seq SeqRead.ldQ (.seq SeqRead.ldA SeqRead.ldB)))
          SeqRead.ldR)),
    SeqRead.stA, SeqRead.stB] := rfl

section ReaderMain

variable {s : Nat} {ws : List (Nat × Nat)} {outs : List Nat} {init : Heap} {t o : Nat}

theorem gp_push_ne {g : W} (ht : t ≠ 0) (e : Nat × Nat) (h : gp s ws g) : gp s ws (g.push t e) := by
  obtain ⟨f, hf, hl⟩ := h
  exact ⟨f, hf, by rw [push_log_ne _ (Ne.symm ht), hl]⟩

/-- The output stores, from a consistent snapshot. -/
theorem out_k (X : Ctx s ws outs init t) (hown : own s outs t o ∧ own s outs t (o + 4))
    (ho : o + 8 ≤ 2 ^ 64) (hpost : outs.getD (t - 1) 0 = o) {rs : Regs} {p : Nat × Nat}
    (hp : p ∈ (0, 0) :: ws) (hrsi : rs .rsi = BitVec.ofNat 64 o)
    (hrcx : rs .rcx = BitVec.ofNat 64 p.1) (hrdx : rs .rdx = BitVec.ofNat 64 p.2)
    {g : W} (hg : g.log t = []) :
    TSafe (own s outs) init (gp s ws) t (post ws outs t)
      (.seq SeqRead.stA (.seq SeqRead.stB .skip)) rs g := by
  have hp' : p.1 < 2 ^ 32 ∧ p.2 < 2 ^ 32 := by
    rcases List.mem_cons.mp hp with rfl | hp
    · decide
    · exact X.hws p hp
  refine tsafe_seq_store _ (stab_log _) ?_ ?_ hg
  · rw [eval_at 0 hrsi (by omega), Nat.add_zero]; exact hown.1
  intro g1 hg1 hgp _
  rw [eval_at 0 hrsi (by omega), Nat.add_zero, eval_reg_mod hrcx hp'.1]
  refine ⟨gp_push_ne X.ht _ hgp, ?_⟩
  refine tsafe_seq_store _ (stab_log _) ?_ ?_ (push_log g1 t _)
  · rw [eval_at 4 hrsi (by omega)]; exact hown.2
  intro g hg hgp _
  rw [eval_at 4 hrsi (by omega), eval_reg_mod hrdx hp'.2]
  refine ⟨gp_push_ne X.ht _ hgp, tsafe_skip (fun _ _ _ h r _ => ?_) (Or.inr ⟨p, hp, ?_⟩)⟩
  · rcases h with h | ⟨p, hp, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, r.1.trans h⟩
  · rw [push_log, hg, hg1, hpost]; rfl

/-- **A reader is safe**, for every loop bound, and ends having logged a written pair. -/
theorem reader_safe (X : Ctx s ws outs init t) (hown : own s outs t o ∧ own s outs t (o + 4))
    (ho : o + 8 ≤ 2 ^ 64) (hpost : outs.getD (t - 1) 0 = o) (L : Nat) {rs : Regs} {g : W}
    (hb : base s o t rs g) :
    TSafe (own s outs) init (gp s ws) t (post ws outs t) (SeqRead.cert.body L) rs g := by
  rw [seqRead_body]
  simp only [Tv.chain]
  -- the final check and the output stores
  have fin : ∀ rs g, A4 s o t ws rs g → truthy ((notE (zCmp .r8 .rax)).eval rs) = false →
      TSafe (own s outs) init (gp s ws) t (post ws outs t)
        (.seq SeqRead.stA (.seq SeqRead.stB .skip)) rs g := by
    intro rs g h hf
    obtain ⟨⟨_, hrsi, hl⟩, fQ, fA, fB, fR, h1, h2, h3, _, h5, hev, hax, hcx, hdx, hr8⟩ := h
    have he := eq_of hf hr8 hax (seqAt_lt X.hlen h5) (seqAt_lt X.hlen (by omega))
    obtain ⟨p, hp, hpa, hpb⟩ := snap_ok h1 h2 h3 h5 hev he.symm
    exact out_k X hown ho hpost hp hrsi (hpa ▸ hcx) (hpb ▸ hdx) hl
  -- the outer loop
  have outer : ∀ rs g, A4 s o t ws rs g →
      TSafe (own s outs) init (gp s ws) t (post ws outs t)
        (.seq (.loop L (notE (zCmp .r8 .rax))
          (.seq (.seq SeqRead.ldQ (.seq SeqRead.ldA SeqRead.ldB))
            (.seq (.loop L (notE SeqRead.zEven) (.seq SeqRead.ldQ (.seq SeqRead.ldA SeqRead.ldB)))
              SeqRead.ldR)))
          (.seq SeqRead.stA (.seq SeqRead.stB .skip))) rs g := by
    intro rs g h
    refine tsafe_seq (tsafe_loop (A4 s o t ws) A4_stab (fun rs g h _ => ?_)
      (fun rs g h hf => tsafe_skip_of (fin rs g h hf)) L rs g h)
    exact tsafe_seq (snap_k X _ (A4_stab rs) (fun _ h => h.1) (fun _ _ h => tsafe_skip_of
      (tsafe_seq (inner_k X L (fun _ _ h he => tsafe_skip_of (ldR_k X he (fun _ _ h =>
        tsafe_skip (fun rs => A4_stab rs) h) h)) h))) h)
  -- the prefix: snapshot, inner loop, second read of `seq`
  refine tsafe_seq (ldQ_k X (base s o t rs) (base_stab rs) (fun _ h => h) (fun _ _ h =>
    tsafe_skip_of (tsafe_seq (ldA_k X (fun _ _ h => tsafe_skip_of (tsafe_seq (ldB_k X
      (fun _ _ h => tsafe_skip_of (tsafe_seq (inner_k X L (fun _ _ h he => tsafe_skip_of
        (tsafe_seq (ldR_k X he (fun _ _ h => tsafe_skip_of (outer _ _ h)) h))) h))) h))) h))) hb)

end ReaderMain

/-! ## `Task.seqlockTso` -/

theorem getD_eq {l : List Nat} {j : Nat} (h : j < l.length) : l.getD j 0 = l[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem own_unique {s : Nat} {outs : List Nat}
    (hout : ∀ o ∈ outs, o + 8 ≤ 2 ^ 64 ∧ (o + 8 ≤ s ∨ s + 12 ≤ o))
    (hpw : outs.Pairwise (fun o o' => o + 8 ≤ o' ∨ o' + 8 ≤ o)) :
    ∀ t u c, own s outs t c → own s outs u c → t = u := by
  rintro t u c (⟨rfl, hc⟩ | ⟨j, hj, rfl, hc⟩) (⟨rfl, hc'⟩ | ⟨j', hj', rfl, hc'⟩)
  · rfl
  · have := (hout _ (List.mem_of_getElem? (List.getElem?_eq_getElem hj'))).2
    rw [getD_eq hj'] at hc'; omega
  · have := (hout _ (List.mem_of_getElem? (List.getElem?_eq_getElem hj))).2
    rw [getD_eq hj] at hc; omega
  · rw [getD_eq hj] at hc; rw [getD_eq hj'] at hc'
    rcases Nat.lt_trichotomy j j' with h | h | h
    · have := List.pairwise_iff_getElem.mp hpw j j' hj hj' h; omega
    · rw [h]
    · have := List.pairwise_iff_getElem.mp hpw j' j hj' hj h; omega

/-- **`Task.seqlockTso` is proved.** -/
theorem seqlockTso_holds : Task.seqlockTso := by
  intro L s ws outs hs hws hlen hout hpw writer N C0 C hr hd hfin o ho
  have hU := own_unique hout hpw
  have hmem : ∀ a, a = s ∨ a = s + 4 ∨ a = s + 8 → C0.mem a = some 0 := by
    intro a ha
    refine heapOf_find ?_ (fun p hp _ => ?_) _
    · rcases ha with rfl | rfl | rfl <;> simp
    · simp only [List.mem_append, List.mem_cons, List.mem_flatMap] at hp
      rcases hp with ((rfl | rfl | rfl | h) | ⟨o, _, rfl | rfl | h⟩) <;> simp_all
  have X : ∀ t, t ≠ 0 → Ctx s ws outs C0.mem t := fun t ht =>
    ⟨hU, hs, hlen, hws, hmem s (Or.inl rfl), hmem _ (Or.inr (Or.inl rfl)),
      hmem _ (Or.inr (Or.inr rfl)), ht⟩
  have hT0 : ∀ t < N, TSafe (own s outs) C0.mem (gp s ws) t (post ws outs t) (C0.ts t).1
      (C0.ts t).2 W.zero := by
    intro t ht
    by_cases h0 : t = 0
    · subst h0
      exact writer_safe hU hs hws hlen (hmem s (Or.inl rfl)) (hmem _ (Or.inr (Or.inl rfl)))
        (hmem _ (Or.inr (Or.inr rfl))) L _ (by simp [C0, regs])
    · have hts : C0.ts t = (SeqRead.cert.body L,
          regs [(.rdi, s), (.rsi, outs.getD (t - 1) 0)]) := by simp [C0, h0, ht]
      rw [hts]
      have hj : t - 1 < outs.length := by simp [N] at ht; omega
      have hmo := (hout _ (List.mem_of_getElem? (List.getElem?_eq_getElem hj)))
      rw [← getD_eq hj] at hmo
      refine reader_safe (X t h0) ⟨Or.inr ⟨t - 1, hj, by omega, Or.inl rfl⟩,
        Or.inr ⟨t - 1, hj, by omega, Or.inr rfl⟩⟩ hmo.1 rfl L ⟨?_, ?_, rfl⟩
      · simp [regs]
      · simp [regs]
  obtain ⟨g, _, hpost, hcell, _⟩ := sw_final (Own := own s outs) (Gp := gp s ws)
    (Q := post ws outs) (N := N) (C0 := C0) hU (fun g t h _ _ => gp_flush s ws g t h)
    ⟨0, Nat.zero_le _, rfl⟩ hT0 hr hd hfin
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ho
  have ht : j + 1 < N := by simp [N]; omega
  rcases hpost (j + 1) ht with h | ⟨p, hp, hl⟩
  · omega
  have hj' : outs.getD (j + 1 - 1) 0 = outs[j] := by rw [Nat.add_sub_cancel, getD_eq hj]
  rw [hj'] at hl
  refine ⟨p, hp, ?_, ?_⟩
  · rw [hcell (j + 1) _ (Or.inr ⟨j, hj, rfl, Or.inl (getD_eq hj).symm⟩), hl]
    simp [cellAfter, lastV]
  · rw [hcell (j + 1) _ (Or.inr ⟨j, hj, rfl, Or.inr (by rw [getD_eq hj])⟩), hl]
    simp [cellAfter, lastV]

end Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Seq
