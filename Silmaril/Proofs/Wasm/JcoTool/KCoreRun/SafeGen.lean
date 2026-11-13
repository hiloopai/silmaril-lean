module

public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Safe

/-!
# The callback of a generated module is safe: the walk through `callbackD`

`genD_cbSafe`: for read sizes `N ≤ 256` and globals within the buffer bounds of `KDrop.okD`, the
callback `KDrop.callbackD k N` is `CbSafe`: every `dexec` run with the runtime's parameters is a
`bexec CBL` run. The walk uses the rules of `KCoreRun.Safe`:

* **Memory-free code** (`sok`: no load, store, copy, loop, nor `stream.read`/`stream.write`;
  indices in range, divisors nonzero constants) is safe from any state (`sok_safe`); this covers
  `WTW`, `WTRD`, `CL`, `DEAD`, the end of `WR`, `onWriteD`.
* **The kernel's code** `cS` keeps the buffer bounds `GB` (`BLEN ≤ CAP`, `OLEN ≤ CAP`): the guard
  of `emitS`/`pushS` gives the store's address below `MSZ`, the guard of `emitBufS` (under `GB`, no
  wrap-around) the copy's (`cS_safe`).
* **`feedLoop`**: the loop invariant `LI ≤ LN ≤ 256` (and `GB`) keeps the load `IN + LI` below
  `MSZ` (`feedLoop_safe`).
* **The reads**: `stream.read` of `N ≤ 256` bytes at `IN` lies in memory, and its count is at most
  `N` (`dcallBI` checks it); an event of the input delivers at most `256` items (`KDrop.wfD`).
* **The write** of `WR`: `OOFF ≤ OLEN ≤ CAP` puts its buffer at `OUT + OOFF .. OUT + OLEN`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun

open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.Component.Streams.Kernel (KExp KStmt KM)

/-! ## Memory-free code -/

/-- A divisor `cev` accepts whatever the state: a nonzero constant (other operators: any). -/
def divOk : Bin → E → Bool
  | .divu, .c n => decide (n % M32 ≠ 0)
  | .remu, .c n => decide (n % M32 ≠ 0)
  | .divu, _ => false
  | .remu, _ => false
  | _, _ => true

/-- Expressions `cev nl` computes in every state: no load, indices in range, constant divisors. -/
def eok (nl : Nat) : E → Bool
  | .c _ => true
  | .l i => decide (i < nl)
  | .g i => decide (i < NG)
  | .bin o a b => eok nl a && eok nl b && divOk o b
  | .eqz a => eok nl a
  | .ld8 _ => false

theorem divOk_ok {o : Bin} {b : E} (h : divOk o b = true) (s : St) :
    (o = .divu ∨ o = .remu) → b.eval s ≠ 0 := by
  cases o <;> cases b <;> simp_all [divOk, E.eval]

theorem eok_ok {nl : Nat} (s : DSt) : ∀ {e : E}, eok nl e = true → EOk nl s e
  | .c _, _ => trivial
  | .l i, h => (of_decide_eq_true h : i < nl)
  | .g i, h => (of_decide_eq_true h : i < NG)
  | .bin o a b, h => by
    have h' : (eok nl a = true ∧ eok nl b = true) ∧ divOk o b = true := by
      simpa only [eok, Bool.and_eq_true] using h
    exact ⟨eok_ok s h'.1.1, eok_ok s h'.1.2, divOk_ok h'.2 s.down⟩
  | .eqz a, h => eok_ok (e := a) s h
  | .ld8 _, h => by cases h

/-- Statements safe in every state: memory-free, the drops the only calls. -/
def sok (nl : Nat) : S → Bool
  | .nop => true
  | .unreachable => true
  | .lset i e => decide (i < nl) && eok nl e
  | .gset i e => decide (i < NG) && eok nl e
  | .seq a b => sok nl a && sok nl b
  | .ite c t e => eok nl c && sok nl t && sok nl e
  | .block b => sok nl b
  | .br k => decide (k < M32)
  | .brIf k c => decide (k < M32) && eok nl c
  | .ret e => eok nl e
  | .call .dropR args [] => args.all (eok nl)
  | .call .dropW args [] => args.all (eok nl)
  | _ => false

/-- The trivial postcondition. -/
abbrev TT : Out → DSt → Prop := fun _ _ => True

theorem args_ok {nl : Nat} {s : DSt} {args : List E} (h : args.all (eok nl) = true) :
    ∀ a ∈ args, EOk nl s a := fun a ha => eok_ok s (List.all_eq_true.mp h a ha)

theorem sok_safe {nl : Nat} : ∀ {S : S}, sok nl S = true → Safe nl (fun _ => True) S TT
  | .nop, _ => safe_nop fun _ _ => trivial
  | .unreachable, _ => safe_unreachable
  | .lset _ _, h => by
    have h' : _ ∧ _ := Bool.and_eq_true _ _ ▸ h
    exact safe_lset (of_decide_eq_true h'.1) fun s _ => ⟨eok_ok s h'.2, trivial⟩
  | .gset _ _, h => by
    have h' : _ ∧ _ := Bool.and_eq_true _ _ ▸ h
    exact safe_gset (of_decide_eq_true h'.1) fun s _ => ⟨eok_ok s h'.2, trivial⟩
  | .seq a b, h => by
    have h' : sok nl a = true ∧ sok nl b = true := by simpa only [sok, Bool.and_eq_true] using h
    exact safe_seq (sok_safe h'.1) (sok_safe h'.2).conseq_pre fun _ _ _ _ => trivial
  | .ite c t e, h => by
    have h' : (eok nl c = true ∧ sok nl t = true) ∧ sok nl e = true := by
      simpa only [sok, Bool.and_eq_true] using h
    exact safe_ite (fun s _ => eok_ok s h'.1.1) (sok_safe h'.1.2).conseq_pre
      (sok_safe h'.2).conseq_pre fun _ _ _ => trivial
  | .block b, h => safe_block (sok_safe (S := b) h) fun _ _ _ => trivial
  | .br _, h => safe_br (of_decide_eq_true h) fun _ _ => trivial
  | .brIf _ c, h => by
    have h' : _ ∧ eok nl c = true := Bool.and_eq_true _ _ ▸ h
    exact safe_brIf (of_decide_eq_true h'.1) fun s _ => ⟨eok_ok s h'.2, fun _ => trivial, fun _ => trivial⟩
  | .ret _, h => safe_ret fun s _ => ⟨eok_ok s h, trivial⟩
  | .call .dropR args [], h =>
    safe_call fun _ _ => ⟨args_ok h, fun _ hr => bcall_dropR hr, fun _ _ _ => trivial⟩
  | .call .dropW args [], h =>
    safe_call fun _ _ => ⟨args_ok h, fun _ hr => bcall_dropW hr, fun _ _ _ => trivial⟩
  | .st8 _ _, h => by cases h
  | .mcopy _ _ _, h => by cases h
  | .loop _, h => by cases h
  | .call .streamNew _ _, h => by cases h
  | .call .streamRead _ _, h => by cases h
  | .call .streamWrite _ _, h => by cases h
  | .call .wsNew _ _, h => by cases h
  | .call .join _ _, h => by cases h
  | .call .taskReturn _ _, h => by cases h
  | .call .dropR _ (_ :: _), h => by cases h
  | .call .dropW _ (_ :: _), h => by cases h

/-- Memory-free code is safe from any precondition. -/
theorem sok_safe' {nl : Nat} {P : DSt → Prop} {S : S} (h : sok nl S = true) : Safe nl P S TT :=
  (sok_safe h).conseq (fun _ _ => trivial) fun _ _ _ => trivial

/-! ## Arithmetic of the generated code -/

/-- The buffer bounds the kernel's code keeps. -/
def GB (g : Nat → Nat) : Prop := g BLEN ≤ CAP ∧ g OLEN ≤ CAP

theorem eval_c (s : St) (n : Nat) : (E.c n).eval s = n % M32 := rfl

theorem upd_ne {f : Nat → Nat} {k v j : Nat} (h : j ≠ k) : upd f k v j = f j := ite_eq_right h
theorem upd_eq {f : Nat → Nat} {k v : Nat} : upd f k v k = v := ite_eq_left rfl

/-- A built-in call ends normally and keeps the globals. -/
theorem bcall_g {nl : Nat} {b : BI} {as dst : List Nat} {s : DSt} {o : Out} {s' : DSt}
    (h : bcall nl b as dst s = some (o, s')) : o = .norm ∧ s'.g = s.g := by
  unfold bcall at h
  split at h
  · split at h
    · split at h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h).symm
        exact ⟨rfl, rfl⟩
      · cases h
    · cases h
  · cases h

/-- A `stream.read`'s result local: `BLOCKED`, or a count of at most `n` items. -/
theorem dcall_read {h p n d : Nat} {s : DSt} {o : Out} {s' : DSt}
    (hc : dcallBI .streamRead [h, p, n] [d] s = some (o, s')) :
    s'.l d = Silmaril.Wasm.Component.Async.blocked ∨ s'.l d / 16 ≤ n := by
  simp only [dcallBI] at hc
  split at hc
  · split at hc
    · rename_i code xs _ hk
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hc).symm
      exact .inr (by simp only [upd_eq]; omega)
    · cases hc
  · split at hc
    · rename_i r _ hr
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hc).symm
      exact .inl (by simp only [upd_eq, hr])
    · cases hc
  · cases hc

/-! ## Sequences and guards -/

theorem m32_eq : M32 = 4294967296 := rfl

theorem safe_seqN {nl : Nat} {P A : DSt → Prop} {Q : Out → DSt → Prop} {a b : S}
    (ha : Safe nl P a (fun o s => o = .norm ∧ A s)) (hb : Safe nl A b Q) : Safe nl P (.seq a b) Q :=
  safe_seq ha (hb.conseq (fun _ h => h.2) fun _ _ h => h) fun _ _ hn h => absurd h.1 hn

/-- A guard `if c then unreachable`: past it, `c` is `0`. -/
theorem safe_guard {nl : Nat} {P : DSt → Prop} {c : E} (hc : eok nl c = true) :
    Safe nl P (.ite c .unreachable .nop) (fun o s => o = .norm ∧ P s ∧ c.eval s.down = 0) :=
  safe_ite (R := fun o s => o = .norm ∧ P s ∧ c.eval s.down = 0) (fun s _ => eok_ok s hc)
    safe_unreachable (safe_nop fun _ h => ⟨rfl, h⟩) fun o _ h => ⟨by rw [h.1]; rfl, h.2⟩

theorem geu_zero {a b : E} {s : St} (h : (E.bin .geu a b).eval s = 0) : a.eval s < b.eval s := by
  by_contra hc
  have h1 : (E.bin .geu a b).eval s = 1 := ite_eq_left (Nat.le_of_not_lt hc)
  omega

theorem geu_ne {a b : E} {s : St} (h : (E.bin .geu a b).eval s ≠ 0) : b.eval s ≤ a.eval s := by
  by_contra hc
  exact h (ite_eq_right hc)

theorem ltu_zero {a b : E} {s : St} (h : (E.bin .ltu a b).eval s = 0) : b.eval s ≤ a.eval s := by
  by_contra hc
  have h1 : (E.bin .ltu a b).eval s = 1 := ite_eq_left (Nat.lt_of_not_le hc)
  omega

theorem isE_ne {a : E} {v : Nat} {s : St} (h : (isE a v).eval s ≠ 0) : a.eval s = v % M32 := by
  by_contra hc
  exact h (ite_eq_right hc)

theorem isE_zero {a : E} {v : Nat} {s : St} (h : (isE a v).eval s = 0) : a.eval s ≠ v % M32 := by
  intro hc
  have h1 : (isE a v).eval s = 1 := ite_eq_left hc
  omega

theorem andE_ne {a b : E} {s : St} (h : (andE a b).eval s ≠ 0) : a.eval s ≠ 0 ∧ b.eval s ≠ 0 := by
  simp only [andE, E.eval, Bin.eval] at h
  by_cases ha : a.eval s = 0 <;> by_cases hb : b.eval s = 0 <;> simp_all [m32_eq]

/-! ## The kernel's code keeps the buffer bounds -/

/-- The buffer bounds, and a condition on the locals. -/
def KP (L : (Nat → Nat) → Prop) (s : DSt) : Prop := GB s.g ∧ L s.l

/-- Ends normally with `KP L`. -/
def KQ (L : (Nat → Nat) → Prop) (o : Out) (s : DSt) : Prop := o = .norm ∧ KP L s

theorem gb_set {g : Nat → Nat} (h : GB g) (i : Nat) {v : Nat} (hv : (i = BLEN ∨ i = OLEN) → v ≤ CAP) :
    GB (upd g i v) := by
  constructor
  · show (if BLEN = i then v else g BLEN) ≤ CAP
    by_cases hi : BLEN = i
    · rw [ite_eq_left hi]; exact hv (.inl hi.symm)
    · rw [ite_eq_right hi]; exact h.1
  · show (if OLEN = i then v else g OLEN) ≤ CAP
    by_cases hi : OLEN = i
    · rw [ite_eq_left hi]; exact hv (.inr hi.symm)
    · rw [ite_eq_right hi]; exact h.2

theorem gb_upd {g : Nat → Nat} (h : GB g) {i v : Nat} (hi : i ≠ BLEN ∧ i ≠ OLEN) : GB (upd g i v) :=
  gb_set h i fun h' => (h'.elim hi.1 hi.2).elim

theorem cE_ok (ke : KExp) : eok CBL (cE ke) = true := by
  induction ke <;> simp_all [cE, eok, divOk, CBL, LB, NG, GST, BLEN]

theorem emit_safe {L : (Nat → Nat) → Prop} {v : E} (hv : eok CBL v = true) :
    Safe CBL (KP L) (emitS v) (KQ L) := by
  have hst : Safe CBL (fun s => KP L s ∧ (E.bin .geu (.g OLEN) (.c CAP)).eval s.down = 0)
      (.st8 (.bin .add (.c OUT) (.g OLEN)) v) (fun o s => o = .norm ∧ KP L s ∧ s.g OLEN < CAP) :=
    safe_st8 fun s h => by
      have hl : s.g OLEN < CAP := geu_zero h.2
      refine ⟨eok_ok s (by decide), eok_ok s hv, ?_, rfl, h.1, hl⟩
      show (OUT % M32 + s.g OLEN) % M32 < MSZ
      simp only [OUT, CAP, MSZ, m32_eq] at hl ⊢
      omega
  have hgs : Safe CBL (fun s => KP L s ∧ s.g OLEN < CAP) (.gset OLEN (.bin .add (.g OLEN) (.c 1)))
      (KQ L) :=
    safe_gset (by decide) fun s h => by
      refine ⟨eok_ok s (by decide), rfl, gb_set h.1.1 OLEN fun _ => ?_, h.1.2⟩
      show (s.g OLEN + 1 % M32) % M32 ≤ CAP
      have hl := h.2
      simp only [CAP, m32_eq] at hl ⊢
      omega
  exact safe_seqN (safe_guard (by decide)) (safe_seqN hst hgs)

theorem push_safe {L : (Nat → Nat) → Prop} {v : E} (hv : eok CBL v = true) :
    Safe CBL (KP L) (pushS v) (KQ L) := by
  have hst : Safe CBL (fun s => KP L s ∧ (E.bin .geu (.g BLEN) (.c CAP)).eval s.down = 0)
      (.st8 (.bin .add (.c KBUF) (.g BLEN)) v) (fun o s => o = .norm ∧ KP L s ∧ s.g BLEN < CAP) :=
    safe_st8 fun s h => by
      have hl : s.g BLEN < CAP := geu_zero h.2
      refine ⟨eok_ok s (by decide), eok_ok s hv, ?_, rfl, h.1, hl⟩
      show (KBUF % M32 + s.g BLEN) % M32 < MSZ
      simp only [KBUF, CAP, MSZ, m32_eq] at hl ⊢
      omega
  have hgs : Safe CBL (fun s => KP L s ∧ s.g BLEN < CAP) (.gset BLEN (.bin .add (.g BLEN) (.c 1)))
      (KQ L) :=
    safe_gset (by decide) fun s h => by
      refine ⟨eok_ok s (by decide), rfl, gb_set h.1.1 BLEN fun _ => ?_, h.1.2⟩
      show (s.g BLEN + 1 % M32) % M32 ≤ CAP
      have hl := h.2
      simp only [CAP, m32_eq] at hl ⊢
      omega
  exact safe_seqN (safe_guard (by decide)) (safe_seqN hst hgs)

/-- Past the guard of `emitBufS`, under the bounds, the buffer fits (no wrap-around). -/
theorem emitBuf_fit {L : (Nat → Nat) → Prop} {s : DSt} (hp : KP L s)
    (h : (E.bin .ltu (.c CAP) (.bin .add (.g OLEN) (.g BLEN))).eval s.down = 0) :
    s.g OLEN + s.g BLEN ≤ CAP := by
  have h' : (s.g OLEN + s.g BLEN) % 4294967296 ≤ 32768 % 4294967296 := ltu_zero h
  have hb : s.g BLEN ≤ 32768 ∧ s.g OLEN ≤ 32768 := hp.1
  show s.g OLEN + s.g BLEN ≤ 32768
  omega

theorem emitBuf_safe {L : (Nat → Nat) → Prop} : Safe CBL (KP L) emitBufS (KQ L) := by
  have hmc : Safe CBL (fun s => KP L s ∧
        (E.bin .ltu (.c CAP) (.bin .add (.g OLEN) (.g BLEN))).eval s.down = 0)
      (.mcopy (.bin .add (.c OUT) (.g OLEN)) (.c KBUF) (.g BLEN))
      (fun o s => o = .norm ∧ KP L s ∧ s.g OLEN + s.g BLEN ≤ CAP) :=
    safe_mcopy fun s h => by
      have hf : s.g OLEN + s.g BLEN ≤ 32768 := emitBuf_fit h.1 h.2
      refine ⟨eok_ok s (by decide), eok_ok s (by decide), eok_ok s (by decide), ?_, rfl, h.1, hf⟩
      show (4096 % 4294967296 + s.g OLEN) % 4294967296 ≤ 65536 % 4294967296 ∧
        65536 % 4294967296 + s.g BLEN ≤ 131072
      omega
  have hgs : Safe CBL (fun s => KP L s ∧ s.g OLEN + s.g BLEN ≤ CAP)
      (.gset OLEN (.bin .add (.g OLEN) (.g BLEN))) (KQ L) :=
    safe_gset (by decide) fun s h => by
      refine ⟨eok_ok s (by decide), rfl, gb_set h.1.1 OLEN fun _ => ?_, h.1.2⟩
      have hl : s.g OLEN + s.g BLEN ≤ 32768 := h.2
      show (s.g OLEN + s.g BLEN) % 4294967296 ≤ 32768
      omega
  exact safe_seqN (safe_guard (by decide)) (safe_seqN hmc hgs)

/-- **The kernel's compiled statements are safe and keep the buffer bounds.** -/
theorem cS_safe (L : (Nat → Nat) → Prop) : ∀ st : KStmt, Safe CBL (KP L) (cS st) (KQ L)
  | .skip => safe_nop fun _ h => ⟨rfl, h⟩
  | .seq p q => safe_seqN (cS_safe L p) (cS_safe L q)
  | .emit e => emit_safe (cE_ok e)
  | .set e => safe_gset (by decide) fun s h =>
      ⟨eok_ok s (cE_ok e), rfl, gb_upd h.1 (i := GST) (by decide), h.2⟩
  | .push e => push_safe (cE_ok e)
  | .emitBuf => emitBuf_safe
  | .clear => safe_gset (by decide) fun s h =>
      ⟨trivial, rfl, gb_set h.1 BLEN fun _ => Nat.zero_le _, h.2⟩
  | .ite c p q => safe_ite (fun s _ => eok_ok s (cE_ok c)) ((cS_safe L p).conseq (fun _ h => h.1)
      fun _ _ h => h) ((cS_safe L q).conseq (fun _ h => h.1) fun _ _ h => h)
      fun o _ h => ⟨by rw [h.1]; rfl, h.2⟩

/-! ## `feedLoop` -/

/-- The loop invariant of `feedLoop`: the bounds, `LI ≤ LN ≤ 256`. -/
def FL (s : DSt) : Prop := GB s.g ∧ s.l LI ≤ s.l LN ∧ s.l LN ≤ 256

/-- Inside the body, past the test: `LI < LN ≤ 256`. -/
def LIn (l : Nat → Nat) : Prop := l LI < l LN ∧ l LN ≤ 256

/-- How the body ends: `br 0` with the invariant, or out of the loop. -/
def FX : Out → DSt → Prop := LoopQ FL (fun o _ => o = .br 0)

/-- Normally with `A`, or by an exit of the body. -/
def Ex (A : DSt → Prop) (o : Out) (s : DSt) : Prop := (o = .norm ∧ A s) ∨ (o ≠ .norm ∧ FX o s)

theorem ex_norm {A : DSt → Prop} {s : DSt} (h : Ex A .norm s) : A s :=
  h.elim (·.2) fun h => absurd rfl h.1

theorem safe_seqX {P A B : DSt → Prop} {a b : S} (ha : Safe CBL P a (Ex A))
    (hb : Safe CBL A b (Ex B)) : Safe CBL P (.seq a b) (Ex B) :=
  safe_seq ha (hb.conseq (fun _ h => ex_norm h) fun _ _ h => h)
    fun _ _ hn h => .inr ⟨hn, (h.resolve_left fun h' => hn h'.1).2⟩

theorem exit1 (s : DSt) : Ex (fun _ => False) (.br 1) s ∧ ∀ A, Ex A (.br 1) s :=
  ⟨.inr ⟨fun h => (by cases h), (rfl : Out.br 0 = Out.br 0)⟩,
    fun _ => .inr ⟨fun h => (by cases h), (rfl : Out.br 0 = Out.br 0)⟩⟩

/-- Setting a local other than `LI` and `LN` keeps `KP LIn`. -/
theorem lin_upd {s : DSt} (h : KP LIn s) {i v : Nat} (hi : i ≠ LI ∧ i ≠ LN) :
    KP LIn { s with l := upd s.l i v } :=
  ⟨h.1, by
    show upd s.l i v LI < upd s.l i v LN ∧ upd s.l i v LN ≤ 256
    rw [upd_ne (Ne.symm hi.1), upd_ne (Ne.symm hi.2)]
    exact h.2⟩

theorem feed_test : Safe CBL FL (.brIf 1 (.bin .geu (.l LI) (.l LN))) (Ex (KP LIn)) :=
  safe_brIf (by decide) fun s h =>
    ⟨eok_ok s (by decide), fun _ => (exit1 s).2 _, fun hc => .inl ⟨rfl, h.1, geu_zero hc, h.2.2⟩⟩

theorem feed_done (k : KM) : Safe CBL (KP LIn) (.brIf 1 (cE k.done)) (Ex (KP LIn)) :=
  safe_brIf (by decide) fun s h => ⟨eok_ok s (cE_ok _), fun _ => (exit1 s).2 _, fun _ => .inl ⟨rfl, h⟩⟩

theorem feed_load : Safe CBL (KP LIn) (.lset LB (.ld8 (.bin .add (.c IN) (.l LI)))) (Ex (KP LIn)) :=
  safe_lset (by decide) fun s h => by
    refine ⟨⟨eok_ok s (by decide), ?_⟩, .inl ⟨rfl, lin_upd h (by decide)⟩⟩
    show (IN % M32 + s.l LI) % M32 < MSZ
    have hl := h.2
    simp only [LIn, IN, MSZ, m32_eq] at hl ⊢
    omega

theorem feed_next : Safe CBL (KP LIn) (.lset LI (.bin .add (.l LI) (.c 1))) (Ex FL) :=
  safe_lset (by decide) fun s h => by
    refine ⟨eok_ok s (by decide), .inl ⟨rfl, h.1, ?_⟩⟩
    show upd s.l LI ((s.l LI + 1 % M32) % M32) LI ≤ upd s.l LI ((s.l LI + 1 % M32) % M32) LN ∧
      upd s.l LI ((s.l LI + 1 % M32) % M32) LN ≤ 256
    rw [upd_eq, upd_ne (show LN ≠ LI by decide)]
    have hl := h.2
    simp only [LIn, m32_eq] at hl ⊢
    omega

/-- **`feedLoop` is safe** from its invariant. -/
theorem feedLoop_safe (k : KM) : Safe CBL FL (feedLoop k) (fun o _ => o = .norm) := by
  have hbody : Safe CBL FL (seqs [.brIf 1 (.bin .geu (.l LI) (.l LN)), .lset LB (.c 0),
      .brIf 1 (cE k.done), .lset LB (.ld8 (.bin .add (.c IN) (.l LI))), cS k.step,
      .lset LI (.bin .add (.l LI) (.c 1)), .br 0]) (Ex fun _ => False) :=
    safe_seqX feed_test <| safe_seqX
      (safe_lset (by decide) fun s h => ⟨trivial, .inl ⟨rfl, lin_upd h (by decide)⟩⟩) <|
      safe_seqX (feed_done k) <| safe_seqX feed_load <|
      safe_seqX ((cS_safe LIn k.step).conseq (fun _ h => h) fun _ _ h => .inl h) <|
      safe_seqX feed_next (safe_br (by decide) fun _ h => .inr ⟨fun h => (by cases h), h⟩)
  have hloop : Safe CBL FL (.loop (seqs [.brIf 1 (.bin .geu (.l LI) (.l LN)), .lset LB (.c 0),
      .brIf 1 (cE k.done), .lset LB (.ld8 (.bin .add (.c IN) (.l LI))), cS k.step,
      .lset LI (.bin .add (.l LI) (.c 1)), .br 0])) (fun o _ => o = .br 0) :=
    safe_loop (hbody.conseq (fun _ h => h) fun _ _ h => h.elim (fun h => h.2.elim) (·.2))
  exact safe_block hloop fun o _ h => by rw [h]; rfl

/-! ## Reads, the flush, and the cases of the callback -/

theorem safe_gsetN {nl : Nat} {A : DSt → Prop} {i : Nat} {e : E} (hi : i < NG) (he : eok nl e = true)
    (hA : ∀ s v, A s → A { s with g := upd s.g i v }) :
    Safe nl A (.gset i e) (fun o s => o = .norm ∧ A s) :=
  safe_gset hi fun s h => ⟨eok_ok s he, rfl, hA s _ h⟩

theorem safe_lsetN {nl : Nat} {A : DSt → Prop} {i : Nat} {e : E} (hi : i < nl) (he : eok nl e = true)
    (hA : ∀ s v, A s → A { s with l := upd s.l i v }) :
    Safe nl A (.lset i e) (fun o s => o = .norm ∧ A s) :=
  safe_lset hi fun s h => ⟨eok_ok s he, rfl, hA s _ h⟩

/-- **After a read** whose packed result is local `i` with a count of at most `256`. -/
theorem onReadD_safe (k : KM) {i : Nat} (hi : i < CBL) :
    Safe CBL (fun s => GB s.g ∧ s.l i / 16 ≤ 256) (onReadD k (.l i)) TT := by
  have h₁ : Safe CBL (fun s => GB s.g ∧ s.l i / 16 ≤ 256) (.gset NXT (nxtOf (.l i)))
      (fun o s => o = .norm ∧ GB s.g ∧ s.l i / 16 ≤ 256) :=
    safe_gsetN (by decide) (by simp [nxtOf, eok, divOk, hi, m32_eq])
      fun _ _ h => ⟨gb_upd h.1 (i := NXT) (by decide), h.2⟩
  have h₂ : Safe CBL (fun s => GB s.g ∧ s.l i / 16 ≤ 256) (.lset LN (.bin .divu (.l i) (.c 16)))
      (fun o s => o = .norm ∧ GB s.g ∧ s.l LN ≤ 256) :=
    safe_lset (by decide) fun s h => by
      refine ⟨eok_ok s (by simp [eok, divOk, hi, m32_eq]), rfl, h.1, ?_⟩
      show upd s.l LN (s.l i / (16 % M32)) LN ≤ 256
      rw [upd_eq]
      exact h.2
  have h₃ : Safe CBL (fun s => GB s.g ∧ s.l LN ≤ 256) (.lset LI (.c 0)) (fun o s => o = .norm ∧ FL s) :=
    safe_lset (by decide) fun s h => by
      refine ⟨trivial, rfl, h.1, ?_⟩
      show upd s.l LI (0 % M32) LI ≤ upd s.l LI (0 % M32) LN ∧ upd s.l LI (0 % M32) LN ≤ 256
      rw [upd_eq, upd_ne (show LN ≠ LI by decide)]
      exact ⟨Nat.zero_le _, h.2⟩
  have h₄ : Safe CBL FL (.seq (feedLoop k) (.gset PC (.c pWR))) TT :=
    safe_seqN ((feedLoop_safe k).conseq (fun _ h => h) fun _ _ h => ⟨h, trivial⟩)
      (sok_safe' (by decide))
  exact safe_seqN h₁ (safe_seqN h₂ (safe_seqN h₃ h₄))

/-- A drop: it ends normally and keeps the globals. -/
theorem drop_safe {A : DSt → Prop} {b : BI} {args : List E} (hb : b = .dropR ∨ b = .dropW)
    (ha : args.all (eok CBL) = true) (hA : ∀ s s', s'.g = s.g → A s → A s') :
    Safe CBL A (.call b args []) (fun o s => o = .norm ∧ A s) := by
  have hbc : ∀ s r, dcallBI b (args.map (·.eval s.down)) [] s = some r →
      bcall CBL b (args.map (·.eval s.down)) [] s = some r := by
    rcases hb with rfl | rfl
    · exact fun _ _ hr => bcall_dropR hr
    · exact fun _ _ hr => bcall_dropW hr
  exact safe_call fun s h => ⟨args_ok ha, hbc s, fun _ _ hc =>
    ⟨(bcall_g (hbc s _ hc)).1, hA s _ (bcall_g (hbc s _ hc)).2 h⟩⟩

theorem gb_of {s s' : DSt} (he : s'.g = s.g) (h : GB s.g) : GB s'.g := he ▸ h

/-- **The flush** from the buffer bounds. -/
theorem flushOut_safe (k : KM) : Safe CBL (fun s => GB s.g) (flushOut k) TT := by
  have hc : Safe CBL (KP fun _ => True) (seqs [cS k.flush, .gset NXT (.c 0), .gset PC (.c pWR)]) TT :=
    safe_seqN ((cS_safe _ k.flush).conseq (fun _ h => h) fun _ _ h => ⟨h.1, h.2⟩)
      (sok_safe' (by decide))
  refine safe_seqN (safe_gsetN (by decide) (by decide) fun _ _ h => gb_upd h (i := OOFF) (by decide)) ?_
  refine safe_seqN (A := fun s => GB s.g) (safe_gset (by decide) fun s h =>
    ⟨trivial, rfl, gb_set h OLEN fun _ => Nat.zero_le _⟩) ?_
  exact safe_seqN (safe_lsetN (by decide) (by decide) fun _ _ h => h) (hc.conseq (fun _ h => ⟨h, trivial⟩)
    fun _ _ h => h)

/-- `seq a yield_`, `a` safe. -/
theorem safe_yield {P : DSt → Prop} {a : S} (ha : Safe CBL P a TT) : Safe CBL P (.seq a yield_) TT :=
  safe_seq ha (sok_safe' (by decide)) fun _ _ _ _ => trivial

theorem blocked_mod : Silmaril.Wasm.Component.Async.blocked % M32 = Silmaril.Wasm.Component.Async.blocked :=
  Nat.mod_eq_of_lt blocked_lt

/-- **`RD`**: the read of `N ≤ 256` bytes at `IN`, then `onReadD`. -/
theorem dRD_safe (k : KM) {N : Nat} (hN : N ≤ 256) : Safe CBL (fun s => GB s.g) (dRD k N) TT := by
  have hrd : Safe CBL (fun s => GB s.g) (.call .streamRead [.g INSR, .c IN, .c N] [LR])
      (fun o s => o = .norm ∧ GB s.g ∧ (s.l LR = Silmaril.Wasm.Component.Async.blocked ∨ s.l LR / 16 ≤ N)) :=
    safe_call fun s h => by
      have hm : memOK MSZ .streamRead [s.g INSR, IN % M32, N % M32] = true := by
        show decide (IN % M32 + N % M32 ≤ MSZ) = true
        exact decide_eq_true (by simp only [IN, MSZ, m32_eq]; omega)
      have hN' : N % M32 = N := Nat.mod_eq_of_lt (by simp only [m32_eq]; omega)
      refine ⟨args_ok rfl, fun _ hr => bcall_read hm (by decide) hr, fun _ _ hc => ?_⟩
      have hb := bcall_g (bcall_read (nl := CBL) hm (by decide) hc)
      have h₂ := dcall_read hc
      exact ⟨hb.1, gb_of hb.2 h, by simpa only [eval_c, hN'] using h₂⟩
  have hcase : Safe CBL (fun s => GB s.g ∧
      (s.l LR = Silmaril.Wasm.Component.Async.blocked ∨ s.l LR / 16 ≤ N))
      (.ite (isE (.l LR) Silmaril.Wasm.Component.Async.blocked) (.seq (.gset PC (.c pWTR)) (.ret waitCode))
        (.seq (onReadD k (.l LR)) yield_)) TT :=
    safe_ite (fun s _ => eok_ok s (by decide)) (sok_safe' (by decide))
      ((safe_yield (onReadD_safe k (by decide))).conseq (fun s h => ⟨h.1.1, by
        have hne : s.l LR ≠ Silmaril.Wasm.Component.Async.blocked := blocked_mod ▸ isE_zero h.2
        have := h.1.2.resolve_left hne
        omega⟩) fun _ _ h => h) fun _ _ _ => trivial
  have hdone : Safe CBL (fun s => GB s.g) (seqs [.call .dropR [.g INSR] [], flushOut k, yield_]) TT :=
    safe_seqN (drop_safe (.inl rfl) (by decide) fun _ _ he h => gb_of he h)
      (safe_yield (flushOut_safe k))
  refine safe_seqN (safe_lsetN (by decide) (by decide) fun _ _ h => h) ?_
  exact safe_ite (fun s _ => eok_ok s (cE_ok _)) (hdone.conseq (fun _ h => h.1) fun _ _ h => h)
    ((safe_seqN hrd hcase).conseq (fun _ h => h.1) fun _ _ h => h) fun _ _ _ => trivial

/-- **`EOI`**. -/
theorem dEOI_safe (k : KM) : Safe CBL (fun s => GB s.g) (dEOI k) TT :=
  safe_seqN (drop_safe (.inl rfl) (by decide) fun _ _ he h => gb_of he h)
    (safe_yield (flushOut_safe k))

/-- The read event's count: at most `256` when the event is a read (`l 0 = 2`). -/
def EvOK (l : Nat → Nat) : Prop := l 0 = 2 → l 2 / 16 ≤ 256

/-- **`WTR`**: the read's event, then `onReadD`. -/
theorem dWTR_safe (k : KM) : Safe CBL (fun s => GB s.g ∧ EvOK s.l) (dWTR k) TT :=
  safe_ite (fun s _ => eok_ok s (by decide))
    ((safe_yield (onReadD_safe k (by decide))).conseq (fun s h => ⟨h.1.1, h.1.2 (by
      have h0 : s.l 0 = 2 % M32 := isE_ne (andE_ne h.2).1
      exact h0.trans (Nat.mod_eq_of_lt (by decide)))⟩) fun _ _ h => h)
    (sok_safe' (by decide)) fun _ _ _ => trivial

/-- The buffer bounds of the runtime (`KDrop.okD`). -/
def BOK (g : Nat → Nat) : Prop := g BLEN ≤ CAP ∧ g OLEN ≤ CAP ∧ g OOFF ≤ g OLEN

/-- **`WR`**: the write of `OUT + OOFF .. OUT + OLEN`. -/
theorem dWR_safe : Safe CBL (fun s => BOK s.g) dWR TT := by
  have hwr : Safe CBL (fun s => BOK s.g) (.call .streamWrite [.g OUTSW, .bin .add (.c OUT) (.g OOFF),
      .bin .sub (.g OLEN) (.g OOFF)] [LR]) TT :=
    safe_call fun s h => by
      have hb : s.g OOFF ≤ s.g OLEN ∧ s.g OLEN ≤ 32768 := ⟨h.2.2, h.2.1⟩
      have hm : memOK MSZ .streamWrite [s.g OUTSW, (OUT % M32 + s.g OOFF) % M32,
          (s.g OLEN + (M32 - s.g OOFF % M32)) % M32] = true := by
        show decide ((OUT % M32 + s.g OOFF) % M32 + (s.g OLEN + (M32 - s.g OOFF % M32)) % M32 ≤ MSZ) = true
        exact decide_eq_true (by simp only [OUT, MSZ, m32_eq]; omega)
      exact ⟨args_ok rfl, fun _ hr => bcall_write hm (by decide) hr, fun _ _ _ => trivial⟩
  exact safe_ite (fun s _ => eok_ok s (by decide)) (sok_safe' (by decide))
    (safe_seq (hwr.conseq (fun _ h => h.1) fun _ _ h => h) (sok_safe' (by decide))
      fun _ _ _ _ => trivial) fun _ _ _ => trivial

/-- A case of the dispatch, `TT` after it. -/
theorem safe_case {P : DSt → Prop} {c : E} {t e : S} (hc : eok CBL c = true) (ht : Safe CBL P t TT)
    (he : Safe CBL P e TT) : Safe CBL P (.ite c t e) TT :=
  safe_ite (fun s _ => eok_ok s hc) (ht.conseq (fun _ h => h.1) fun _ _ h => h)
    (he.conseq (fun _ h => h.1) fun _ _ h => h) fun _ _ _ => trivial

/-- The precondition of the callback: the buffer bounds and the runtime's parameters. -/
def CbPre (s : DSt) : Prop := BOK s.g ∧ EvOK s.l

/-- **The callback of `genD k N` is safe** from `CbPre`, for `N ≤ 256`. -/
theorem callbackD_safe (k : KM) {N : Nat} (hN : N ≤ 256) : Safe CBL CbPre (callbackD k N) TT := by
  have gb : ∀ s, CbPre s → GB s.g := fun _ h => ⟨h.1.1, h.1.2.1⟩
  refine safe_case (by decide) ((dWTR_safe k).conseq (fun s h => ⟨gb s h, h.2⟩) fun _ _ h => h) ?_
  refine safe_case (by decide) (sok_safe' (by decide)) ?_
  refine safe_case (by decide) ((dRD_safe k hN).conseq gb fun _ _ h => h) ?_
  refine safe_case (by decide) ((dEOI_safe k).conseq gb fun _ _ h => h) ?_
  refine safe_case (by decide) (dWR_safe.conseq (fun _ h => h.1) fun _ _ h => h) ?_
  refine safe_case (by decide) (sok_safe' (by decide)) ?_
  refine safe_case (by decide) (sok_safe' (by decide)) ?_
  exact safe_case (by decide) (sok_safe' (by decide)) safe_unreachable

/-- The runtime's parameters give `EvOK`: no event, or a well-formed one (a read event delivers
at most `256` items). -/
theorem wf_items {e : Silmaril.Wasm.Component.Async.Event} (h : wellFormed e = true) :
    e.items.length ≤ 256 := by
  have h₁ : ((decide (e.payload < M32) = true ∧ decide (e.index < M32) = true) ∧
      decide (e.items.length ≤ 256) = true) ∧
      (e.code != .streamRead || e.payload % 16 != 0 ||
        decide (e.payload / 16 = e.items.length)) = true := by
    simpa only [wellFormed, Bool.and_eq_true] using h
  exact of_decide_eq_true h₁.1.2

theorem params_evOK {ps : List Nat} (h : ParamsOK ps) : EvOK (locals ps) := by
  rcases h with rfl | ⟨e, hwf, rfl⟩
  · intro h0
    cases h0
  · show e.code.toNat = 2 → e.payload / 16 ≤ 256
    intro h0
    have hc : e.code = .streamRead := by
      revert h0
      cases e.code <;> simp [Silmaril.Wasm.Component.Async.EventCode.toNat]
    have hw : wellFormed e = true ∧
        (e.code != .streamRead || decide (e.payload / 16 = e.items.length)) = true := by
      simpa only [wfD, Bool.and_eq_true] using hwf
    have hl : e.items.length ≤ 256 := wf_items hw.1
    have hp : e.payload / 16 = e.items.length := by
      simpa only [hc, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] using hw.2
    show e.payload / 16 ≤ 256
    rw [hp]
    exact hl

/-- **`Task.genD_safe`, proved**: the callback of `genD k N`, `N ≤ 256`, is `CbSafe` at every
globals within the buffer bounds. -/
theorem genD_cbSafe (k : KM) {N : Nat} (hN : N ≤ 256) (g : Nat → Nat) (hg : BOK g) :
    CbSafe (genD k N) g := by
  intro ps m st rp r hps hd
  obtain ⟨o, s'⟩ := r
  exact (callbackD_safe k hN FUEL ⟨g, m, locals ps, st, rp⟩ o s' ⟨hg, params_evOK hps⟩ hd).1

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun
