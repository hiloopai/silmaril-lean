module

public import Silmaril.Wasm.JcoTool.KCore.Defs

/-!
# The compiled kernel statements run as the kernel says

(Restyled to the Isar conventions of `docs/projects/wasm-components.md` when moved out of `Silmaril/Raw`; the statements are
restated in `Silmaril.Wasm.JcoTool.KCore.Thms`.)

* Memory: `slice` and its updates by `upd`, `writeBytes` and `mcopy`.
* `KRep g m ks out`: the globals and memory hold the kernel state `ks` (state global, buffer
  at `KBUF`) and the output so far `out` (at `OUT`), both within `CAP` bytes.
* `cE_eval`: a compiled expression evaluates as the kernel expression.
* `cS_sound`: when the compiled statement finishes, it finishes normally, the bounds checks
  passed (`fitsS`), the new globals and memory hold `c.exec b ks` (state, and outputs appended),
  and nothing else changed (`Frame`); `cS_complete`: when the bounds checks pass, it finishes.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCore

open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.Component.Streams.Kernel (KExp KStmt KM KSt)

/-! ## Memory -/

theorem upd_apply (f : Nat → Nat) (k v j : Nat) : upd f k v j = if j = k then v else f j := rfl

theorem slice_zero (m : Nat → Nat) (a : Nat) : slice m a 0 = [] := rfl

theorem slice_succ (m : Nat → Nat) (a n : Nat) : slice m a (n + 1) = slice m a n ++ [m (a + n)] := by
  simp [slice, List.range_succ]

theorem slice_length (m : Nat → Nat) (a n : Nat) : (slice m a n).length = n := by
  simp [slice]

theorem slice_congr {m m' : Nat → Nat} {a n : Nat} (h : ∀ i, i < n → m (a + i) = m' (a + i)) :
    slice m a n = slice m' a n := by
  unfold slice
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem slice_add (m : Nat → Nat) (a n k : Nat) : slice m a (n + k) = slice m a n ++ slice m (a + n) k := by
  induction k with
  | zero => simp [slice_zero]
  | succ k ih => rw [← Nat.add_assoc, slice_succ, ih, slice_succ, List.append_assoc, Nat.add_assoc]

theorem slice_drop (m : Nat → Nat) (a n j : Nat) : (slice m a n).drop j = slice m (a + j) (n - j) := by
  unfold slice
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [Nat.add_assoc]

theorem getElem_slice (m : Nat → Nat) (a n i : Nat) (h : i < (slice m a n).length) :
    (slice m a n)[i] = m (a + i) := by
  simp [slice]

theorem slice_writeBytes (m : Nat → Nat) (a : Nat) (bs : List Nat) :
    slice (writeBytes m a bs) a bs.length = bs := by
  apply List.ext_getElem
  · simp [slice_length]
  · intro i h₁ h₂
    have hi : i < bs.length := by simpa [slice_length] using h₁
    simp [slice, writeBytes, hi, List.getD_eq_getElem?_getD]

/-- Writing outside `[a, a + n)` leaves `slice m a n` alone. -/
theorem slice_upd_out {m : Nat → Nat} {a n x v : Nat} (h : x < a ∨ a + n ≤ x) :
    slice (upd m x v) a n = slice m a n := by
  apply slice_congr
  intro i hi
  have hx : a + i ≠ x := by omega
  simp [upd_apply, hx]

theorem slice_writeBytes_out {m : Nat → Nat} {a n p : Nat} {bs : List Nat}
    (h : p + bs.length ≤ a ∨ a + n ≤ p) : slice (writeBytes m p bs) a n = slice m a n := by
  apply slice_congr
  intro i hi
  have hx : ¬ (p ≤ a + i ∧ a + i < p + bs.length) := by omega
  simp [writeBytes, hx]

theorem slice_mcopy_out {m : Nat → Nat} {a n d s k : Nat} (h : d + k ≤ a ∨ a + n ≤ d) :
    slice (mcopy m d s k) a n = slice m a n := by
  apply slice_congr
  intro i hi
  have hx : ¬ (d ≤ a + i ∧ a + i < d + k) := by omega
  simp [mcopy, hx]

theorem slice_mcopy_in (m : Nat → Nat) (d s k : Nat) : slice (mcopy m d s k) d k = slice m s k := by
  unfold slice
  apply List.map_congr_left
  intro i hi
  have hx : d ≤ d + i ∧ d + i < d + k := by
    have : i < k := List.mem_range.mp hi
    omega
  simp [mcopy, hx]

/-! ## Constants below `2 ^ 32` -/

@[simp] theorem IN_mod : IN % M32 = IN := by decide
@[simp] theorem OUT_mod : OUT % M32 = OUT := by decide
@[simp] theorem KBUF_mod : KBUF % M32 = KBUF := by decide
@[simp] theorem CAP_mod : CAP % M32 = CAP := by decide
@[simp] theorem one_mod_M32 : 1 % M32 = 1 := by decide
@[simp] theorem two_mod_M32 : 2 % M32 = 2 := by decide
@[simp] theorem three_mod_M32 : 3 % M32 = 3 := by decide
@[simp] theorem four_mod_M32 : 4 % M32 = 4 := by decide
@[simp] theorem sixteen_mod_M32 : 16 % M32 = 16 := by decide
@[simp] theorem blocked_mod_M32 : Silmaril.Wasm.Component.Async.blocked % M32 = Silmaril.Wasm.Component.Async.blocked := by decide
@[simp] theorem pc_mod {n : Nat} (h : n ≤ 7) : n % M32 = n := Nat.mod_eq_of_lt (by simp [M32]; omega)

/-! ## Representation of the kernel state and the output -/

/-- The globals `g` and memory `m` hold the kernel state `ks` and the output so far `out`. -/
structure KRep (g m : Nat → Nat) (ks : KSt) (out : List Nat) : Prop where
  st : g GST = ks.st
  blen : g BLEN = ks.buf.length
  bufs : slice m KBUF ks.buf.length = ks.buf
  olen : g OLEN = out.length
  outs : slice m OUT out.length = out
  bcap : ks.buf.length ≤ CAP
  ocap : out.length ≤ CAP

/-- What a compiled kernel statement leaves alone. -/
structure Frame (s s' : St) : Prop where
  l : s'.l = s.l
  st : s'.st = s.st
  rp : s'.rp = s.rp
  task : s'.task = s.task
  g : ∀ i, i ≠ GST → i ≠ BLEN → i ≠ OLEN → s'.g i = s.g i
  m : ∀ a, a < OUT → s'.m a = s.m a

theorem Frame.refl (s : St) : Frame s s := ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩

theorem Frame.trans {s₁ s₂ s₃ : St} (h₁ : Frame s₁ s₂) (h₂ : Frame s₂ s₃) : Frame s₁ s₃ :=
  ⟨h₂.l.trans h₁.l, h₂.st.trans h₁.st, h₂.rp.trans h₁.rp, h₂.task.trans h₁.task,
    fun i a b c => (h₂.g i a b c).trans (h₁.g i a b c),
    fun a ha => (h₂.m a ha).trans (h₁.m a ha)⟩

/-! ## Expressions -/

theorem cE_eval {s : St} {ks : KSt} (hst : s.g GST = ks.st) (hbl : s.g BLEN = ks.buf.length)
    (e : KExp) : (cE e).eval s = e.eval ks (s.l LB) := by
  induction e with
  | x => rfl
  | st => exact hst
  | blen => exact hbl
  | lit n => simp [cE, E.eval, KExp.eval, M32, Silmaril.Wasm.Component.Streams.Kernel.M32]
  | add a b iha ihb => simp [cE, E.eval, KExp.eval, Bin.eval, iha, ihb, M32,
      Silmaril.Wasm.Component.Streams.Kernel.M32]
  | sub a b iha ihb => simp [cE, E.eval, KExp.eval, Bin.eval, iha, ihb, M32,
      Silmaril.Wasm.Component.Streams.Kernel.M32]
  | eq a b iha ihb => simp [cE, E.eval, KExp.eval, Bin.eval, iha, ihb]
  | ltu a b iha ihb => simp [cE, E.eval, KExp.eval, Bin.eval, iha, ihb]
  | eqz a iha => simp [cE, E.eval, KExp.eval, iha]

/-! ## Statements: generic lemmas -/

theorem exec_seq {a b : S} {f : Nat} {s : St} :
    exec (.seq a b) f s = match exec a f s with
      | some (.norm, s') => exec b f s'
      | r => r := rfl

theorem exec_seq_norm {a b : S} {f : Nat} {s s₁ : St} (h : exec a f s = some (.norm, s₁)) :
    exec (.seq a b) f s = exec b f s₁ := by
  rw [exec_seq, h]

/-- A sequence that finished normally: both parts did. -/
theorem exec_seq_inv {a b : S} {f : Nat} {s s' : St} (h : exec (.seq a b) f s = some (.norm, s')) :
    ∃ s₁, exec a f s = some (.norm, s₁) ∧ exec b f s₁ = some (.norm, s') := by
  cases h₁ : exec a f s with
  | none => rw [exec_seq, h₁] at h; cases h
  | some p =>
    obtain ⟨o, s₁⟩ := p
    cases o with
    | norm => exact ⟨s₁, rfl, by rwa [exec_seq, h₁] at h⟩
    | br k => rw [exec_seq, h₁] at h; cases h
    | ret v => rw [exec_seq, h₁] at h; cases h

theorem lab_norm (s : St) : lab (some (.norm, s)) = some (.norm, s) := rfl

theorem lab_ret (v : Nat) (s : St) : lab (some (.ret v, s)) = some (.ret v, s) := rfl

theorem lab_none : lab none = none := rfl

/-- `lab x` finished normally: `x` finished normally, or branched to the label. -/
theorem lab_inv {x : Option (Out × St)} {s : St} (h : lab x = some (.norm, s)) :
    x = some (.norm, s) ∨ x = some (.br 0, s) := by
  unfold lab at h
  split at h
  · cases h
    exact .inr rfl
  · cases h
  · rename_i r h₁ h₂
    exact .inl h

theorem exec_ite {c : E} {t e : S} {f : Nat} {s : St} :
    exec (.ite c t e) f s = lab (if c.eval s ≠ 0 then exec t f s else exec e f s) := rfl

theorem exec_lset (i : Nat) (e : E) (f : Nat) (s : St) :
    exec (.lset i e) f s = some (.norm, { s with l := upd s.l i (e.eval s) }) := rfl

theorem exec_gset (i : Nat) (e : E) (f : Nat) (s : St) :
    exec (.gset i e) f s = some (.norm, { s with g := upd s.g i (e.eval s) }) := rfl

/-! ## The compiled kernel statements -/

/-- Small values of `i32` arithmetic. -/
theorem add_small {a b : Nat} (h : a + b < M32) : Bin.eval .add a b = a + b := by
  simp [Bin.eval, Nat.mod_eq_of_lt h]

theorem M32_eq : M32 = 4294967296 := rfl

theorem c_eval (n : Nat) (s : St) (h : n < M32) : (E.c n).eval s = n := by
  simp [E.eval, Nat.mod_eq_of_lt h]




theorem emitS_exec (v : E) (f : Nat) (s : St) (n : Nat) (hn : s.g OLEN = n) (hc : n ≤ CAP) :
    exec (emitS v) f s = if n < CAP then
      some (.norm, { s with m := upd s.m (OUT + n) (v.eval s % 256), g := upd s.g OLEN (n + 1) })
    else none := by
  simp only [CAP, OUT] at hc ⊢
  by_cases h : n < 32768
  · have h0 : ¬ 32768 ≤ n := by omega
    have h1 : (4096 + n) % 4294967296 = 4096 + n := Nat.mod_eq_of_lt (by omega)
    have h2 : (n + 1) % 4294967296 = n + 1 := Nat.mod_eq_of_lt (by omega)
    simp [emitS, seqs, exec, lab, E.eval, Bin.eval, hn, h, h0, h1, h2, CAP, OUT, M32]
  · have h0 : 32768 ≤ n := by omega
    simp [emitS, seqs, exec, lab, E.eval, Bin.eval, hn, h, h0, CAP, M32]

theorem pushS_exec (v : E) (f : Nat) (s : St) (n : Nat) (hn : s.g BLEN = n) (hc : n ≤ CAP) :
    exec (pushS v) f s = if n < CAP then
      some (.norm, { s with m := upd s.m (KBUF + n) (v.eval s % 256), g := upd s.g BLEN (n + 1) })
    else none := by
  simp only [CAP, KBUF] at hc ⊢
  by_cases h : n < 32768
  · have h0 : ¬ 32768 ≤ n := by omega
    have h1 : (65536 + n) % 4294967296 = 65536 + n := Nat.mod_eq_of_lt (by omega)
    have h2 : (n + 1) % 4294967296 = n + 1 := Nat.mod_eq_of_lt (by omega)
    simp [pushS, seqs, exec, lab, E.eval, Bin.eval, hn, h, h0, h1, h2, CAP, KBUF, M32]
  · have h0 : 32768 ≤ n := by omega
    simp [pushS, seqs, exec, lab, E.eval, Bin.eval, hn, h, h0, CAP, M32]

theorem emitBufS_exec (f : Nat) (s : St) (n b : Nat) (hn : s.g OLEN = n) (hb : s.g BLEN = b)
    (hc : n ≤ CAP) (hbc : b ≤ CAP) :
    exec emitBufS f s = if n + b ≤ CAP then
      some (.norm, { s with m := mcopy s.m (OUT + n) KBUF b, g := upd s.g OLEN (n + b) })
    else none := by
  simp only [CAP, OUT, KBUF] at hc hbc ⊢
  have h3 : (n + b) % 4294967296 = n + b := Nat.mod_eq_of_lt (by omega)
  by_cases h : n + b ≤ 32768
  · have h0 : ¬ 32768 < n + b := by omega
    have h1 : (4096 + n) % 4294967296 = 4096 + n := Nat.mod_eq_of_lt (by omega)
    have h4 : b % 4294967296 = b := Nat.mod_eq_of_lt (by omega)
    simp [emitBufS, seqs, exec, lab, E.eval, Bin.eval, hn, hb, h, h0, h1, h3, CAP, OUT, KBUF, M32]
  · have h0 : 32768 < n + b := by omega
    simp [emitBufS, seqs, exec, lab, E.eval, Bin.eval, hn, hb, h, h0, h3, CAP, M32]

/-! ## Soundness of the compiled statements -/

theorem lab_of_norm {x : Option (Out × St)} {s₁ : St} (h : x = some (.norm, s₁)) : lab x = x := by
  rw [h]
  rfl

theorem KRep.emit {g m : Nat → Nat} {ks : KSt} {out : List Nat} (hR : KRep g m ks out)
    (hc : out.length < CAP) (v : Nat) :
    KRep (upd g OLEN (out.length + 1)) (upd m (OUT + out.length) (v % 256)) ks (out ++ [v % 256]) where
  st := by simpa [upd_apply, GST, OLEN] using hR.st
  blen := by simpa [upd_apply, BLEN, OLEN] using hR.blen
  bufs := by
    have hx : OUT + out.length < KBUF := by simp [OUT, KBUF, CAP] at *; omega
    rw [slice_upd_out (.inl hx)]
    exact hR.bufs
  olen := by simp [upd_apply]
  outs := by
    have e : (out ++ [v % 256]).length = out.length + 1 := by simp
    rw [e, slice_succ, slice_upd_out (.inr (Nat.le_refl _)), hR.outs]
    simp [upd_apply]
  bcap := hR.bcap
  ocap := by simp; omega

theorem KRep.push {g m : Nat → Nat} {ks : KSt} {out : List Nat} (hR : KRep g m ks out)
    (hc : ks.buf.length < CAP) (v : Nat) :
    KRep (upd g BLEN (ks.buf.length + 1)) (upd m (KBUF + ks.buf.length) (v % 256))
      { ks with buf := ks.buf ++ [v % 256] } out where
  st := by simpa [upd_apply, GST, BLEN] using hR.st
  blen := by simp [upd_apply]
  bufs := by
    have e : (ks.buf ++ [v % 256]).length = ks.buf.length + 1 := by simp
    show slice _ KBUF (ks.buf ++ [v % 256]).length = ks.buf ++ [v % 256]
    rw [e, slice_succ, slice_upd_out (.inr (Nat.le_refl _)), hR.bufs]
    simp [upd_apply]
  olen := by simpa [upd_apply, BLEN, OLEN] using hR.olen
  outs := by
    have hx : OUT + out.length < KBUF + ks.buf.length := by
      have := hR.ocap
      simp [OUT, KBUF, CAP] at *; omega
    rw [slice_upd_out (.inr (Nat.le_of_lt hx))]
    exact hR.outs
  bcap := by simp; omega
  ocap := hR.ocap

theorem KRep.emitBuf {g m : Nat → Nat} {ks : KSt} {out : List Nat} (hR : KRep g m ks out)
    (hc : out.length + ks.buf.length ≤ CAP) :
    KRep (upd g OLEN (out.length + ks.buf.length)) (mcopy m (OUT + out.length) KBUF ks.buf.length)
      ks (out ++ ks.buf) where
  st := by simpa [upd_apply, GST, OLEN] using hR.st
  blen := by simpa [upd_apply, BLEN, OLEN] using hR.blen
  bufs := by
    have hx : OUT + out.length + ks.buf.length ≤ KBUF := by simp [OUT, KBUF, CAP] at *; omega
    rw [slice_mcopy_out (.inl hx)]
    exact hR.bufs
  olen := by simp [upd_apply]
  outs := by
    have e : (out ++ ks.buf).length = out.length + ks.buf.length := by simp
    rw [e, slice_add, slice_mcopy_out (.inr (Nat.le_refl _)), slice_mcopy_in, hR.outs, hR.bufs]
  bcap := hR.bcap
  ocap := by simpa using hc

theorem KRep.set {g m : Nat → Nat} {ks : KSt} {out : List Nat} (hR : KRep g m ks out) (v : Nat) :
    KRep (upd g GST v) m { ks with st := v } out where
  st := by simp [upd_apply]
  blen := by simpa [upd_apply, GST, BLEN] using hR.blen
  bufs := hR.bufs
  olen := by simpa [upd_apply, GST, OLEN] using hR.olen
  outs := hR.outs
  bcap := hR.bcap
  ocap := hR.ocap

theorem KRep.clear {g m : Nat → Nat} {ks : KSt} {out : List Nat} (hR : KRep g m ks out) :
    KRep (upd g BLEN 0) m { ks with buf := [] } out where
  st := by simpa [upd_apply, GST, BLEN] using hR.st
  blen := by simp [upd_apply]
  bufs := rfl
  olen := by simpa [upd_apply, BLEN, OLEN] using hR.olen
  outs := hR.outs
  bcap := by simp
  ocap := hR.ocap


theorem frame_g (s : St) (i v : Nat) (hi : i = GST ∨ i = BLEN ∨ i = OLEN) :
    Frame s { s with g := upd s.g i v } :=
  ⟨rfl, rfl, rfl, rfl, fun j h₁ h₂ h₃ => by
    have hj : j ≠ i := by rcases hi with rfl | rfl | rfl <;> assumption
    simp [upd_apply, hj], fun _ _ => rfl⟩

theorem frame_gm (s : St) (i v : Nat) (m : Nat → Nat) (hi : i = GST ∨ i = BLEN ∨ i = OLEN)
    (hm : ∀ a, a < OUT → m a = s.m a) : Frame s { s with m := m, g := upd s.g i v } :=
  ⟨rfl, rfl, rfl, rfl, fun j h₁ h₂ h₃ => by
    have hj : j ≠ i := by rcases hi with rfl | rfl | rfl <;> assumption
    simp [upd_apply, hj], hm⟩

/-- The facts a compiled kernel statement establishes when it finishes. -/
def Post (c : KStmt) (s : St) (ks : KSt) (out : List Nat) (o : Out) (s' : St) : Prop :=
  fitsS (s.l LB) c ks out.length = true ∧ o = .norm ∧
    KRep s'.g s'.m (c.exec (s.l LB) ks).1 (out ++ (c.exec (s.l LB) ks).2) ∧ Frame s s'

theorem post_skip (s : St) (ks : KSt) (out : List Nat) (hR : KRep s.g s.m ks out) :
    Post .skip s ks out .norm s :=
  ⟨rfl, rfl, by simpa [KStmt.exec] using hR, Frame.refl s⟩

theorem post_emit (e : KExp) {f : Nat} {s s' : St} {o : Out} {ks : KSt} {out : List Nat}
    (hR : KRep s.g s.m ks out) (h : exec (cS (.emit e)) f s = some (o, s')) :
    Post (.emit e) s ks out o s' := by
  have hx := emitS_exec (cE e) f s out.length hR.olen hR.ocap
  have hv : (cE e).eval s = e.eval ks (s.l LB) := cE_eval hR.st hR.blen e
  by_cases hc : out.length < CAP
  · simp only [cS] at h
    rw [hx] at h
    simp only [hc, ↓reduceIte] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simpa [fitsS] using hc, rfl, ?_, frame_gm _ _ _ _ (.inr (.inr rfl)) ?_⟩
    · simpa [KStmt.exec, hv] using hR.emit hc (e.eval ks (s.l LB))
    · intro a ha
      have hne : a ≠ OUT + out.length := by omega
      simp [upd_apply, hne]
  · have hn : exec (cS (.emit e)) f s = none := by simp only [cS, hx, hc, ite_false]
    rw [hn] at h
    cases h

theorem post_push (e : KExp) {f : Nat} {s s' : St} {o : Out} {ks : KSt} {out : List Nat}
    (hR : KRep s.g s.m ks out) (h : exec (cS (.push e)) f s = some (o, s')) :
    Post (.push e) s ks out o s' := by
  have hx := pushS_exec (cE e) f s ks.buf.length hR.blen hR.bcap
  have hv : (cE e).eval s = e.eval ks (s.l LB) := cE_eval hR.st hR.blen e
  by_cases hc : ks.buf.length < CAP
  · simp only [cS] at h
    rw [hx] at h
    simp only [hc, ↓reduceIte] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simpa [fitsS] using hc, rfl, ?_, frame_gm _ _ _ _ (.inr (.inl rfl)) ?_⟩
    · simpa [KStmt.exec, hv] using hR.push hc (e.eval ks (s.l LB))
    · intro a ha
      have hne : a ≠ KBUF + ks.buf.length := by simp [OUT, KBUF] at *; omega
      simp [upd_apply, hne]
  · have hn : exec (cS (.push e)) f s = none := by simp only [cS, hx, hc, ite_false]
    rw [hn] at h
    cases h

theorem post_emitBuf {f : Nat} {s s' : St} {o : Out} {ks : KSt} {out : List Nat}
    (hR : KRep s.g s.m ks out) (h : exec (cS .emitBuf) f s = some (o, s')) :
    Post .emitBuf s ks out o s' := by
  have hx := emitBufS_exec f s out.length ks.buf.length hR.olen hR.blen hR.ocap hR.bcap
  by_cases hc : out.length + ks.buf.length ≤ CAP
  · simp only [cS] at h
    rw [hx] at h
    simp only [hc, ↓reduceIte] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simpa [fitsS] using hc, rfl, ?_, frame_gm _ _ _ _ (.inr (.inr rfl)) ?_⟩
    · simpa [KStmt.exec] using hR.emitBuf hc
    · intro a ha
      have hne : ¬ (OUT + out.length ≤ a ∧ a < OUT + out.length + ks.buf.length) := by omega
      simp [mcopy, hne]
  · have hn : exec (cS .emitBuf) f s = none := by simp only [cS, hx, hc, ite_false]
    rw [hn] at h
    cases h

theorem post_set (e : KExp) {f : Nat} {s s' : St} {o : Out} {ks : KSt} {out : List Nat}
    (hR : KRep s.g s.m ks out) (h : exec (cS (.set e)) f s = some (o, s')) :
    Post (.set e) s ks out o s' := by
  have hv : (cE e).eval s = e.eval ks (s.l LB) := cE_eval hR.st hR.blen e
  have hs : some (Out.norm, { s with g := upd s.g GST ((cE e).eval s) }) = some (o, s') := h
  cases hs
  exact ⟨rfl, rfl, by simpa [KStmt.exec, hv] using hR.set (e.eval ks (s.l LB)),
    frame_g _ _ _ (.inl rfl)⟩

theorem post_clear {f : Nat} {s s' : St} {o : Out} {ks : KSt} {out : List Nat}
    (hR : KRep s.g s.m ks out) (h : exec (cS .clear) f s = some (o, s')) :
    Post .clear s ks out o s' := by
  have hs : some (Out.norm, { s with g := upd s.g BLEN ((E.c 0).eval s) }) = some (o, s') := h
  cases hs
  exact ⟨rfl, rfl, by simpa [KStmt.exec, E.eval] using hR.clear, frame_g _ _ _ (.inr (.inl rfl))⟩

/-- Soundness of one compiled kernel statement. -/
def PostOf (c : KStmt) : Prop :=
  ∀ {f : Nat} {s s' : St} {o : Out} {ks : KSt} {out : List Nat},
    KRep s.g s.m ks out → exec (cS c) f s = some (o, s') → Post c s ks out o s'

theorem exec_seq_some {a b : S} {f : Nat} {s : St} {r : Out × St}
    (h : exec (.seq a b) f s = some r) : ∃ r₁, exec a f s = some r₁ := by
  cases h₁ : exec a f s with
  | none => rw [exec_seq, h₁] at h; cases h
  | some r₁ => exact ⟨r₁, rfl⟩

theorem lab_some {x : Option (Out × St)} {r : Out × St} (h : lab x = some r) : ∃ r₁, x = some r₁ := by
  cases x with
  | none => cases h
  | some r₁ => exact ⟨r₁, rfl⟩

theorem post_seq {p q : KStmt} (ihp : PostOf p) (ihq : PostOf q) : PostOf (.seq p q) := by
  intro f s s' o ks out hR h
  obtain ⟨r₁, h₁⟩ : ∃ r₁, exec (cS p) f s = some r₁ := exec_seq_some h
  obtain ⟨hf₁, ho₁, hR₁, hF₁⟩ : Post p s ks out r₁.1 r₁.2 := ihp hR h₁
  have h₁' : exec (cS p) f s = some (.norm, r₁.2) := by rw [h₁, ← ho₁]
  have h₂ : exec (cS q) f r₁.2 = some (o, s') := by
    rw [← h]
    exact (exec_seq_norm h₁').symm
  have hl : r₁.2.l LB = s.l LB := by rw [hF₁.l]
  obtain ⟨hf₂, ho, hR₂, hF₂⟩ := ihq hR₁ h₂
  have hf : fitsS (s.l LB) (.seq p q) ks out.length = true := by
    simp only [fitsS, hf₁, Bool.true_and]
    simpa [hl] using hf₂
  have hR' : KRep s'.g s'.m ((KStmt.seq p q).exec (s.l LB) ks).1
      (out ++ ((KStmt.seq p q).exec (s.l LB) ks).2) := by
    simpa [KStmt.exec, List.append_assoc, hl] using hR₂
  exact ⟨hf, ho, hR', hF₁.trans hF₂⟩

/-- One arm of a conditional, under its label. -/
theorem post_arm {p c : KStmt} (ihp : PostOf p) {f : Nat} {s s' : St} {o : Out} {ks : KSt}
    {out : List Nat} (hR : KRep s.g s.m ks out) (hx : lab (exec (cS p) f s) = some (o, s'))
    (hfit : fitsS (s.l LB) c ks out.length = fitsS (s.l LB) p ks out.length)
    (hexec : c.exec (s.l LB) ks = p.exec (s.l LB) ks) : Post c s ks out o s' := by
  obtain ⟨r₁, h₁⟩ : ∃ r₁, exec (cS p) f s = some r₁ := lab_some hx
  obtain ⟨hf₁, ho₁, hR₁, hF₁⟩ : Post p s ks out r₁.1 r₁.2 := ihp hR h₁
  have hl : lab (some (Out.norm, r₁.2)) = some (o, s') := by rw [← hx, h₁, ← ho₁]
  have hr : o = .norm ∧ s' = r₁.2 := by
    simp only [lab_norm, Option.some.injEq, Prod.mk.injEq] at hl
    exact ⟨hl.1.symm, hl.2.symm⟩
  rw [hr.2]
  exact ⟨hfit ▸ hf₁, hr.1, hexec ▸ hR₁, hF₁⟩

theorem post_ite {c : KExp} {p q : KStmt} (ihp : PostOf p) (ihq : PostOf q) :
    PostOf (.ite c p q) := by
  intro f s s' o ks out hR h
  have hv : (cE c).eval s = c.eval ks (s.l LB) := cE_eval hR.st hR.blen c
  by_cases hc : c.eval ks (s.l LB) ≠ 0
  · have hx : lab (exec (cS p) f s) = some (o, s') := by
      rw [← h]
      simp only [cS, exec_ite, hv, hc, ite_true, ne_eq, not_false_eq_true]
    exact post_arm ihp hR hx (by simp [fitsS, hc]) (by simp [KStmt.exec, hc])
  · have hc' : c.eval ks (s.l LB) = 0 := Classical.not_not.mp hc
    have hx : lab (exec (cS q) f s) = some (o, s') := by
      rw [← h]
      simp only [cS, exec_ite, hv, hc', ne_eq, not_true_eq_false, ite_false]
    exact post_arm ihq hR hx (by simp [fitsS, hc']) (by simp [KStmt.exec, hc'])

/-- **Soundness of the compiled kernel statements.** -/
theorem cS_sound (c : KStmt) : PostOf c := by
  induction c with
  | skip =>
    intro f s s' o ks out hR h
    cases h
    exact post_skip s ks out hR
  | seq p q ihp ihq => exact post_seq ihp ihq
  | emit e => intro f s s' o ks out hR h; exact post_emit e hR h
  | set e => intro f s s' o ks out hR h; exact post_set e hR h
  | push e => intro f s s' o ks out hR h; exact post_push e hR h
  | emitBuf => intro f s s' o ks out hR h; exact post_emitBuf hR h
  | clear => intro f s s' o ks out hR h; exact post_clear hR h
  | ite c p q ihp ihq => exact post_ite ihp ihq

/-- Completeness of one compiled kernel statement. -/
def DoneOf (c : KStmt) : Prop :=
  ∀ {f : Nat} {s : St} {ks : KSt} {out : List Nat},
    KRep s.g s.m ks out → fitsS (s.l LB) c ks out.length = true →
    ∃ s', exec (cS c) f s = some (.norm, s')

theorem done_seq {p q : KStmt} (ihp : DoneOf p) (ihq : DoneOf q) : DoneOf (.seq p q) := by
  intro f s ks out hR hf
  have hf' : fitsS (s.l LB) p ks out.length = true ∧
      fitsS (s.l LB) q (p.exec (s.l LB) ks).1 (out.length + (p.exec (s.l LB) ks).2.length) = true := by
    simpa [fitsS] using hf
  obtain ⟨s₁, h₁⟩ := ihp (f := f) hR hf'.1
  obtain ⟨-, -, hR₁, hF₁⟩ := cS_sound p hR h₁
  have hl : s₁.l LB = s.l LB := by rw [hF₁.l]
  have hq : fitsS (s₁.l LB) q (p.exec (s.l LB) ks).1 (out ++ (p.exec (s.l LB) ks).2).length = true := by
    simpa [hl] using hf'.2
  obtain ⟨s', h₂⟩ := ihq (f := f) hR₁ hq
  exact ⟨s', by rw [cS, exec_seq_norm h₁, h₂]⟩

theorem done_ite {c : KExp} {p q : KStmt} (ihp : DoneOf p) (ihq : DoneOf q) :
    DoneOf (.ite c p q) := by
  intro f s ks out hR hf
  have hv : (cE c).eval s = c.eval ks (s.l LB) := cE_eval hR.st hR.blen c
  by_cases hc : c.eval ks (s.l LB) ≠ 0
  · obtain ⟨s', h⟩ := ihp (f := f) hR (by simpa [fitsS, hc] using hf)
    exact ⟨s', by simp only [cS, exec_ite, hv, hc, ne_eq, not_false_eq_true, ↓reduceIte, h, lab_norm]⟩
  · have hc' : c.eval ks (s.l LB) = 0 := Classical.not_not.mp hc
    obtain ⟨s', h⟩ := ihq (f := f) hR (by simpa [fitsS, hc'] using hf)
    exact ⟨s', by simp only [cS, exec_ite, hv, hc', ne_eq, not_true_eq_false, ↓reduceIte, h, lab_norm]⟩

theorem done_emit (e : KExp) : DoneOf (.emit e) := by
  intro f s ks out hR hf
  have hc : out.length < CAP := by simpa [fitsS] using hf
  have hx := emitS_exec (cE e) f s out.length hR.olen hR.ocap
  exact ⟨_, by simp only [cS]; rw [hx]; simp only [hc, ↓reduceIte]; rfl⟩

theorem done_push (e : KExp) : DoneOf (.push e) := by
  intro f s ks out hR hf
  have hc : ks.buf.length < CAP := by simpa [fitsS] using hf
  have hx := pushS_exec (cE e) f s ks.buf.length hR.blen hR.bcap
  exact ⟨_, by simp only [cS]; rw [hx]; simp only [hc, ↓reduceIte]; rfl⟩

theorem done_emitBuf : DoneOf .emitBuf := by
  intro f s ks out hR hf
  have hc : out.length + ks.buf.length ≤ CAP := by simpa [fitsS] using hf
  have hx := emitBufS_exec f s out.length ks.buf.length hR.olen hR.blen hR.ocap hR.bcap
  exact ⟨_, by simp only [cS]; rw [hx]; simp only [hc, ↓reduceIte]; rfl⟩

/-- **Completeness of the compiled kernel statements**: when the bounds checks pass, the
statement finishes. -/
theorem cS_complete (c : KStmt) : DoneOf c := by
  induction c with
  | skip => intro f s ks out _ _; exact ⟨s, rfl⟩
  | seq p q ihp ihq => exact done_seq ihp ihq
  | emit e => exact done_emit e
  | set e => intro f s ks out _ _; exact ⟨_, rfl⟩
  | push e => exact done_push e
  | emitBuf => exact done_emitBuf
  | clear => intro f s ks out _ _; exact ⟨_, rfl⟩
  | ite c p q ihp ihq => exact done_ite ihp ihq

/-- Setting a global other than the kernel's keeps the representation. -/
theorem KRep.upd_g {g m : Nat → Nat} {ks : KSt} {out : List Nat} (h : KRep g m ks out) {i : Nat}
    (v : Nat) (h₁ : i ≠ GST) (h₂ : i ≠ BLEN) (h₃ : i ≠ OLEN) : KRep (upd g i v) m ks out :=
  ⟨by simpa [upd_apply, Ne.symm h₁] using h.st, by simpa [upd_apply, Ne.symm h₂] using h.blen,
    h.bufs, by simpa [upd_apply, Ne.symm h₃] using h.olen, h.outs, h.bcap, h.ocap⟩

end Silmaril.Proofs.Wasm.JcoTool.KCore
