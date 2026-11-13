module

public import Silmaril.Proofs.Wasm.JcoTool.KTee.Basic

/-!
# The generated tee: what each piece of the callback does

`onW_exec`, `onR_exec`: the bookkeeping after a write and after a read, as functions of the
packed result (`onWS`, `onRS`). `actW_ret`, `actR_ret`, `actStop_ret`, `actClose_ret`: each
action of an invocation after `YIELD` is one built-in call and its bookkeeping. `readyT_ret`:
the invocation after `YIELD` is the first action whose guard holds, or `EXIT`, or `WAIT`.
`cbT_ret`: the dispatch on the event.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KTee

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Event EventCode blocked)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.JcoTool.KTee

/-! ## Bookkeeping -/

/-- The globals and memory after a write of output `j` with packed result `p`. -/
def onWS (j p : Nat) (g m : Nat → Nat) : (Nat → Nat) × (Nat → Nat) :=
  if p % 16 = 0 then
    (upd g (OFFg j) (if g LENg - g (OFFg j) ≤ p / 16 then g LENg else g (OFFg j) + p / 16),
      upd m (aO j) 0)
  else (g, upd m (aO j) 2)

/-- The globals and memory after a read with packed result `p`. -/
def onRS (p : Nat) (g m : Nat → Nat) : (Nat → Nat) × (Nat → Nat) :=
  (upd (upd (upd g LENg (p / 16)) OFF0 0) OFF1 0, upd m aRS (if p % 16 = 0 then 0 else 2))

theorem c_eval (n : Nat) (t : St) (h : n < M32) : (E.c n).eval t = n := Nat.mod_eq_of_lt h

theorem sub_eval (t : St) (a b : Nat) (h : t.g b ≤ t.g a) (ha : t.g a < M32) :
    (E.bin .sub (.g a) (.g b)).eval t = t.g a - t.g b := by
  simp only [E.eval, Bin.eval]
  rw [Nat.mod_eq_of_lt (show t.g b < M32 by omega)]
  have : t.g a + (M32 - t.g b) = (t.g a - t.g b) + M32 := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem endedOf_eval (p : E) (t : St) :
    (endedOf p).eval t = if p.eval t % 16 = 0 then 0 else 2 := by
  have h16 : (16 : Nat) % M32 = 16 := rfl
  have h0 : (0 : Nat) % M32 = 0 := rfl
  simp only [endedOf, E.eval, Bin.eval, h16, h0]
  by_cases h : p.eval t % 16 = 0 <;> simp [h, M32]

theorem endedOf_l (i : Nat) (t : St) :
    (endedOf (.l i)).eval t = if t.l i % 16 = 0 then 0 else 2 := endedOf_eval _ _

/-- After a write: `onWS`. -/
theorem onW_exec (j i f : Nat) (s : DSt) (hj : j ≤ 1) (hp : s.l i < M32)
    (hle : s.g (OFFg j) ≤ s.g LENg) (hL : s.g LENg ≤ 256) :
    dexec (onW j (.l i)) f s =
      some (.norm, { s with g := (onWS j (s.l i) s.g s.m).1, m := (onWS j (s.l i) s.g s.m).2 }) := by
  have h16 : (16 : Nat) % M32 = 16 := rfl
  have hc2 : (2 : Nat) % M32 = 2 := rfl
  have hc0 : (0 : Nat) % M32 = 0 := rfl
  have hA : (aO j) % M32 = aO j := Nat.mod_eq_of_lt (by simp [aO, M32]; omega)
  have hsub : (E.bin .sub (.g LENg) (.g (OFFg j))).eval s.down = s.g LENg - s.g (OFFg j) :=
    sub_eval s.down _ _ hle (by simp [DSt.down, M32]; omega)
  by_cases hs : s.l i % 16 = 0
  · have hadd : (s.g (OFFg j) + s.l i / 16) % M32 = s.g (OFFg j) + s.l i / 16 :=
      Nat.mod_eq_of_lt (by simp [M32] at hp ⊢; omega)
    simp only [onW, dexec, E.eval, Bin.eval, h16, hc0, hA, DSt.down, hs, ne_eq,
      not_true_eq_false, ↓reduceIte, dexec.dlab, onWS] at hsub ⊢
    rw [hsub]
    by_cases hge : s.g LENg - s.g (OFFg j) ≤ s.l i / 16
    · simp [hge]
    · simp [hge, hadd]
  · simp [onW, dexec, E.eval, Bin.eval, h16, hc2, hA, DSt.down, hs, dexec.dlab, onWS]

/-- After a read: `onRS`. -/
theorem onR_exec (i f : Nat) (s : DSt) :
    dexec (onR (.l i)) f s =
      some (.norm, { s with g := (onRS (s.l i) s.g s.m).1, m := (onRS (s.l i) s.g s.m).2 }) := by
  have hR : aRS % M32 = aRS := rfl
  have h16 : (16 : Nat) % M32 = 16 := rfl
  have hc0 : (0 : Nat) % M32 = 0 := rfl
  have hlt : (if s.l i % 16 = 0 then 0 else 2) % 256 = (if s.l i % 16 = 0 then 0 else 2) := by
    split <;> rfl
  simp only [onR, seqs, dexec, endedOf_l, E.eval, Bin.eval, h16, hc0, hR, DSt.down, hlt, onRS]

/-- `return YIELD` after a statement that ends normally. -/
theorem seq_yield {a : S} {f v : Nat} {s s₁ s' : DSt} (ha : dexec a f s = some (.norm, s₁))
    (h : dexec (.seq a yield_) f s = some (.ret v, s')) : v = 1 ∧ s' = s₁ := by
  rw [dexec_seq_norm ha] at h
  simp only [yield_, dexec, E.eval, Option.some.injEq, Prod.mk.injEq, Out.ret.injEq] at h
  exact ⟨h.1.symm.trans rfl, h.2.symm⟩

theorem ite_then {c : E} {t e : S} {f : Nat} {s s₂ : DSt} (hc : c.eval s.down ≠ 0)
    (ht : dexec t f s = some (.norm, s₂)) : dexec (.ite c t e) f s = some (.norm, s₂) := by
  show dexec.dlab (if c.eval s.down ≠ 0 then dexec t f s else dexec e f s) = _
  simp only [ne_eq, hc, not_false_eq_true, ↓reduceIte, ht]; rfl

theorem ite_else {c : E} {t e : S} {f : Nat} {s s₂ : DSt} (hc : c.eval s.down = 0)
    (he : dexec e f s = some (.norm, s₂)) : dexec (.ite c t e) f s = some (.norm, s₂) := by
  show dexec.dlab (if c.eval s.down ≠ 0 then dexec t f s else dexec e f s) = _
  simp only [ne_eq, hc, not_true_eq_false, ↓reduceIte, he]; rfl

theorem st8_exec (a v f : Nat) (s : DSt) (ha : a < M32) (hv : v < 256) :
    dexec (.st8 (.c a) (.c v)) f s = some (.norm, { s with m := upd s.m a v }) := by
  simp [dexec, E.eval, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hv,
    Nat.mod_eq_of_lt (show v < M32 by simp [M32]; omega)]

/-! ## The built-ins -/

theorem dcall_write {h p n d : Nat} {s s₁ : DSt} {o : Out}
    (hc : dcallBI .streamWrite [h, p, n] [d] s = some (o, s₁)) :
    ∃ st₁ r, dstep s.st (.streamWrite h ((slice s.m p n).map u8v)) = some (st₁, .nat r) ∧ r < M32 ∧
      o = .norm ∧ s₁ = { s with st := st₁, l := upd s.l d r } := by
  simp only [dcallBI] at hc
  split at hc
  · rename_i st₁ r hd
    split_ifs at hc with hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    exact ⟨st₁, r, hd, hr, hc.1.symm, hc.2.symm⟩
  · cases hc

theorem dcall_read {h p n d : Nat} {s s₁ : DSt} {o : Out}
    (hc : dcallBI .streamRead [h, p, n] [d] s = some (o, s₁)) : o = .norm ∧ ∃ st₁,
      (∃ code xs, dstep s.st (.streamRead h n) = some (st₁, .read code xs) ∧ code < M32 ∧
        code / 16 = xs.length ∧ xs.length ≤ n ∧
        s₁ = { s with st := st₁, m := writeBytes s.m p (xs.map byteOf), l := upd s.l d code }) ∨
      (dstep s.st (.streamRead h n) = some (st₁, .nat blocked) ∧
        s₁ = { s with st := st₁, rp := some (h, p), l := upd s.l d blocked }) := by
  simp only [dcallBI] at hc
  split at hc
  · rename_i st₁ code xs hd
    split_ifs at hc with hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    exact ⟨hc.1.symm, st₁, .inl ⟨code, xs, hd, hr.1, hr.2.1, hr.2.2, hc.2.symm⟩⟩
  · rename_i st₁ r hd
    split_ifs at hc with hr
    subst hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    exact ⟨hc.1.symm, st₁, .inr ⟨hd, hc.2.symm⟩⟩
  · cases hc

theorem dcall_dropR {h : Nat} {s s₁ : DSt} {o : Out}
    (hc : dcallBI .dropR [h] [] s = some (o, s₁)) :
    ∃ st₁ res, dstep s.st (.streamDropR h) = some (st₁, res) ∧ o = .norm ∧ s₁ = { s with st := st₁ } := by
  simp only [dcallBI] at hc
  obtain ⟨⟨st₁, res⟩, hd, he⟩ := Option.map_eq_some_iff.mp hc
  simp only [Prod.mk.injEq] at he
  exact ⟨st₁, res, hd, he.1.symm, he.2.symm⟩

theorem dcall_dropW {h : Nat} {s s₁ : DSt} {o : Out}
    (hc : dcallBI .dropW [h] [] s = some (o, s₁)) :
    ∃ st₁ res, dstep s.st (.streamDropW h) = some (st₁, res) ∧ o = .norm ∧ s₁ = { s with st := st₁ } := by
  simp only [dcallBI] at hc
  obtain ⟨⟨st₁, res⟩, hd, he⟩ := Option.map_eq_some_iff.mp hc
  simp only [Prod.mk.injEq] at he
  exact ⟨st₁, res, hd, he.1.symm, he.2.symm⟩

/-- A call never returns. -/
theorem call_seq {b : BI} {as : List E} {ds : List Nat} {rest : S} {f v : Nat} {s s' : DSt}
    (h : dexec (.seq (.call b as ds) rest) f s = some (.ret v, s')) :
    ∃ s₁, dcallBI b (as.map (·.eval s.down)) ds s = some (.norm, s₁) ∧ dexec rest f s₁ = some (.ret v, s') := by
  rcases dexec_seq_ret h with h1 | ⟨s₁, h1, h2⟩
  · exfalso
    change dcallBI b _ ds s = _ at h1
    unfold dcallBI at h1
    repeat' split at h1
    all_goals (first | cases h1 | (simp at h1))
  · exact ⟨s₁, h1, h2⟩

/-! ## The actions -/

/-- The test of a copy's result against `BLOCKED`. -/
theorem isE_LR_iff (s : DSt) : (isE (.l LR) blocked).eval s.down ≠ 0 ↔ s.l LR = blocked :=
  isE_ne _ _ blocked_lt _

/-- After a `stream.write` with result `r` in `LR`: the bookkeeping and `YIELD`. -/
theorem actW_tail {j f v : Nat} {s s' : DSt} (hj : j ≤ 1) (hrM : s.l LR < M32)
    (hle : s.g (OFFg j) ≤ s.g LENg) (hL : s.g LENg ≤ 256)
    (h : dexec (.seq (.ite (isE (.l LR) blocked) (.st8 (.c (aO j)) (.c 1)) (onW j (.l LR))) yield_) f s =
      some (.ret v, s')) :
    v = 1 ∧ s'.st = s.st ∧ s'.rp = s.rp ∧
      (s.l LR = blocked → s'.g = s.g ∧ s'.m = upd s.m (aO j) 1) ∧
      (s.l LR ≠ blocked → s'.g = (onWS j (s.l LR) s.g s.m).1 ∧ s'.m = (onWS j (s.l LR) s.g s.m).2) := by
  have hA : aO j < M32 := by simp [aO, M32]; omega
  by_cases hb : s.l LR = blocked
  · have hc : (isE (.l LR) blocked).eval s.down ≠ 0 := (isE_LR_iff s).mpr hb
    have hy : v = 1 ∧ s' = { s with m := upd s.m (aO j) 1 } :=
      seq_yield (ite_then hc (st8_exec _ _ _ _ hA (by decide))) h
    rw [hy.2]
    exact ⟨hy.1, rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun h' => absurd hb h'⟩
  · have hc : (isE (.l LR) blocked).eval s.down = 0 := by
      by_contra hne; exact hb ((isE_LR_iff s).mp hne)
    have hy : v = 1 ∧ s' = { s with g := (onWS j (s.l LR) s.g s.m).1, m := (onWS j (s.l LR) s.g s.m).2 } :=
      seq_yield (ite_else hc (onW_exec j LR f s hj hrM hle hL)) h
    rw [hy.2]
    exact ⟨hy.1, rfl, rfl, fun h' => absurd h' hb, fun _ => ⟨rfl, rfl⟩⟩

/-- **Write the rest of the batch to output `j`**: one `stream.write`, then the bookkeeping. -/
theorem actW_ret {j f v : Nat} {s s' : DSt} (hj : j ≤ 1) (hlt : s.g (OFFg j) < s.g LENg)
    (hL : s.g LENg ≤ 256) (h : dexec (actW j) f s = some (.ret v, s')) :
    ∃ st₁ r, dstep s.st (.streamWrite (s.g (WHg j))
        ((slice s.m (IN + s.g (OFFg j)) (s.g LENg - s.g (OFFg j))).map u8v)) = some (st₁, .nat r) ∧
      r < M32 ∧ v = 1 ∧ s'.st = st₁ ∧ s'.rp = s.rp ∧
      (r = blocked → s'.g = s.g ∧ s'.m = upd s.m (aO j) 1) ∧
      (r ≠ blocked → s'.g = (onWS j r s.g s.m).1 ∧ s'.m = (onWS j r s.g s.m).2) := by
  have hadd : (E.bin .add (.c IN) (.g (OFFg j))).eval s.down = IN + s.g (OFFg j) := by
    show (IN % M32 + s.g (OFFg j)) % M32 = _
    exact Nat.mod_eq_of_lt (by simp [IN, M32]; omega)
  have hsub : (E.bin .sub (.g LENg) (.g (OFFg j))).eval s.down = s.g LENg - s.g (OFFg j) :=
    sub_eval s.down _ _ (Nat.le_of_lt hlt) (by simp [DSt.down, M32]; omega)
  obtain ⟨s₁, hc, hr⟩ := call_seq h
  have hw : (E.g (WHg j)).eval s.down = s.g (WHg j) := rfl
  have hc' : dcallBI .streamWrite [s.g (WHg j), IN + s.g (OFFg j), s.g LENg - s.g (OFFg j)] [LR] s =
      some (.norm, s₁) := by simpa only [List.map, hadd, hsub, hw] using hc
  obtain ⟨st₁, r, hd, hrM, -, hs₁⟩ := dcall_write hc'
  have hl : s₁.l LR = r := by rw [hs₁]; simp [upd]
  have ht := actW_tail (s := s₁) hj (by rw [hl]; exact hrM) (by rw [hs₁]; exact Nat.le_of_lt hlt)
    (by rw [hs₁]; exact hL) hr
  rw [hl, hs₁] at ht
  exact ⟨st₁, r, hd, hrM, ht⟩

/-- The globals with an empty batch. -/
def g0 (g : Nat → Nat) : Nat → Nat := upd (upd (upd g LENg 0) OFF0 0) OFF1 0

theorem g0_INSR (g : Nat → Nat) : g0 g INSR = g INSR := by simp [g0, upd, INSR, LENg, OFF0, OFF1]

/-- `global.set i 0`. -/
theorem gset0_exec (i f : Nat) (s : DSt) :
    dexec (.gset i (.c 0)) f s = some (.norm, { s with g := upd s.g i 0 }) := rfl

/-- After a `stream.read` with result `code` in `LR`: the bookkeeping and `YIELD`. -/
theorem actR_tail {f v : Nat} {s s' : DSt}
    (h : dexec (.seq (.ite (isE (.l LR) blocked) (.st8 (.c aRS) (.c 1)) (onR (.l LR))) yield_) f s =
      some (.ret v, s')) :
    v = 1 ∧ s'.st = s.st ∧ s'.rp = s.rp ∧
      (s.l LR = blocked → s'.g = s.g ∧ s'.m = upd s.m aRS 1) ∧
      (s.l LR ≠ blocked → s'.g = (onRS (s.l LR) s.g s.m).1 ∧ s'.m = (onRS (s.l LR) s.g s.m).2) := by
  by_cases hb : s.l LR = blocked
  · have hc : (isE (.l LR) blocked).eval s.down ≠ 0 := (isE_LR_iff s).mpr hb
    have hy : v = 1 ∧ s' = { s with m := upd s.m aRS 1 } :=
      seq_yield (ite_then hc (st8_exec _ _ _ _ (by decide) (by decide))) h
    rw [hy.2]
    exact ⟨hy.1, rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun h' => absurd hb h'⟩
  · have hc : (isE (.l LR) blocked).eval s.down = 0 := by
      by_contra hne; exact hb ((isE_LR_iff s).mp hne)
    have hy : v = 1 ∧ s' = { s with g := (onRS (s.l LR) s.g s.m).1, m := (onRS (s.l LR) s.g s.m).2 } :=
      seq_yield (ite_else hc (onR_exec LR f s)) h
    rw [hy.2]
    exact ⟨hy.1, rfl, rfl, fun h' => absurd h' hb, fun _ => ⟨rfl, rfl⟩⟩

/-- The `stream.read` call of `actR`, on the state with an empty batch. -/
theorem actR_call {N f v : Nat} {s s' : DSt} (hN : N ≤ 256) (h : dexec (actR N) f s = some (.ret v, s')) :
    ∃ s₁, dcallBI .streamRead [s.g INSR, IN, N] [LR] { s with g := g0 s.g } = some (.norm, s₁) ∧
      dexec (.seq (.ite (isE (.l LR) blocked) (.st8 (.c aRS) (.c 1)) (onR (.l LR))) yield_) f s₁ =
        some (.ret v, s') := by
  have h' : dexec (seqs [.call .streamRead [.g INSR, .c IN, .c N] [LR],
      .ite (isE (.l LR) blocked) (.st8 (.c aRS) (.c 1)) (onR (.l LR)), yield_]) f
      { s with g := g0 s.g } = some (.ret v, s') := by
    have e1 := dexec_seq_norm (b := .seq (.gset OFF0 (.c 0)) (.seq (.gset OFF1 (.c 0))
      (seqs [.call .streamRead [.g INSR, .c IN, .c N] [LR],
        .ite (isE (.l LR) blocked) (.st8 (.c aRS) (.c 1)) (onR (.l LR)), yield_]))) (gset0_exec LENg f s)
    have e2 := dexec_seq_norm (b := .seq (.gset OFF1 (.c 0))
      (seqs [.call .streamRead [.g INSR, .c IN, .c N] [LR],
        .ite (isE (.l LR) blocked) (.st8 (.c aRS) (.c 1)) (onR (.l LR)), yield_])) (gset0_exec OFF0 f { s with g := upd s.g LENg 0 })
    have e3 := dexec_seq_norm (b := seqs [.call .streamRead [.g INSR, .c IN, .c N] [LR],
        .ite (isE (.l LR) blocked) (.st8 (.c aRS) (.c 1)) (onR (.l LR)), yield_]) (gset0_exec OFF1 f { s with g := upd (upd s.g LENg 0) OFF0 0 })
    have h1 : dexec (actR N) f s = _ := (e1.trans e2).trans e3
    exact h1 ▸ h
  have hargs : [E.g INSR, .c IN, .c N].map (·.eval ({ s with g := g0 s.g } : DSt).down) =
      [s.g INSR, IN, N] := by
    simp [E.eval, DSt.down, g0_INSR, IN, M32, Nat.mod_eq_of_lt (show N < 4294967296 by omega)]
  obtain ⟨s₁, hc, hr⟩ := call_seq h'
  exact ⟨s₁, by rw [← hargs]; exact hc, hr⟩

/-- **Read the next batch**: one `stream.read`, then the bookkeeping. -/
theorem actR_ret {N f v : Nat} {s s' : DSt} (hN : N ≤ 256) (h : dexec (actR N) f s = some (.ret v, s')) :
    v = 1 ∧
      ((∃ code xs, dstep s.st (.streamRead (s.g INSR) N) = some (s'.st, .read code xs) ∧ code < M32 ∧
        code / 16 = xs.length ∧ xs.length ≤ N ∧ s'.rp = s.rp ∧
        s'.g = (onRS code (g0 s.g) (writeBytes s.m IN (xs.map byteOf))).1 ∧
        s'.m = (onRS code (g0 s.g) (writeBytes s.m IN (xs.map byteOf))).2) ∨
      (dstep s.st (.streamRead (s.g INSR) N) = some (s'.st, .nat blocked) ∧
        s'.rp = some (s.g INSR, IN) ∧ s'.g = g0 s.g ∧ s'.m = upd s.m aRS 1)) := by
  obtain ⟨s₁, hc, hr⟩ := actR_call hN h
  obtain ⟨hv, hst, hrp, hb, hnb⟩ := actR_tail hr
  obtain ⟨-, st₁, hrd⟩ := dcall_read hc
  refine ⟨hv, ?_⟩
  rcases hrd with ⟨code, xs, hd, hcM, hlen, hxs, hs₁⟩ | ⟨hd, hs₁⟩
  · have hnb' : code ≠ blocked := by
      intro e; rw [e] at hlen; simp [blocked] at hlen; omega
    have hl : s₁.l LR = code := by rw [hs₁]; simp [upd]
    have hg := hnb (by rw [hl]; exact hnb')
    rw [hl, hs₁] at hg
    rw [hs₁] at hst hrp
    exact .inl ⟨code, xs, by rw [hst]; exact hd, hcM, hlen, hxs, hrp, hg⟩
  · have hl : s₁.l LR = blocked := by rw [hs₁]; simp [upd]
    have hg := hb hl
    rw [hs₁] at hg hst hrp
    exact .inr ⟨by rw [hst]; exact hd, hrp, hg⟩

/-- **Drop the input.** -/
theorem actStop_ret {f v : Nat} {s s' : DSt} (h : dexec actStop f s = some (.ret v, s')) :
    v = 1 ∧ (∃ res, dstep s.st (.streamDropR (s.g INSR)) = some (s'.st, res)) ∧ s'.rp = s.rp ∧
      s'.g = s.g ∧ s'.m = upd s.m aRS 3 := by
  obtain ⟨s₁, hc, hr⟩ := call_seq h
  obtain ⟨st₁, res, hd, -, rfl⟩ := dcall_dropR hc
  obtain ⟨rfl, rfl⟩ := seq_yield (st8_exec _ _ _ _ (by decide) (by decide)) hr
  exact ⟨rfl, ⟨res, hd⟩, rfl, rfl, rfl⟩

/-- **Drop output `j`.** -/
theorem actClose_ret {j f v : Nat} {s s' : DSt} (hj : j ≤ 1) (h : dexec (actClose j) f s = some (.ret v, s')) :
    v = 1 ∧ (∃ res, dstep s.st (.streamDropW (s.g (WHg j))) = some (s'.st, res)) ∧ s'.rp = s.rp ∧
      s'.g = s.g ∧ s'.m = upd s.m (aO j) 3 := by
  obtain ⟨s₁, hc, hr⟩ := call_seq h
  obtain ⟨st₁, res, hd, -, rfl⟩ := dcall_dropW hc
  obtain ⟨rfl, rfl⟩ := seq_yield (st8_exec _ _ _ _ (by simp [aO, M32]; omega) (by decide)) hr
  exact ⟨rfl, ⟨res, hd⟩, rfl, rfl, rfl⟩

/-! ## Dispatch -/

theorem ret_exec {e : E} {f v : Nat} {s s' : DSt} (h : dexec (.ret e) f s = some (.ret v, s')) :
    v = e.eval s.down ∧ s' = s := by
  simp only [dexec, Option.some.injEq, Prod.mk.injEq, Out.ret.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- **After `YIELD`**: the first action whose guard holds, or `EXIT`, or `WAIT`. -/
theorem readyT_ret {N f v : Nat} {s s' : DSt} (h : dexec (readyT N) f s = some (.ret v, s')) :
    (s.m (aO 0) = 0 ∧ s.g OFF0 < s.g LENg ∧ dexec (actW 0) f s = some (.ret v, s')) ∨
    (s.m (aO 1) = 0 ∧ s.g OFF1 < s.g LENg ∧ dexec (actW 1) f s = some (.ret v, s')) ∨
    (¬ (s.m (aO 0) = 0 ∧ s.g OFF0 < s.g LENg) ∧ ¬ (s.m (aO 1) = 0 ∧ s.g OFF1 < s.g LENg) ∧
      s.m aRS = 0 ∧ s.m (aO 0) ≠ 1 ∧ s.m (aO 1) ≠ 1 ∧ ¬ (s.m (aO 0) = 2 ∧ s.m (aO 1) = 2) ∧
      dexec (actR N) f s = some (.ret v, s')) ∨
    ((s.m aRS = 2 ∨ (s.m aRS = 0 ∧ s.m (aO 0) = 2 ∧ s.m (aO 1) = 2)) ∧
      dexec actStop f s = some (.ret v, s')) ∨
    (s.m aRS = 3 ∧ ((s.m (aO 0) = 0 ∧ s.g LENg ≤ s.g OFF0) ∨ s.m (aO 0) = 2) ∧
      dexec (actClose 0) f s = some (.ret v, s')) ∨
    (s.m aRS = 3 ∧ ((s.m (aO 1) = 0 ∧ s.g LENg ≤ s.g OFF1) ∨ s.m (aO 1) = 2) ∧
      dexec (actClose 1) f s = some (.ret v, s')) ∨
    (s.m aRS = 3 ∧ s.m (aO 0) = 3 ∧ s.m (aO 1) = 3 ∧ v = 0 ∧ s' = s) ∨
    (v = waitCode.eval s.down ∧ s' = s) := by
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨c0, h⟩
  · exact .inl ⟨((wrG_iff 0 (by omega) _).mp c).1, ((wrG_iff 0 (by omega) _).mp c).2, h⟩
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨c1, h⟩
  · exact .inr (.inl ⟨((wrG_iff 1 (by omega) _).mp c).1, ((wrG_iff 1 (by omega) _).mp c).2, h⟩)
  have n0 : ¬ (s.m (aO 0) = 0 ∧ s.g OFF0 < s.g LENg) := fun hh =>
    ((wrG_iff 0 (by omega) s.down).mpr hh) c0
  have n1 : ¬ (s.m (aO 1) = 0 ∧ s.g OFF1 < s.g LENg) := fun hh =>
    ((wrG_iff 1 (by omega) s.down).mpr hh) c1
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · obtain ⟨a, b, c', d⟩ := (rdG_iff _).mp c
    exact .inr (.inr (.inl ⟨n0, n1, a, b, c', d, h⟩))
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · exact .inr (.inr (.inr (.inl ⟨(stopG_iff _).mp c, h⟩)))
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · obtain ⟨a, b⟩ := (closeG_iff 0 (by omega) _).mp c
    exact .inr (.inr (.inr (.inr (.inl ⟨a, b, h⟩))))
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · obtain ⟨a, b⟩ := (closeG_iff 1 (by omega) _).mp c
    exact .inr (.inr (.inr (.inr (.inr (.inl ⟨a, b, h⟩)))))
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · obtain ⟨a, b, c'⟩ := (exitG_iff _).mp c
    obtain ⟨hv, hs⟩ := ret_exec h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨a, b, c', hv.trans rfl, hs⟩))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (ret_exec h)))))))

/-- **The dispatch** on the event's code and handle. -/
theorem cbT_ret {N f v : Nat} {s s' : DSt} (h : dexec (cbT N) f s = some (.ret v, s')) :
    (s.l 0 = 2 ∧ s.l 1 = s.g INSR ∧ dexec evR f s = some (.ret v, s')) ∨
    (s.l 0 = 3 ∧ s.l 1 = s.g OUTSW ∧ dexec (evW 0) f s = some (.ret v, s')) ∨
    (s.l 0 = 3 ∧ s.l 1 = s.g W1g ∧ dexec (evW 1) f s = some (.ret v, s')) ∨
    (s.l 0 = 0 ∧ dexec (readyT N) f s = some (.ret v, s')) := by
  have hev : ∀ (c i : Nat), c < M32 →
      (andE (isE (.l 0) c) (.bin .eq (.l 1) (.g i))).eval s.down ≠ 0 → s.l 0 = c ∧ s.l 1 = s.g i := by
    intro c i hc hh
    rw [andE_ne, isE_ne _ _ hc] at hh
    exact ⟨hh.1, (ite01_ne _).mp hh.2⟩
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · exact .inl ⟨(hev 2 _ (by decide) c).1, (hev 2 _ (by decide) c).2, h⟩
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · exact .inr (.inl ⟨(hev 3 _ (by decide) c).1, (hev 3 _ (by decide) c).2, h⟩)
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · exact .inr (.inr (.inl ⟨(hev 3 _ (by decide) c).1, (hev 3 _ (by decide) c).2, h⟩))
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · exact .inr (.inr (.inr ⟨(isE_ne _ _ (by decide) _).mp c, h⟩))
  · cases h

/-! ## Events -/

/-- **A read event of the input.** -/
theorem evR_ret {f v : Nat} {s s' : DSt} (h : dexec evR f s = some (.ret v, s')) :
    v = 1 ∧ s'.st = s.st ∧ s'.rp = s.rp ∧
      ((s.m aRS = 1 ∧ s'.g = (onRS (s.l 2) s.g s.m).1 ∧ s'.m = (onRS (s.l 2) s.g s.m).2) ∨
       (s.m aRS = 0 ∧ s.l 2 / 16 = 0 ∧ s'.g = s.g ∧
          s'.m = upd s.m aRS (if s.l 2 % 16 = 0 then 0 else 2))) := by
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · rw [isE_ne _ _ (by decide), eval_ldA_RS] at c
    obtain ⟨rfl, rfl⟩ := seq_yield (onR_exec 2 f s) h
    exact ⟨rfl, rfl, rfl, .inl ⟨c, rfl, rfl⟩⟩
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · rw [andE_ne, isE_ne _ _ (by decide), isE_ne _ _ (by decide), eval_ldA_RS] at c
    have hst : dexec (.st8 (.c aRS) (endedOf (.l 2))) f s =
        some (.norm, { s with m := upd s.m aRS (if s.l 2 % 16 = 0 then 0 else 2) }) := by
      have hlt : (if s.l 2 % 16 = 0 then 0 else 2) % 256 = (if s.l 2 % 16 = 0 then 0 else 2) := by
        split <;> rfl
      simp only [dexec, endedOf_l, E.eval, DSt.down, hlt]
      rfl
    obtain ⟨rfl, rfl⟩ := seq_yield hst h
    exact ⟨rfl, rfl, rfl, .inr ⟨c.1, c.2, rfl, rfl⟩⟩
  · cases h

/-- `DROPPED` on an idle output makes it dead; any other result leaves it. -/
theorem evW_idle {j f v : Nat} {s s' : DSt} (hj : j ≤ 1)
    (h : dexec (.seq (.ite (.bin .remu (.l 2) (.c 16)) (.st8 (.c (aO j)) (.c 2)) .nop) yield_) f s =
      some (.ret v, s')) :
    v = 1 ∧ s' = { s with m := if s.l 2 % 16 = 0 then s.m else upd s.m (aO j) 2 } := by
  have hA : aO j < M32 := by simp [aO, M32]; omega
  have hev : (E.bin .remu (.l 2) (.c 16)).eval s.down = s.l 2 % 16 := by
    simp [E.eval, Bin.eval, DSt.down, M32]
  by_cases hs : s.l 2 % 16 = 0
  · have hn : dexec (.ite (.bin .remu (.l 2) (.c 16)) (.st8 (.c (aO j)) (.c 2)) .nop) f s =
        some (.norm, s) := ite_else (by rw [hev, hs]) rfl
    have hy : v = 1 ∧ s' = s := seq_yield hn h
    exact ⟨hy.1, by rw [hy.2]; simp [hs]⟩
  · have hn := ite_then (e := .nop) (by rw [hev]; exact hs) (st8_exec (aO j) 2 f s hA (by decide))
    have hy : v = 1 ∧ s' = { s with m := upd s.m (aO j) 2 } := seq_yield hn h
    exact ⟨hy.1, by rw [hy.2]; simp [hs]⟩

/-- **A write event of output `j`.** -/
theorem evW_ret {j f v : Nat} {s s' : DSt} (hj : j ≤ 1) (hp : s.l 2 < M32)
    (hle : s.g (OFFg j) ≤ s.g LENg) (hL : s.g LENg ≤ 256) (h : dexec (evW j) f s = some (.ret v, s')) :
    v = 1 ∧ s'.st = s.st ∧ s'.rp = s.rp ∧
      ((s.m (aO j) = 1 ∧ s'.g = (onWS j (s.l 2) s.g s.m).1 ∧ s'.m = (onWS j (s.l 2) s.g s.m).2) ∨
       (s.m (aO j) = 0 ∧ s'.g = s.g ∧ s'.m = if s.l 2 % 16 = 0 then s.m else upd s.m (aO j) 2) ∨
       (s.m (aO j) ≠ 0 ∧ s.m (aO j) ≠ 1 ∧ s' = s)) := by
  have hb : ∀ n, n < M32 → ((isE (ldA (aO j)) n).eval s.down ≠ 0 ↔ s.m (aO j) = n) := fun n hn => by
    rw [isE_ne _ _ hn, eval_ldA_O _ _ hj]; rfl
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨c1, h⟩
  · have hy : v = 1 ∧ s' = { s with g := (onWS j (s.l 2) s.g s.m).1, m := (onWS j (s.l 2) s.g s.m).2 } :=
      seq_yield (onW_exec j 2 f s hj hp hle hL) h
    rw [hy.2]
    exact ⟨hy.1, rfl, rfl, .inl ⟨(hb 1 (by decide)).mp c, rfl, rfl⟩⟩
  have n1 : s.m (aO j) ≠ 1 := fun e => (hb 1 (by decide)).mpr e c1
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨c0, h⟩
  · have hy := evW_idle hj h
    rw [hy.2]
    exact ⟨hy.1, rfl, rfl, .inr (.inl ⟨(hb 0 (by decide)).mp c, rfl, rfl⟩)⟩
  · have n0 : s.m (aO j) ≠ 0 := fun e => (hb 0 (by decide)).mpr e c0
    have hy : v = 1 ∧ s' = s := by
      have e := ret_exec (e := .c 1) h
      exact ⟨e.1.trans rfl, e.2⟩
    rw [hy.2]
    exact ⟨hy.1, rfl, rfl, .inr (.inr ⟨n0, n1, rfl⟩)⟩

end Silmaril.Proofs.Wasm.JcoTool.KTee