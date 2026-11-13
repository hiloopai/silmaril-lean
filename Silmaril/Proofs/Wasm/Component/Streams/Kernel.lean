module

public import Silmaril.Wasm.Component.Streams.Kernel.Defs
public import Silmaril.Wasm.Component.Streams.Chunks.Thms
public import Silmaril.Proofs.Wasm.Component.Streams.Spec

/-!
# Byte kernels: proofs

A simulation of transformers (`feed_sim`, `run_sim`, `runP_sim`): two transformers related by a
relation on their states that agrees on `done`, is preserved by steps on admissible inputs with
equal outputs, and gives equal flushes, have the same outputs so far and the same whole outputs.
Each kernel is related to its specification transformer this way.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Kernel

open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Kernel
open Silmaril.Proofs.Wasm.Component.Streams.Spec
open scoped Silmaril.Wasm.Component.Streams.Tr

variable {σ τ α β : Type}

/-- A simulation between two transformers, on the inputs satisfying `P`. -/
structure Sim (T : Tr σ α β) (U : Tr τ α β) (P : α → Prop) (R : σ → τ → Prop) : Prop where
  init : R T.init U.init
  done : ∀ s t, R s t → T.done s = U.done t
  step : ∀ s t a, R s t → P a → T.done s = false →
    R (T.step s a).1 (U.step t a).1 ∧ (T.step s a).2 = (U.step t a).2
  flush : ∀ s t, R s t → T.flush s = U.flush t

theorem feed_sim {T : Tr σ α β} {U : Tr τ α β} {P : α → Prop} {R : σ → τ → Prop}
    (h : Sim T U P R) (xs : List α) (hx : ∀ a ∈ xs, P a) (s : σ) (t : τ) (hr : R s t) :
    R (T.feed s xs).1 (U.feed t xs).1 ∧ (T.feed s xs).2 = (U.feed t xs).2 := by
  induction xs generalizing s t with
  | nil => exact ⟨hr, rfl⟩
  | cons a xs ih =>
    have hd := h.done s t hr
    by_cases hs : T.done s = true
    · have ht : U.done t = true := hd ▸ hs
      rw [feed_cons, feed_cons]
      simp only [hs, ht, ↓reduceIte]
      exact ⟨hr, trivial⟩
    · have hs' : T.done s = false := by simpa using hs
      have ht : U.done t = false := hd ▸ hs'
      obtain ⟨hr', ho⟩ := h.step s t a hr (hx a (List.mem_cons_self ..)) hs'
      obtain ⟨h1, h2⟩ := ih (fun b hb => hx b (List.mem_cons_of_mem _ hb)) _ _ hr'
      rw [feed_cons, feed_cons]
      simp only [hs', ht, Bool.false_eq_true, ↓reduceIte]
      exact ⟨h1, by rw [ho, h2]⟩

theorem run_sim {T : Tr σ α β} {U : Tr τ α β} {P : α → Prop} {R : σ → τ → Prop}
    (h : Sim T U P R) (xs : List α) (hx : ∀ a ∈ xs, P a) : T.run xs = U.run xs := by
  obtain ⟨h1, h2⟩ := feed_sim h xs hx T.init U.init h.init
  show (T.feed T.init xs).2 ++ T.flush (T.feed T.init xs).1 =
    (U.feed U.init xs).2 ++ U.flush (U.feed U.init xs).1
  rw [h2, h.flush _ _ h1]

theorem runP_sim {T : Tr σ α β} {U : Tr τ α β} {P : α → Prop} {R : σ → τ → Prop}
    (h : Sim T U P R) (xs : List α) (hx : ∀ a ∈ xs, P a) : T.runP xs = U.runP xs :=
  (feed_sim h xs hx T.init U.init h.init).2

/-! ## Arithmetic of the expressions -/

theorem lit_eval (s : KSt) (b n : Nat) (hn : n < M32) : (KExp.lit n).eval s b = n :=
  Nat.mod_eq_of_lt hn

theorem M32_pos : 256 < M32 := by decide

/-! ## The kernels -/

theorem sim_map (e : KExp) :
    Sim (kMap e).tr (Tr.map (fun b => e.eval ⟨0, []⟩ b % 256)) (fun _ => True)
      (fun s _ => s = ⟨0, []⟩) where
  init := by simp [KM.tr, kMap]
  done s t _ := by simp [KM.tr, kMap, Tr.map, KExp.eval]
  step s t a hr _ _ := by
    subst hr
    simp [KM.tr, kMap, Tr.map, KStmt.exec]
  flush s t _ := by simp [KM.tr, kMap, Tr.map, KStmt.exec]

theorem sim_filter (c : KExp) :
    Sim (kFilter c).tr (Tr.filter (fun b => c.eval ⟨0, []⟩ b != 0)) (fun b => b < 256)
      (fun s _ => s = ⟨0, []⟩) where
  init := by simp [KM.tr, kFilter]
  done s t _ := by simp [KM.tr, kFilter, Tr.filter, KExp.eval]
  step s t a hr ha _ := by
    subst hr
    by_cases hc : c.eval ⟨0, []⟩ a = 0 <;>
      simp [KM.tr, kFilter, Tr.filter, KStmt.exec, KExp.eval, hc, Nat.mod_eq_of_lt ha]
  flush s t _ := by simp [KM.tr, kFilter, Tr.filter, KStmt.exec]

theorem sim_take (n : Nat) (hn : n < M32) :
    Sim (kTake n).tr (Tr.take n) (fun b => b < 256) (fun s k => s = ⟨k, []⟩ ∧ k < M32) where
  init := by simp [KM.tr, kTake, Tr.take, Nat.mod_eq_of_lt hn, hn]
  done s k hr := by
    obtain ⟨rfl, -⟩ := hr
    by_cases hk : k = 0 <;> simp [KM.tr, kTake, Tr.take, KExp.eval, hk]
  step s k a hr ha hd := by
    obtain ⟨rfl, hk⟩ := hr
    have hk0 : k ≠ 0 := by
      intro h0
      subst h0
      simp [KM.tr, kTake, KExp.eval] at hd
    have h1 : (k + (M32 - 1 % M32)) % M32 = k - 1 := by
      have : 1 % M32 = 1 := Nat.mod_eq_of_lt (by decide)
      rw [this]
      have : k + (M32 - 1) = (k - 1) + M32 := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    refine ⟨⟨?_, by simp only [Tr.take]; omega⟩, ?_⟩
    · simp [KM.tr, kTake, Tr.take, KStmt.exec, KExp.eval, h1]
    · simp [KM.tr, kTake, Tr.take, KStmt.exec, KExp.eval, Nat.mod_eq_of_lt ha]
  flush s t _ := by simp [KM.tr, kTake, Tr.take, KStmt.exec]

/-- Cutting a separator-free buffer followed by one item. -/
theorem cut_free_snoc (sep : Nat → Bool) (buf : List Nat) (hb : ∀ y ∈ buf, sep y = false)
    (b : Nat) : cut sep (buf ++ [b]) = if sep b then ([buf], []) else ([], buf ++ [b]) := by
  induction buf with
  | nil => by_cases hs : sep b <;> simp [cut, hs]
  | cons a buf ih =>
    have ha : sep a = false := hb a (List.mem_cons_self ..)
    have ih' := ih (fun y hy => hb y (List.mem_cons_of_mem _ hy))
    simp only [List.cons_append, cut, ha, Bool.false_eq_true, ↓reduceIte]
    rw [ih']
    by_cases hs : sep b <;> simp [hs]

theorem feed_flatMap (g : α → List β) (u : Unit) (xs : List α) :
    (Tr.flatMap g).feed u xs = ((), xs.flatMap g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [feed_cons]
    have hd : (Tr.flatMap g).done u = false := rfl
    simp only [hd, Bool.false_eq_true, ↓reduceIte]
    rw [show (Tr.flatMap g).step u x = ((), g x) from rfl, ih]
    simp

theorem flatMap_done (g : α → List β) (u : Unit) : (Tr.flatMap g).done u = false := rfl

theorem flatMap_flush (g : α → List β) (u : Unit) : (Tr.flatMap g).flush u = [] := rfl

/-- The relation of `kLines nl` to `linesU nl`. -/
def LinesR (nl : Nat) (s : KSt) (t : (Unit × List Nat) × Unit) : Prop :=
  s.st = 0 ∧ s.buf = t.1.2 ∧ ∀ y ∈ s.buf, (y == nl) = false

theorem nl_mod (nl : Nat) (hnl : nl < 256) : nl % M32 = nl :=
  Nat.mod_eq_of_lt (by have := M32_pos; omega)

/-- A newline: the buffer is emitted and cleared. -/
theorem lines_step_nl (nl : Nat) (hnl : nl < 256) (s : KSt) (hst : s.st = 0)
    (hfree : ∀ y ∈ s.buf, (y == nl) = false) :
    LinesR nl ((kLines nl).tr.step s nl).1 ((linesU nl).step (((), s.buf), ()) nl).1 ∧
      ((kLines nl).tr.step s nl).2 = ((linesU nl).step (((), s.buf), ()) nl).2 := by
  have hc0 := cut_free_snoc (· == nl) s.buf hfree nl
  have hc : cut (· == nl) (s.buf ++ [nl]) = ([s.buf], []) := by
    simpa only [beq_self_eq_true, ↓reduceIte] using hc0
  have hnl' : nl % M32 = nl := nl_mod nl hnl
  simp [LinesR, KM.tr, kLines, linesU, Tr.comp, Tr.map, Tr.linesT, KStmt.exec, KExp.eval,
    feed_cons, feed_nil, hc, hnl', hst, Nat.mod_eq_of_lt hnl, feed_flatMap]

/-- Another byte: it is appended to the buffer. -/
theorem lines_step_other (nl : Nat) (hnl : nl < 256) (s : KSt) (hst : s.st = 0)
    (hfree : ∀ y ∈ s.buf, (y == nl) = false) (a : Nat) (ha : a < 256) (hb : a ≠ nl) :
    LinesR nl ((kLines nl).tr.step s a).1 ((linesU nl).step (((), s.buf), ()) a).1 ∧
      ((kLines nl).tr.step s a).2 = ((linesU nl).step (((), s.buf), ()) a).2 := by
  have hb' : (a == nl) = false := by simpa using hb
  have hc0 := cut_free_snoc (· == nl) s.buf hfree a
  have hc : cut (· == nl) (s.buf ++ [a]) = ([], s.buf ++ [a]) := by
    simpa only [hb', Bool.false_eq_true, ↓reduceIte] using hc0
  have hnl' : nl % M32 = nl := nl_mod nl hnl
  have hfree' : ∀ y, y ∈ s.buf ∨ y = a → ¬y = nl := by
    intro y hy
    rcases hy with hy | rfl
    · simpa using hfree y hy
    · exact hb
  simpa [LinesR, KM.tr, kLines, linesU, Tr.comp, Tr.map, Tr.linesT, KStmt.exec, KExp.eval,
    feed_cons, feed_nil, hc, hnl', hb, hst, Nat.mod_eq_of_lt ha, feed_flatMap] using hfree'

theorem lines_flush (nl : Nat) (hnl : nl < 256) (s : KSt) :
    (kLines nl).tr.flush s = (linesU nl).flush (((), s.buf), ()) := by
  have hnl' : nl % M32 = nl := nl_mod nl hnl
  by_cases he : s.buf = []
  · simp [KM.tr, kLines, linesU, Tr.comp, Tr.map, Tr.linesT, KStmt.exec, KExp.eval,
      he, feed_flatMap, feed_nil, flatMap_flush]
  · simp [KM.tr, kLines, linesU, Tr.comp, Tr.map, Tr.linesT, KStmt.exec, KExp.eval,
      he, feed_flatMap, feed_nil, flatMap_flush, hnl', Nat.mod_eq_of_lt hnl]

theorem lines_t_eq {s : KSt} {t : (Unit × List Nat) × Unit} (hbuf : s.buf = t.1.2) :
    t = (((), s.buf), ()) := by
  obtain ⟨⟨u, buf⟩, u'⟩ := t
  simp only at hbuf
  rw [hbuf]

theorem sim_lines (nl : Nat) (hnl : nl < 256) :
    Sim (kLines nl).tr (linesU nl) (fun b => b < 256) (LinesR nl) where
  init := by simp [LinesR, KM.tr, kLines, linesU, Tr.comp, Tr.map, Tr.linesT]
  done s t _ := by
    simp [KM.tr, kLines, linesU, Tr.comp, Tr.map, Tr.linesT, KExp.eval, flatMap_done]
  step s t a hr ha _ := by
    obtain ⟨hst, hbuf, hfree⟩ := hr
    rw [lines_t_eq hbuf]
    by_cases hb : a = nl
    · rw [hb]; exact lines_step_nl nl hnl s hst hfree
    · exact lines_step_other nl hnl s hst hfree a ha hb
  flush s t hr := by
    obtain ⟨-, hbuf, -⟩ := hr
    rw [lines_t_eq hbuf]
    exact lines_flush nl hnl s

theorem chunksOf_nil (n : Nat) : chunksOf n ([] : List α) = [] := by
  rw [chunksOf]
  simp

theorem chunksOf_full (n : Nat) (bs : List α) (hn : 0 < n) (hl : bs.length = n) :
    chunksOf n bs = [bs] := by
  have hne : bs ≠ [] := by
    intro h
    subst h
    simp at hl
    omega
  rw [chunksOf]
  simp only [hne, ↓reduceIte, Nat.pos_iff_ne_zero.1 hn]
  rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega), chunksOf_nil]

/-- The relation of `kRechunk n` to `rechunkU n`. -/
def RechunkR (n : Nat) (s : KSt) (t : (Unit × List Nat) × Unit) : Prop :=
  s.st = 0 ∧ s.buf = t.1.2 ∧ s.buf.length < n

/-- The byte that fills the buffer: the chunk is emitted. -/
theorem rechunk_step_full (n : Nat) (h1 : 0 < n) (h2 : n ≤ 255) (s : KSt) (hst : s.st = 0)
    (a : Nat) (ha : a < 256) (hl' : s.buf.length + 1 = n) :
    RechunkR n ((kRechunk n).tr.step s a).1 ((rechunkU n).step (((), s.buf), ()) a).1 ∧
      ((kRechunk n).tr.step s a).2 = ((rechunkU n).step (((), s.buf), ()) a).2 := by
  have hn' : n % M32 = n := Nat.mod_eq_of_lt (by have := M32_pos; omega)
  have ha' : a % 256 = a := Nat.mod_eq_of_lt ha
  have hl : (s.buf ++ [a]).length = n := by simpa using hl'
  have hk : n / n * n = n := by rw [Nat.div_self h1, Nat.one_mul]
  have hc : chunksOf n (List.take n (s.buf ++ [a])) = [s.buf ++ [a]] := by
    rw [List.take_of_length_le (by omega)]
    exact chunksOf_full n _ h1 hl
  have hout : ((kRechunk n).tr.step s a).2 = ((rechunkU n).step (((), s.buf), ()) a).2 := by
    simp [KM.tr, kRechunk, rechunkU, Tr.comp, Tr.map, Tr.rechunk, KStmt.exec, KExp.eval,
      feed_cons, feed_nil, hn', ha', hl', hk, feed_flatMap, hc]
    omega
  refine ⟨⟨?_, ?_, ?_⟩, hout⟩
  · simp [KM.tr, kRechunk, KStmt.exec, KExp.eval, hn', ha', hl', hst]
  · simp [KM.tr, kRechunk, rechunkU, Tr.comp, Tr.map, Tr.rechunk, KStmt.exec, KExp.eval,
      feed_cons, feed_nil, hn', ha', hl', hk]
  · simp [KM.tr, kRechunk, KStmt.exec, KExp.eval, hn', ha', hl', h1]

/-- A byte that does not fill the buffer: it is appended. -/
theorem rechunk_step_part (n : Nat) (h2 : n ≤ 255) (s : KSt) (hst : s.st = 0)
    (a : Nat) (ha : a < 256) (hlt : s.buf.length + 1 < n) :
    RechunkR n ((kRechunk n).tr.step s a).1 ((rechunkU n).step (((), s.buf), ()) a).1 ∧
      ((kRechunk n).tr.step s a).2 = ((rechunkU n).step (((), s.buf), ()) a).2 := by
  have hn' : n % M32 = n := Nat.mod_eq_of_lt (by have := M32_pos; omega)
  have ha' : a % 256 = a := Nat.mod_eq_of_lt ha
  have hk : (s.buf.length + 1) / n * n = 0 := by rw [Nat.div_eq_of_lt hlt, Nat.zero_mul]
  have hl' : s.buf.length + 1 ≠ n := by omega
  have hlen : ((kRechunk n).tr.step s a).1.buf.length < n := by
    simp [KM.tr, kRechunk, KStmt.exec, KExp.eval, hn', ha', hl']
    omega
  refine ⟨⟨?_, ?_, hlen⟩, ?_⟩
  · simp [KM.tr, kRechunk, KStmt.exec, KExp.eval, hn', ha', hl', hst]
  · simp [KM.tr, kRechunk, rechunkU, Tr.comp, Tr.map, Tr.rechunk, KStmt.exec, KExp.eval,
      feed_cons, feed_nil, hn', ha', hl', hk]
  · simp [KM.tr, kRechunk, rechunkU, Tr.comp, Tr.map, Tr.rechunk, KStmt.exec, KExp.eval,
      feed_cons, feed_nil, hn', ha', hl', hk, feed_flatMap, chunksOf_nil]

theorem rechunk_flush (n : Nat) (h2 : n ≤ 255) (s : KSt) (hlen : s.buf.length < n) :
    (kRechunk n).tr.flush s = (rechunkU n).flush (((), s.buf), ()) := by
  have hl : s.buf.length % 256 = s.buf.length := Nat.mod_eq_of_lt (by omega)
  by_cases he : s.buf = []
  · simp [KM.tr, kRechunk, rechunkU, Tr.comp, Tr.map, Tr.rechunk, KStmt.exec, KExp.eval,
      he, feed_flatMap, feed_nil, flatMap_flush]
  · simp [KM.tr, kRechunk, rechunkU, Tr.comp, Tr.map, Tr.rechunk, KStmt.exec, KExp.eval,
      he, hl, feed_flatMap, feed_nil, flatMap_flush]

theorem sim_rechunk (n : Nat) (h1 : 0 < n) (h2 : n ≤ 255) :
    Sim (kRechunk n).tr (rechunkU n) (fun b => b < 256) (RechunkR n) where
  init := by simp [RechunkR, KM.tr, kRechunk, rechunkU, Tr.comp, Tr.map, Tr.rechunk, h1]
  done s t _ := by
    simp [KM.tr, kRechunk, rechunkU, Tr.comp, Tr.map, Tr.rechunk, KExp.eval, flatMap_done]
  step s t a hr ha _ := by
    obtain ⟨hst, hbuf, hlen⟩ := hr
    rw [lines_t_eq hbuf]
    by_cases hl : s.buf.length + 1 = n
    · exact rechunk_step_full n h1 h2 s hst a ha hl
    · exact rechunk_step_part n h2 s hst a ha (by omega)
  flush s t hr := by
    obtain ⟨-, hbuf, hlen⟩ := hr
    rw [lines_t_eq hbuf]
    exact rechunk_flush n h2 s hlen

end Silmaril.Proofs.Wasm.Component.Streams.Kernel
