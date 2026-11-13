module

public import Silmaril.Proofs.Wasi.Versions.P2OverP3.FsWp
public import Silmaril.Wasi.Versions.P2OverP3.Comp.Thms

/-!
# Proofs (unrefined): the invariant of the filesystem extension

`RdInv s q2 q3` relates the component's file streams `s.fs` to the states `q2` of the 0.2 read
theory `fsRead2 F` and `q3` of the 0.3 read theory `fsReadTh3w F`:

* (`known`) a stream the 0.2 theory tracks is in the table;
* (`rel`) a tracked stream with bytes left is not closed, and a **live** tracked stream is not
  closed and has the same bytes left on its 0.3 readable end;
* (`uniq`) two live file streams have different readable ends;
* (`keyed`) the readable end of a live file stream is a `u32` handle.

`JF` adds the `wasi:io` record and the clock (as `J` of `p2OverP3`). Lemmas: the steps of the 0.2
theories on the component's answers (`p2F_step`, `rd2_*`), the closed streams after an answer
(`ioUpd_closed`), and `RdInv.mono` (the invariant survives a step that keeps the table, the 0.2
rests and the 0.3 rests of live ends, and closes only untracked streams).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Versions.P2
open Silmaril.Wasi.Versions.P3OverP2 (fsReadTh3w fsRead2 rd2Step)

/-! ## The invariant -/

/-- The read invariant. -/
structure RdInv (s : StF) (q2 q3 : RdSt) : Prop where
  known : ∀ h : BitVec 32, rest q2 h.toNat ≠ none → s.fs h ≠ none
  rel : ∀ h e bs, s.fs h = some e → rest q2 h.toNat = some bs →
    (bs ≠ [] → s.io.closed h = false) ∧
    (e.live = true → s.io.closed h = false ∧ ∃ k, natOf e.r = some k ∧ rest q3 k = some bs)
  uniq : ∀ h1 h2 e1 e2 k, s.fs h1 = some e1 → s.fs h2 = some e2 → e1.live = true →
    e2.live = true → natOf e1.r = some k → natOf e2.r = some k → h1 = h2
  keyed : ∀ h e, s.fs h = some e → e.live = true → ∃ k, natOf e.r = some k

/-- The invariant of the component. -/
def JF (s : StF) (qT : ClockSt × RdSt) (qG : P2St × RdSt) : Prop :=
  qG.1.1 = s.io ∧ ClkLe qG.1.2.1 qT.1.last ∧ RdInv s qG.2 qT.2

theorem rdInv_init : RdInv StF.init [] [] where
  known := fun _ h => absurd rfl h
  rel := fun _ _ _ h => nomatch h
  uniq := fun _ _ _ _ _ h => nomatch h
  keyed := fun _ _ h => nomatch h

/-! ## Closed streams -/

theorem markReady_closed (s : IoSt) (p : BitVec 32) : (markReady s p).closed = s.closed := by
  unfold markReady; split <;> rfl

theorem foldl_markReady_closed (ps : List (BitVec 32)) (s : IoSt) :
    (ps.foldl markReady s).closed = s.closed := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih => rw [List.foldl_cons, ih, markReady_closed]

theorem ioUpd_closed {io : IoSt} {o : IoOp} {a : List Val} {r : Option (List Val)} {h : BitVec 32}
    (hc : (ioUpd io o a r).closed h = true) :
    io.closed h = true ∨ (h = selfOf a ∧ o.isStream = true ∧ isErrAns r = true) := by
  have hcl : (ioUpd io o a r).closed = (closeOn io o (selfOf a) r).closed := by
    unfold ioUpd
    split <;> (try split) <;> (try rfl) <;> simp only [markReady_closed, foldl_markReady_closed]
  rw [hcl] at hc
  unfold closeOn at hc
  split at hc
  · next hs =>
    simp only [upd] at hc
    by_cases hh : h = selfOf a
    · simp only [Bool.and_eq_true] at hs
      exact .inr ⟨hh, hs.1, hs.2⟩
    · rw [ite_eq_right hh] at hc; exact .inl hc
  · exact .inl hc

/-- The table `t'` is `t` with some streams marked not live. -/
def Shrinks (t t' : FsTab) : Prop :=
  ∀ h, t' h = t h ∨ ∃ e, t h = some e ∧ t' h = some { e with live := false }

theorem shrinks_refl (t : FsTab) : Shrinks t t := fun _ => .inl rfl

theorem shrinks_kill (t : FsTab) {h : BitVec 32} {e : FEnt} (he : t h = some e) :
    Shrinks t (fsUpd t h (some { e with live := false })) := fun x => by
  by_cases hx : x = h
  · subst hx; exact .inr ⟨e, he, by simp [fsUpd]⟩
  · exact .inl (by simp [fsUpd, hx])

/-- **The invariant survives** a step that marks some streams not live, keeps the 0.2 rests and
the 0.3 rests of live ends, and closes only streams the 0.2 read theory does not track. -/
theorem RdInv.mono {s s' : StF} {q2 q2' q3 q3' : RdSt} (hI : RdInv s q2 q3)
    (hfs : Shrinks s.fs s'.fs) (h2 : ∀ n, rest q2' n = rest q2 n)
    (hc : ∀ h, s'.io.closed h = true → s.io.closed h = true ∨ rest q2 h.toNat = none)
    (h3 : ∀ k, Tracked s.fs k → rest q3' k = rest q3 k) : RdInv s' q2' q3' where
  known := fun h hh => by
    have hk := hI.known h (h2 _ ▸ hh)
    rcases hfs h with he | ⟨e, he, he'⟩
    · rw [he]; exact hk
    · rw [he']; simp
  rel := fun h e' bs he' hb => by
    rw [h2] at hb
    have hcl : s.io.closed h = false → s'.io.closed h = false := fun hf => by
      cases hx : s'.io.closed h
      · rfl
      · rcases hc h hx with hy | hy
        · rw [hf] at hy; exact absurd hy (by decide)
        · rw [hb] at hy; exact absurd hy (by simp)
    rcases hfs h with heq | ⟨e, he, hk⟩
    · rw [heq] at he'
      obtain ⟨hA, hB⟩ := hI.rel h e' bs he' hb
      refine ⟨fun hne => hcl (hA hne), fun hl => ?_⟩
      obtain ⟨hcf, k, hk, hr⟩ := hB hl
      exact ⟨hcl hcf, k, hk, (h3 k ⟨h, e', he', hl, hk⟩).trans hr⟩
    · rw [hk] at he'
      cases he'
      exact ⟨fun hne => hcl ((hI.rel h e bs he hb).1 hne), fun hl => absurd hl (by simp)⟩
  uniq := fun h1 h2 e1 e2 k he1 he2 hl1 hl2 => by
    have hb1 : s.fs h1 = some e1 := by
      rcases hfs h1 with heq | ⟨e, -, hk⟩
      · exact heq ▸ he1
      · rw [hk] at he1; cases he1; exact absurd hl1 (by simp)
    have hb2 : s.fs h2 = some e2 := by
      rcases hfs h2 with heq | ⟨e, -, hk⟩
      · exact heq ▸ he2
      · rw [hk] at he2; cases he2; exact absurd hl2 (by simp)
    exact hI.uniq h1 h2 e1 e2 k hb1 hb2 hl1 hl2
  keyed := fun h e he hl => by
    rcases hfs h with heq | ⟨e0, -, hk⟩
    · exact hI.keyed h e (heq ▸ he) hl
    · rw [hk] at he; cases he; exact absurd hl (by simp)

/-! ## The 0.2 read theory on the component's answers -/

theorem rd2_other {F : BitVec 32 → List (BitVec 8)} (q : RdSt) {f : FnName} (a : List Val)
    (r : Option (List Val)) (h1 : f ≠ fdReadStream) (h2 : f ≠ isRead) (h3 : f ≠ isBread) :
    rd2Step F q (.imp f a r) = some q := by
  have h23 : ¬ (f = isBread ∨ f = isRead) := fun h => h.elim h3 h2
  simp [rd2Step, h1, h23]

/-- A read of a stream the 0.2 theory does not track. -/
theorem rd2_untracked {F : BitVec 32 → List (BitVec 8)} (q : RdSt) {f : FnName} (a : List Val)
    (r : Option (List Val)) (h1 : f ≠ fdReadStream) (hn : rest q (selfOf a).toNat = none) :
    rd2Step F q (.imp f a r) = some q := by
  unfold rd2Step
  dsimp only
  rw [ite_eq_right h1]
  split
  · split
    · next is t =>
      have hs : selfOf (.u32 is :: t) = is := rfl
      rw [hs] at hn
      rw [hn]
    · rfl
  · rfl

/-- An error of a read of a stream with nothing left. -/
theorem rd2_err {F : BitVec 32 → List (BitVec 8)} (q : RdSt) {f : FnName} (a : List Val)
    (h1 : f ≠ fdReadStream) (hn : rest q (selfOf a).toNat = none ∨ rest q (selfOf a).toNat = some []) :
    rd2Step F q (.imp f a errAns) = some q := by
  rcases hn with hn | hn
  · exact rd2_untracked q a _ h1 hn
  unfold rd2Step
  dsimp only
  rw [ite_eq_right h1]
  split
  · split
    · next is t =>
      have hs : selfOf (.u32 is :: t) = is := rfl
      rw [hs] at hn
      simp [hn, errAns, errClosed, errV]
    · rfl
  · rfl

theorem bytesOf_bytesV (bs : List (BitVec 8)) : bytesOf (bytesV bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [bytesOf, bytesV]

/-- Bytes of a read: a prefix of what is left. -/
theorem rd2_bytes {F : BitVec 32 → List (BitVec 8)} (q : RdSt) {f : FnName} {h : BitVec 32}
    {t : List Val} {bs z : List (BitVec 8)} (h1 : f ≠ fdReadStream) (hf : f = isRead ∨ f = isBread)
    (hq : rest q h.toNat = some bs) (hz : z = bs.take z.length) :
    rd2Step F q (.imp f (.u32 h :: t) (okBytes z)) =
      some (setRest q h.toNat (bs.drop z.length)) := by
  have hf' : f = isBread ∨ f = isRead := hf.symm
  simp only [rd2Step, ite_eq_right h1, ite_eq_left hf', hq, okBytes, okV, bytesOf_bytesV]
  rw [ite_eq_left hz]

/-- The step of `p2F F` on an answer of a function other than `now`. -/
theorem p2F_step {F : BitVec 32 → List (BitVec 8)} {f : FnName} {a : List Val}
    {r : Option (List Val)} (io : IoSt) (g : Option (BitVec 64)) (q2 q2' : RdSt)
    (h1 : ansOk .loose io (ioOp f) a r = true) (h2 : p2Ok (.imp f a r) = true)
    (h3 : fsOk (.imp f a r) = true) (hn : f ≠ clockNow) (h4 : rd2Step F q2 (.imp f a r) = some q2') :
    (p2F F).step ((io, g, (), ()), q2) (.imp f a r) =
      some ((ioUpd io (ioOp f) a r, g, (), ()), q2') := by
  have hs := p2_step io g h1 h2 h3 hn
  simp only [p2F, Protocol.prod] at hs ⊢
  rw [hs]
  simp [fsRead2, h4]

end Silmaril.Wasi.Versions.P2OverP3
