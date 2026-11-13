module

public import Silmaril.Raw.Wasi.Versions.P2OverP3.FsRead

/-!
# Proofs (unrefined): the invariant after a read of a file stream

* `RdInv.read`: the invariant after a step that changes only the stream `h` (its 0.2 rest, the
  0.3 rest of its end `k`, whether it is closed and live), when the new rests agree.
* `wp_fsRead`: `read`/`blocking-read` of a live, open file stream keeps the invariant.

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

variable {F : BitVec 32 → List (BitVec 8)}

/-- **The invariant after a step on the live file stream `h`** (with the readable end `k`). -/
theorem RdInv.read {s s' : StF} {q2 q2' q3 q3' : RdSt} {h : BitVec 32} {e : FEnt} {k : Nat}
    (hI : RdInv s q2 q3) (he : s.fs h = some e) (hl : e.live = true) (hk : natOf e.r = some k)
    (hfs : s'.fs = s.fs ∨ s'.fs = fsUpd s.fs h (some { e with live := false }))
    (hc : ∀ h', s'.io.closed h' = true → s.io.closed h' = true ∨ h' = h)
    (hch : s'.io.closed h = true → s'.fs h = some { e with live := false })
    (h2 : ∀ h', h' ≠ h → rest q2' h'.toNat = rest q2 h'.toNat)
    (h3 : ∀ k', k' ≠ k → rest q3' k' = rest q3 k')
    (hn : rest q2 h.toNat = none → rest q2' h.toNat = none)
    (hs : ∀ bs, rest q2 h.toNat = some bs → ∃ bs', rest q2' h.toNat = some bs' ∧
      rest q3' k = some bs' ∧ (s'.io.closed h = true → bs' = [])) : RdInv s' q2' q3' where
  known := fun h' hh => by
    by_cases hx : h' = h
    · subst hx
      rcases hfs with hf | hf
      · rw [hf, he]; simp
      · rw [hf]; simp [fsUpd]
    · have h0 := hI.known h' (by rw [← h2 h' hx]; exact hh)
      rcases hfs with hf | hf
      · rw [hf]; exact h0
      · rw [hf]; simpa [fsUpd, hx] using h0
  rel := fun h' e' bs he' hb => by
    by_cases hx : h' = h
    · subst hx
      have he'' : e' = e ∨ e' = { e with live := false } := by
        rcases hfs with hf | hf
        · rw [hf, he] at he'; cases he'; exact .inl rfl
        · rw [hf] at he'; simp only [fsUpd, ite_true, Option.some.injEq] at he'
          exact .inr he'.symm
      cases hq : rest q2 h'.toNat with
      | none => rw [hn hq] at hb; exact absurd hb (by simp)
      | some bs0 =>
        obtain ⟨bs', hb', hk', hcl⟩ := hs bs0 hq
        rw [hb'] at hb
        cases hb
        refine ⟨fun hne => ?_, fun hl' => ?_⟩
        · cases hx : s'.io.closed h'
          · rfl
          · exact absurd (hcl hx) hne
        · have hopen : s'.io.closed h' = false := by
            cases hx : s'.io.closed h'
            · rfl
            · have := hch hx
              rw [this] at he'
              cases he'
              exact absurd hl' (by simp)
          refine ⟨hopen, k, ?_, hk'⟩
          rcases he'' with rfl | rfl
          · exact hk
          · exact hk
    · have he0 : s.fs h' = some e' := by
        rcases hfs with hf | hf
        · rw [← hf]; exact he'
        · rw [hf] at he'; simpa [fsUpd, hx] using he'
      rw [h2 h' hx] at hb
      have hopen : s.io.closed h' = false → s'.io.closed h' = false := fun hf => by
        cases hy : s'.io.closed h'
        · rfl
        · rcases hc h' hy with hz | hz
          · rw [hf] at hz; exact absurd hz (by decide)
          · exact absurd hz hx
      obtain ⟨hA, hB⟩ := hI.rel h' e' bs he0 hb
      refine ⟨fun hne => hopen (hA hne), fun hl' => ?_⟩
      obtain ⟨hcf, k0, hk0, hr⟩ := hB hl'
      have hne : k0 ≠ k := fun hkk => hx (hI.uniq h' h e' e k0 he0 he hl' hl hk0 (hkk ▸ hk))
      exact ⟨hopen hcf, k0, hk0, (h3 k0 hne).trans hr⟩
  uniq := fun h1 h2 e1 e2 k' he1 he2 hl1 hl2 hk1 hk2 => by
    have back : ∀ x e', s'.fs x = some e' → e'.live = true → s.fs x = some e' := fun x e' hx hl' => by
      rcases hfs with hf | hf
      · rw [← hf]; exact hx
      · rw [hf] at hx
        by_cases hxh : x = h
        · subst hxh
          simp only [fsUpd, ite_true, Option.some.injEq] at hx
          subst hx; exact absurd hl' (by simp)
        · simpa [fsUpd, hxh] using hx
    exact hI.uniq h1 h2 e1 e2 k' (back h1 e1 he1 hl1) (back h2 e2 he2 hl2) hl1 hl2 hk1 hk2
  keyed := fun x e' hx hl' => by
    rcases hfs with hf | hf
    · exact hI.keyed x e' (hf ▸ hx) hl'
    · rw [hf] at hx
      by_cases hxh : x = h
      · subst hxh
        simp only [fsUpd, ite_true, Option.some.injEq] at hx
        subst hx; exact absurd hl' (by simp)
      · exact hI.keyed x e' (by simpa [fsUpd, hxh] using hx) hl'

/-! ## The read path -/

theorem rdAns_err {len : Nat} {x : RdRes} (h : isErrAns (rdAns false len x) = true) : x = .eof := by
  cases x with
  | data bs => exact absurd h (by simp [rdAns, okBytes, okV, isErrAns])
  | eof => rfl
  | blocked => exact absurd h (by simp [rdAns, okBytes, okV, isErrAns])

theorem isRead_mem : isRead ∈ exp2 := by simp [exp2, ioImports_eq]
theorem isBread_mem : isBread ∈ exp2 := by simp [exp2, ioImports_eq]

/-- **`read`/`blocking-read` of a live, open file stream keeps the invariant.** -/
theorem wp_fsRead {s : StF} {f : FnName} {a : List Val} {g : Option (BitVec 64)} {q2 : RdSt}
    {qT : ClockSt × RdSt} {e : FEnt} (blocking : Bool) (hJ : JF s qT ((s.io, g, (), ()), q2))
    (he : s.fs (selfOf a) = some e) (hl : e.live = true) (hcl : s.io.closed (selfOf a) = false)
    (hu : u32Head a = true) (hf : f = isRead ∨ f = isBread) :
    Wp (t3F F) (fsReadP s (selfOf a) e (lenOf a) blocking) (PostF F s f a g q2) qT := by
  obtain ⟨-, hclk, hI⟩ := hJ
  obtain ⟨k, hk⟩ := hI.keyed _ e he hl
  have hop : ioOp f = .read ∨ ioOp f = .bread := by
    rcases hf with rfl | rfl
    · exact .inl (by decide)
    · exact .inr (by decide)
  have hmem : f ∈ exp2 := by rcases hf with rfl | rfl; exact isRead_mem; exact isBread_mem
  have hn : f ≠ clockNow := by rcases hf with rfl | rfl <;> decide
  have hfr : f ≠ fdReadStream := by rcases hf with rfl | rfl <;> decide
  have hother : ioOp f ≠ .other := by rcases hop with h | h <;> rw [h] <;> decide
  have hread : Wp (t3F F) (if blocking then readLoopF rounds s.impl e.r (lenOf a)
      else (readOnce e.r (lenOf a)).bind fun x => .pure (s.impl, x))
      (fun x q' => RStep k (lenOf a) qT x.2 q') qT := by
    split
    · exact wp_readLoopF hk rounds s.impl qT
    · rw [Wp.bind]; exact Wp.mono (fun x q' hx => hx) (wp_readOnce hk qT)
  unfold fsReadP
  rw [Wp.bind]
  refine Wp.mono (fun x qT' hx => ?_) hread
  obtain ⟨st', res⟩ := x
  show PostF F s f a g q2 (st', afterRead s.fs (selfOf a) e res, rdAns false (lenOf a) res) qT'
  have hans : ansOk .loose s.io (ioOp f) a (rdAns false (lenOf a) res) = true := by
    rw [ansOk_read hop, sticky_open hcl, rdAns_bytes]; rfl
  have hp2 : p2Ok (.imp f a (rdAns false (lenOf a) res)) = true := by simp [p2Ok, hother]
  have hfsok := fsOk_of_mem hmem a (rdAns false (lenOf a) res)
  have hfs : afterRead s.fs (selfOf a) e res = s.fs ∨
      afterRead s.fs (selfOf a) e res = fsUpd s.fs (selfOf a) (some { e with live := false }) := by
    cases res <;> simp [afterRead]
  have hc : ∀ h', (ioUpd s.io (ioOp f) a (rdAns false (lenOf a) res)).closed h' = true →
      s.io.closed h' = true ∨ h' = selfOf a := fun h' hx => by
    rcases ioUpd_closed hx with h0 | ⟨h0, -, -⟩
    · exact .inl h0
    · exact .inr h0
  have hch : (ioUpd s.io (ioOp f) a (rdAns false (lenOf a) res)).closed (selfOf a) = true →
      afterRead s.fs (selfOf a) e res = fsUpd s.fs (selfOf a) (some { e with live := false }) := by
    intro hx
    rcases ioUpd_closed hx with h0 | ⟨-, -, herr⟩
    · rw [hcl] at h0; exact absurd h0 (by decide)
    · rw [rdAns_err herr]; rfl
  have hch' : (ioUpd s.io (ioOp f) a (rdAns false (lenOf a) res)).closed (selfOf a) = true →
      afterRead s.fs (selfOf a) e res (selfOf a) = some { e with live := false } := fun hx => by
    rw [hch hx]; simp [fsUpd]
  have hcleof : (ioUpd s.io (ioOp f) a (rdAns false (lenOf a) res)).closed (selfOf a) = true →
      res = .eof := fun hx => by
    rcases ioUpd_closed hx with h0 | ⟨-, -, herr⟩
    · rw [hcl] at h0; exact absurd h0 (by decide)
    · exact rdAns_err herr
  obtain ⟨h, t, ha⟩ : ∃ h t, a = .u32 h :: t := by
    match a, hu with
    | .u32 h :: t, _ => exact ⟨h, t, rfl⟩
  have hsel : selfOf a = h := by rw [ha]; rfl
  cases hq : rest q2 (selfOf a).toNat with
  | none =>
    refine ⟨_, p2F_step s.io g q2 q2 hans hp2 hfsok hn (rd2_untracked q2 a _ hfr hq), rfl,
      hx.1 g hclk, ?_⟩
    exact hI.read he hl hk hfs hc hch' (fun _ _ => rfl) hx.2.1 (fun _ => hq)
      (fun bs hb => absurd (hq ▸ hb) (by simp))
  | some bs =>
    obtain ⟨-, k0, hk0, hr⟩ := (hI.rel _ e bs he hq).2 hl
    rw [hk] at hk0
    cases hk0
    have hres := hx.2.2 bs hr
    have hfs' : f = isRead ∨ f = isBread := hf
    cases res with
    | data ys =>
      obtain ⟨hz, hr'⟩ := hres
      have hrd : rd2Step F q2 (.imp f a (rdAns false (lenOf a) (.data ys))) =
          some (setRest q2 (selfOf a).toNat (bs.drop (ys.take (lenOf a)).length)) := by
        rw [ha] at hq hz ⊢
        exact rd2_bytes q2 hfr hfs' hq hz
      refine ⟨_, p2F_step s.io g q2 _ hans hp2 hfsok hn hrd, rfl, hx.1 g hclk, ?_⟩
      refine hI.read he hl hk hfs hc hch' (fun h' hne => ?_) hx.2.1
        (fun hq' => absurd (hq ▸ hq') (by simp)) (fun bs0 hb0 => ?_)
      · rw [rest_setRest, ite_eq_right (toNat_ne hne)]
      · rw [hq] at hb0; cases hb0
        refine ⟨_, by rw [rest_setRest, ite_eq_left rfl], hr', fun hx' => ?_⟩
        exact absurd (hcleof hx') (by simp)
    | eof =>
      obtain ⟨hbs, hr'⟩ := hres
      subst hbs
      refine ⟨_, p2F_step s.io g q2 q2 hans hp2 hfsok hn (rd2_err q2 a hfr (.inr hq)), rfl,
        hx.1 g hclk, ?_⟩
      exact hI.read he hl hk hfs hc hch' (fun _ _ => rfl) hx.2.1
        (fun hq' => absurd (hq ▸ hq') (by simp)) (fun bs0 hb0 => by
          rw [hq] at hb0; cases hb0; exact ⟨[], hq, hr', fun _ => rfl⟩)
    | blocked =>
      have hrd : rd2Step F q2 (.imp f a (rdAns false (lenOf a) .blocked)) =
          some (setRest q2 (selfOf a).toNat (bs.drop ([] : List (BitVec 8)).length)) := by
        rw [ha] at hq ⊢
        exact rd2_bytes q2 hfr hfs' hq (by simp)
      refine ⟨_, p2F_step s.io g q2 _ hans hp2 hfsok hn hrd, rfl, hx.1 g hclk, ?_⟩
      refine hI.read he hl hk hfs hc hch' (fun h' hne => ?_) hx.2.1
        (fun hq' => absurd (hq ▸ hq') (by simp)) (fun bs0 hb0 => ?_)
      · rw [rest_setRest, ite_eq_right (toNat_ne hne)]
      · rw [hq] at hb0; cases hb0
        refine ⟨bs, by rw [rest_setRest, ite_eq_left rfl]; rfl, hres, fun hx' => ?_⟩
        exact absurd (hcleof hx') (by simp)

end Silmaril.Wasi.Versions.P2OverP3
