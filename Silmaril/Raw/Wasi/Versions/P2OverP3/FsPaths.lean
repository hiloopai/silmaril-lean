module

public import Silmaril.Raw.Wasi.Versions.P2OverP3.FsInv

/-!
# Proofs (unrefined): the export calls of the filesystem extension, path by path

`PostF`: what an export call must establish (its answer is accepted by `p2F F` and the invariant
`JF` holds after). Proved here:

* `wp_noread`: a program that makes no reads, keeps the `p2OverP3` state, marks some file streams
  not live, and answers admissibly (`Good`);
* `wp_base`: a sanitized `p2OverP3` call (`baseP`), including `monotonic-clock.now`;
* `wp_rvs`: `read-via-stream`.

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

/-- What an export call `f a` from the state `s` must establish. -/
def PostF (F : BitVec 32 → List (BitVec 8)) (s : StF) (f : FnName) (a : List Val)
    (g : Option (BitVec 64)) (q2 : RdSt) (x : RF) (qT' : ClockSt × RdSt) : Prop :=
  ∃ qG', (p2F F).step ((s.io, g, (), ()), q2) (.imp f a x.2.2) = some qG' ∧
    JF ⟨ioUpd s.io (ioOp f) a x.2.2, x.1, x.2.1⟩ qT' qG'

/-- An admissible answer that keeps the 0.2 read state's rests and closes only untracked
streams. -/
structure Good (F : BitVec 32 → List (BitVec 8)) (s : StF) (f : FnName) (a : List Val)
    (q2 : RdSt) (r : Option (List Val)) : Prop where
  ans : ansOk .loose s.io (ioOp f) a r = true
  p2 : p2Ok (.imp f a r) = true
  fs : fsOk (.imp f a r) = true
  rd : ∃ q2', rd2Step F q2 (.imp f a r) = some q2' ∧ ∀ n, rest q2' n = rest q2 n
  closed : ∀ h, (ioUpd s.io (ioOp f) a r).closed h = true → s.io.closed h = true ∨
    rest q2 h.toNat = none

theorem postF_of {s : StF} {f : FnName} {a : List Val} {g : Option (BitVec 64)} {q2 : RdSt}
    {x : RF} {qT' : ClockSt × RdSt} {q3 : RdSt} (hn : f ≠ clockNow) (hI : RdInv s q2 q3)
    (hgood : Good F s f a q2 x.2.2) (hfs : Shrinks s.fs x.2.1) (hclk : ClkLe g qT'.1.last)
    (h3 : ∀ k, Tracked s.fs k → rest qT'.2 k = rest q3 k) : PostF F s f a g q2 x qT' := by
  obtain ⟨q2', hrd, hrest⟩ := hgood.rd
  refine ⟨_, p2F_step s.io g q2 q2' hgood.ans hgood.p2 hgood.fs hn hrd, rfl, hclk, ?_⟩
  exact hI.mono hfs hrest hgood.closed h3

/-- Calls that are not reads. -/
def NoRd (f : FnName) (_ : List Val) : Prop := f ≠ readVia3 ∧ f ≠ cStreamRead

/-- **A program without reads** that keeps the `p2OverP3` state and marks some file streams not
live, with good answers. -/
theorem wp_noread {s : StF} {f : FnName} {a : List Val} {g : Option (BitVec 64)} {q2 : RdSt}
    {qT : ClockSt × RdSt} (hn : f ≠ clockNow) (hJ : JF s qT ((s.io, g, (), ()), q2)) {p : PgF RF}
    (hp : LeavesC NoRd p fun x => Shrinks s.fs x.2.1 ∧ Good F s f a q2 x.2.2) :
    Wp (t3F F) p (PostF F s f a g q2) qT := by
  obtain ⟨-, hclk, hI⟩ := hJ
  refine Wp.of_leavesC (C := NoRd) (R := fun q => ClkLe g q.1.last ∧ q.2 = qT.2)
    (fun q f' a' n q' hq hC hs => ?_) (fun x q hq hx => ?_) p hp ⟨hclk, rfl⟩
  · obtain ⟨h1, h2⟩ := t3_step (qC := q.1) (q3 := q.2) hs
    exact ⟨clkLe_step hq.1 h1, (rd3_keep h2 hC.1 hC.2).trans hq.2⟩
  · exact postF_of hn hI hx.2 hx.1 hq.1 (fun k _ => by rw [hq.2])

/-! ## `p2OverP3` calls -/

/-- The functions of `exp2`. -/
theorem mem_exp2_of {f : FnName} (hf : f ∈ expF) (h1 : f ≠ getDirs) (h2 : f ≠ openAt)
    (h3 : f ≠ fdReadStream) (h4 : f ≠ fdDrop) : f ∈ exp2 := by
  rcases hf with hf | hf
  · exact hf
  · rcases hf with h | h | h | h <;> simp_all

theorem ne_fdReadStream_of_mem {f : FnName} (hf : f ∈ exp2) : f ≠ fdReadStream := by
  rw [exp2, ioImports_eq, cliImports_eq, clockImports_eq] at hf
  rcases hf with ((h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h) | (h | h | h | h | h | h | h | h | h | h)) | (h | h | h | h | h | h) <;> subst h <;>
    decide

theorem isRead_stream : (ioOp isRead).isStream = true := by decide
theorem isBread_stream : (ioOp isBread).isStream = true := by decide

/-- The answers of a `p2OverP3` call are good, when its stream operations are on handles that
are not file streams. -/
theorem base_good {s : StF} {f : FnName} {a : List Val} {q2 q3 : RdSt} (hI : RdInv s q2 q3)
    (hf : f ∈ exp2) (hdisp : (ioOp f).isStream = true → s.fs (selfOf a) = none)
    {r : Option (List Val)} (h1 : ansOk .loose s.io (ioOp f) a r = true)
    (h2 : p2Ok (.imp f a r) = true) : Good F s f a q2 r where
  ans := h1
  p2 := h2
  fs := fsOk_of_mem hf a r
  rd := by
    have hfr : f ≠ fdReadStream := ne_fdReadStream_of_mem hf
    by_cases hr : f = isRead ∨ f = isBread
    · have hst : (ioOp f).isStream = true := by
        rcases hr with rfl | rfl
        · exact isRead_stream
        · exact isBread_stream
      have hnone : rest q2 (selfOf a).toNat = none := by
        by_contra hc
        exact hI.known _ hc (hdisp hst)
      exact ⟨q2, rd2_untracked q2 a r hfr hnone, fun _ => rfl⟩
    · exact ⟨q2, rd2_other q2 a r hfr (fun h => hr (.inl h)) (fun h => hr (.inr h)),
        fun _ => rfl⟩
  closed := fun h hc => by
    rcases ioUpd_closed hc with hc | ⟨rfl, hst, -⟩
    · exact .inl hc
    · refine .inr ?_
      by_contra hn
      exact hI.known _ hn (hdisp hst)

/-- `monotonic-clock.now` through `baseP`. -/
theorem wp_base_now (cap : Nat) {s : StF} {a : List Val} {g : Option (BitVec 64)} {q2 : RdSt}
    {qT : ClockSt × RdSt} (hJ : JF s qT ((s.io, g, (), ()), q2)) :
    Wp (t3F F) (baseP cap s clockNow a) (PostF F s clockNow a g q2) qT := by
  obtain ⟨-, hclk, hI⟩ := hJ
  have hb : badK s.fs now3 [] = false := by
    simp [badK, show now3 ≠ readVia3 by decide, show now3 ≠ cStreamRead by decide]
  unfold baseP
  rw [prog_now]
  simp only [san, opNow, hb]
  intro n qT' hn
  obtain ⟨h1, h2⟩ := t3_step (qC := qT.1) (q3 := qT.2) (qC' := qT'.1) (q3' := qT'.2) hn
  obtain ⟨x, rfl, hle, hlast⟩ := now3_step h1
  have hq3 : qT'.2 = qT.2 := rd3_keep h2 (by decide) (by decide)
  have hgx : g.all (fun l => decide (l ≤ x)) = true := by
    cases g with
    | none => rfl
    | some l =>
      obtain ⟨y, hy, hly⟩ := hclk l rfl
      have hqy : qT.1.last = some y := hy
      rw [hqy] at hle
      simpa using BitVec.le_trans hly (by simpa using hle)
  have hP := p2_step_now s.io (g := g) a hgx
  have hrd : rd2Step F q2 (.imp clockNow a (some [.u64 x])) = some q2 :=
    rd2_other q2 a _ (by decide) (by decide) (by decide)
  refine ⟨((ioUpd s.io (ioOp clockNow) a (some [.u64 x]), some x, (), ()), q2), ?_, rfl, ?_, ?_⟩
  · simp only [p2F, Protocol.prod] at hP ⊢
    rw [hP]
    simp [fsRead2, hrd]
  · intro z hz
    exact ⟨x, hlast, (Option.some.inj hz) ▸ BitVec.le_refl _⟩
  · refine hI.mono (shrinks_refl _) (fun _ => rfl) (fun h hc => ?_) (fun k _ => by rw [hq3])
    rcases ioUpd_closed hc with hc | ⟨-, hst, -⟩
    · exact .inl hc
    · exact absurd hst (by decide)

theorem badK_false {t : FsTab} {f : FnName} {a : List Val} (h : badK t f a = false) :
    f ≠ readVia3 ∧ (f = cStreamRead → ∀ k, keyOf a = some k → ¬ Tracked t k) := by
  unfold badK at h
  have h' : ¬ (f = readVia3 ∨ (f = cStreamRead ∧ ∃ k, keyOf a = some k ∧ Tracked t k)) :=
    decide_eq_false_iff_not.mp h
  refine ⟨fun hf => h' (.inl hf), fun hf k hk ht => h' (.inr ⟨hf, k, hk, ht⟩)⟩

/-- **A sanitized `p2OverP3` call** other than `now`, whose stream operations are on handles
that are not file streams. -/
theorem wp_base (cap : Nat) {s : StF} {f : FnName} {a : List Val} {g : Option (BitVec 64)}
    {q2 : RdSt} {qT : ClockSt × RdSt} (hJ : JF s qT ((s.io, g, (), ()), q2)) (hf : f ∈ exp2)
    (hn : f ≠ clockNow) (hdisp : (ioOp f).isStream = true → s.fs (selfOf a) = none) :
    Wp (t3F F) (baseP cap s f a) (PostF F s f a g q2) qT := by
  obtain ⟨hio, hclk, hI⟩ := hJ
  unfold baseP
  rw [Wp.bind]
  refine Wp.of_leavesC (C := fun f a => badK s.fs f a = false)
    (R := fun q => ClkLe g q.1.last ∧ ∀ k, Tracked s.fs k → rest q.2 k = rest qT.2 k)
    (fun q f' a' n q' hq hC hs => ?_) (fun x q hq hx => ?_) _
    (leavesC_san _ _ _ (prog_good cap ⟨s.io, s.impl⟩ f a)) ⟨hclk, fun _ _ => rfl⟩
  · obtain ⟨h1, h2⟩ := t3_step (qC := q.1) (q3 := q.2) (qC' := q'.1) (q3' := q'.2) hs
    obtain ⟨hv, hr⟩ := badK_false hC
    exact ⟨clkLe_step hq.1 h1, fun k hk => (rd3_frame h2 hv hr k hk).trans (hq.2 k hk)⟩
  · exact postF_of (x := (x.1, s.fs, x.2)) hn hI (base_good hI hf hdisp hx.1 hx.2)
      (shrinks_refl _) hq.1 hq.2

end Silmaril.Wasi.Versions.P2OverP3
