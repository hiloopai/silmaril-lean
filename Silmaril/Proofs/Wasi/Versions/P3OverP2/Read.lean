module

public import Silmaril.Proofs.Wasi.Versions.P3OverP2.ReadSr
public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Typed

/-!
# Proofs: WASI 0.3 over 0.2 satisfies the loose read theory

`read_sat`: under the 0.2 read theory `fsRead2 F`, every return of the component satisfies the
0.3 read theory `fsReadTh3w F`. The invariant is `RdJ`; `read-via-stream` (0.3) binds a fresh
readable end to the 0.2 stream of `read-via-stream` (0.2), so both theories record the same rest
`(F d).drop off`; `stream.read` is `wp_sr`; the other functions keep or kill bindings
(`DFrame`) and make no 0.2 read calls.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy blocked CopyResult Store)
open Silmaril.Wasi.Versions.P3

variable (F : BitVec 32 → List (BitVec 8))

/-- A `setRest` at the handle `0` keeps the invariant (the component never binds `0`). -/
theorem RdJ.zero {c : Core} {q2 q3 : RdSt} (h : RdJ c q2 q3) (bs : List (BitVec 8)) :
    RdJ c q2 (setRest q3 0 bs) := by
  have hne : ∀ r ib, c.inOf r = some ib → r ≠ 0 := fun r ib hr he =>
    absurd (h.bound r ib hr).1 (by omega)
  refine ⟨h.pos, fun r bs' hq => ?_, h.bound, fun r ib hr hf hm => ?_, fun r ib hr hf hm => ?_,
    fun r ib hr hf => ?_, h.uniq, fun r hr => ?_⟩
  · by_cases h0 : r = 0
    · exact Or.inl h0
    · rw [rest_setRest_ne _ _ h0] at hq; exact h.known r bs' hq
  · rw [rest_setRest_ne _ _ (hne r ib hr)]; exact h.live r ib hr hf hm
  · rw [rest_setRest_ne _ _ (hne r ib hr)]; exact h.eof r ib hr hf hm
  · rw [rest_setRest_ne _ _ (hne r ib hr)]; exact h.stdin r ib hr hf
  · rw [rest_setRest_ne _ _ (by have := h.pos; omega)]; exact h.fresh r hr

/-- Non-read programs under the 0.2 read theory. -/
theorem wp_thenFin {D : Type} {Q : St × Option (List Val) → RdSt → Prop} {q2 : RdSt}
    (p : NProg D) (g : D → St × Option (List Val)) (hQ : ∀ d, Q (g d) q2) :
    Wp (fsRead2 F) (thenFin p g) Q q2 :=
  (Wp.bind _ _ q2).2 (wp_emb (fsRead2 F) (fun q _ a n hf => rd2_nr F q hf a n) hQ p)

theorem finSw_ins (c : Core) (a : List Val) (d : Option Nat) : (finSw c a d).1.ins = c.ins := by
  unfold finSw; repeat' split
  all_goals rfl

theorem finFDropR_ins (c : Core) (a : List Val) : (finFDropR c a).ins = c.ins := by
  unfold finFDropR; repeat' split
  all_goals rfl

theorem finJoin_ins (c : Core) (a : List Val) : (finJoin c a).ins = c.ins := by
  unfold finJoin; repeat' split
  all_goals rfl

theorem finWsNew_ins (c : Core) : (finWsNew c).1.ins = c.ins := by
  unfold finWsNew; repeat' split
  all_goals rfl

theorem finWait_ins (c : Core) (a : List Val) (d : Option (Option Nat)) :
    (finWait c a d).1.ins = c.ins := by
  unfold finWait; repeat' split
  all_goals rfl

theorem finNew_ins (c : Core) : (finNew c).1.ins = c.ins := by
  unfold finNew; split <;> rfl

theorem finWvs_ins (c : Core) (a : List Val) (d : Option (BitVec 32)) :
    (finWvs c a d).1.ins = c.ins := by
  cases hr : c.room
  · rw [finWvs_noroom hr]
  · exact (finWvs_room hr a d).2.2.1

/-- `stream.drop-readable` keeps or kills bindings. -/
theorem finDropR_dframe (c : Core) (a : List Val) : DFrame c (finDropR c a) := by
  unfold finDropR
  split
  · rename_i r _
    dsimp only
    split
    · split
      · rename_i hst
        have h1 := DFrame.of_ins (c := c) (c' := { c with st := _ }) (astep_next hst) rfl
        exact h1.trans (DFrame.setDead _ _)
      · exact DFrame.setDead _ _
    · split
      · rename_i hst
        exact DFrame.of_ins (astep_next hst) rfl
      · exact DFrame.of_ins (Nat.le_refl _) rfl
  · exact DFrame.of_ins (Nat.le_refl _) rfl

/-- A frame with unchanged bindings. -/
theorem dframe_of {c c' : Core} (hf : Frame c c') (hi : c'.ins = c.ins) : DFrame c c' :=
  DFrame.of_ins hf.next hi

/-- `read-via-stream` with room: the 0.2 stream's contents are the 0.3 stream's. -/
theorem wp_read_rv_room (s : St) (d : BitVec 32) (off : BitVec 64) (q2 q3 : RdSt)
    (hJ : RdJ s.core q2 q3) (hroom : s.core.room = true) (ans : Option (List Val)) (q2' : RdSt)
    (hstep : (fsRead2 F).step q2 (.imp P2.fdReadStream [.u32 d, .u64 off] ans) = some q2') :
    ∃ q3', (fsReadTh3w F).step q3 (.imp readVia3 [.u32 d, .u64 off]
      (some [.record [natV (finRv s.core [.u32 d, .u64 off] ans).2.1,
        natV (finRv s.core [.u32 d, .u64 off] ans).2.2]])) = some q3' ∧
      RdJ (finRv s.core [.u32 d, .u64 off] ans).1 q2' q3' := by
  rw [rd2_rvs F q2 d off ans, Option.some.injEq] at hstep
  obtain ⟨h1, h2, -, -, -, -⟩ := finIn_room hroom true (isOf ans)
  have hl : s.core.st.next + 4 < 2 ^ 32 := room_lt hroom
  have hra : rvArgs [.u32 d, .u64 off] = some (d, off) := rfl
  simp only [finRv, hra, h1, h2]
  refine ⟨_, rd3_rv F q3 d off (by omega),
    hJ.finIn hroom true (isOf ans) ((F d).drop off.toNat) (fun k hk => ?_) (fun is _ his => ?_) (by simp)⟩
  · subst hstep
    split
    · rename_i is his
      exact rest_setRest_ne _ _ (hk is his)
    · rfl
  · subst hstep
    simp only [his]
    exact rest_setRest_eq _ _ _

/-- `read-via-stream`. -/
theorem wp_read_rv (s : St) (a : List Val) (q2 q3 : RdSt) (hJ : RdJ s.core q2 q3) :
    Wp (fsRead2 F) ((ioRv s.core a).bind fun d => .pure (done s.clk (let r := finRv s.core a d
      (r.1, some [.record [natV r.2.1, natV r.2.2]]))))
      (fun a' q2' => ∃ q3', (fsReadTh3w F).step q3 (.imp readVia3 a a'.2) = some q3' ∧
        RdJ a'.1.core q2' q3') q2 := by
  rw [Wp.bind]
  cases hra : rvArgs a with
  | none =>
    simp only [ioRv, hra]
    exact ⟨q3, rd3_rv_bad F q3 hra _, by simpa [done, finRv, hra] using hJ⟩
  | some p =>
    obtain ⟨d, off⟩ := p
    have ha : a = [.u32 d, .u64 off] := by
      match a, hra with
      | [.u32 _, .u64 _], h => simp only [rvArgs, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1, h.2]
    subst ha
    cases hroom : s.core.room
    · simp only [ioRv, hra, hroom]
      simp only [done, finRv, hra, finIn_noroom hroom]
      exact ⟨_, rd3_rv F q3 d off (by simp), hJ.zero _⟩
    · simp only [ioRv, hra, hroom, ite_true]
      exact fun ans q2' hstep => wp_read_rv_room F s d off q2 q3 hJ hroom ans q2' hstep

/-- `write-via-stream` does not decrease `next`. -/
theorem finWvs_next (c : Core) (a : List Val) (d : Option (BitVec 32)) :
    c.st.next ≤ (finWvs c a d).1.st.next := by
  cases hr : c.room
  · rw [finWvs_noroom hr]
  · rw [(finWvs_room hr a d).2.1]; omega

/-- The read part of a call, by class. -/
theorem wp_read' (s : St) (f : FnName) (hf : f ∈ p3World.imports) (a : List Val) (q2 q3 : RdSt)
    (hJ : RdJ s.core q2 q3) :
    Wp (fsRead2 F) (body s (⟨f, hf⟩, a)) (fun a' q2' => ∃ q3',
      (fsReadTh3w F).step q3 (.imp f a a'.2) = some q3' ∧ RdJ a'.1.core q2' q3') q2 := by
  have hcl : ∃ c, cls f = c ∧ c ≠ .other ∧ f = c.name := cls_cases hf
  obtain ⟨c, hc, hne, rfl⟩ := hcl
  cases c <;> simp only [body, hc]
  case other => exact absurd rfl hne
  case streamNew =>
    exact ⟨q3, rfl, hJ.dframe (dframe_of (finNew_frame _) (finNew_ins _))⟩
  case dropR => exact ⟨q3, rfl, hJ.dframe (finDropR_dframe _ _)⟩
  case futDropR =>
    exact ⟨q3, rfl, hJ.dframe (dframe_of (finFDropR_frame _ _) (finFDropR_ins _ _))⟩
  case wsNew => exact ⟨q3, rfl, hJ.dframe (dframe_of (finWsNew_frame _) (finWsNew_ins _))⟩
  case join => exact ⟨q3, rfl, hJ.dframe (dframe_of (finJoin_frame _ _) (finJoin_ins _ _))⟩
  case streamRead => exact wp_sr F s.core s.clk q2 q3 a hJ
  case readVia => exact wp_read_rv F s a q2 q3 hJ
  all_goals refine wp_thenFin F _ _ (fun d => ?_)
  case streamWrite =>
    exact ⟨q3, rfl, hJ.dframe (dframe_of (finSw_frame _ _ _) (finSw_ins _ _ _))⟩
  case dropW =>
    exact ⟨q3, rfl, hJ.dframe (DFrame.of_ins (finDropW_spec s.core a).1 (finDropW_spec s.core a).2.2.1)⟩
  case futRead => exact ⟨q3, rfl, hJ⟩
  case wait => exact ⟨q3, rfl, hJ.dframe (dframe_of (finWait_frame _ _ _) (finWait_ins _ _ _))⟩
  case wvs => exact ⟨q3, rfl, hJ.dframe (DFrame.of_ins (finWvs_next _ a d) (finWvs_ins _ _ _))⟩
  case stdin =>
    refine ⟨q3, rfl, ?_⟩
    simp only [done]
    cases hroom : s.core.room
    · rw [finIn_noroom hroom]; exact hJ
    · exact hJ.finIn hroom false d [] (fun _ _ => rfl) (fun _ h' => by cases h') (by simp)
  case now => exact ⟨q3, rfl, hJ⟩
  case waitFor => exact ⟨q3, rfl, hJ⟩
  case getDirs => exact ⟨q3, rfl, hJ⟩
  case openAt => exact ⟨q3, rfl, hJ⟩

/-- **The read part of a call**: the 0.3 theory accepts the answer, the invariant is kept. -/
theorem wp_read (s : St) (q : (nsig p3World.imports).Op) (q2 q3 : RdSt) (hJ : RdJ s.core q2 q3) :
    Wp (fsRead2 F) (body s q) (fun a q2' => ∃ q3', (fsReadTh3w F).step q3 (.imp q.1.1 q.2 a.2) =
      some q3' ∧ RdJ a.1.core q2' q3') q2 :=
  wp_read' F s q.1.1 q.1.2 q.2 q2 q3 hJ

/-- **The component satisfies the loose read theory** (for well-shaped calls, with zero-length
reads), under the 0.2 read theory over the same contents `F`. -/
theorem read_sat : (agP (fsRead2 F) (retG (fsReadTh3w F))).holds p3OverP2 :=
  ag_of_wpInv (J := fun s q2 q3 => RdJ s.core q2 q3)
    ⟨RdJ.init F, fun s q2 q3 q hJ => wp_read F s q q2 q3 hJ⟩

end Silmaril.Wasi.Versions.P3OverP2
