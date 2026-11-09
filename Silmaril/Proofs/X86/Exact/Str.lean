module

public import Silmaril.X86.Exact.Defs
public import Silmaril.X86.Loose.Thms

/-!
# Proofs: the string forms of `Σ v1` allow the results of `Str9`

The header is `Silmaril/X86/Exact/Thms.lean`.

* `tightens_of_sem`: a form that allows the result of an executor everywhere is tightened by
  the executor's exact form (when the executor's side condition always holds);
* `Span.sem_run`: the loose spec of a span allows the result of its reference executor
  `Span.run`, under `Span.Frame`;
* `execStr_eq`: `Str9.execStr i` is the reference executor of `strSpan i`, and `frame`: the
  string spans satisfy `Span.Frame`; so `sem_str`: **every string form of `Σ v1` allows the
  result of `Str9`**.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Exact

open Silmaril.X86 (State MState Word Byte Reg Flags)
open Silmaril.X86.Ext (loadN storeN leBytes)
open Silmaril.Process (Memory)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Str9 (Str execStr)
open Silmaril.X86.Loose
open Silmaril.X86.Loose.Forms.Str
open Silmaril.X86.Exact (FormSpec.exact)

variable {σ : Type}

/-- **From "allows the executor's result" to tightening.** -/
theorem tightens_of_sem {F : Silmaril.X86.Loose.FormSpec} {I : Isa σ} {i : I.Instr}
    (hok : ∀ c m l c' m', I.exec i c m l = .ok c' m' → I.ok i c')
    (h : ∀ c m l, F.sem c m l (I.exec i c m l)) : F.Tightens (FormSpec.exact I i) := by
  intro c m l res hres
  rcases hres with hu | ⟨c', m', rfl, hex, _, _⟩
  · rcases h c m l with hF | ⟨c', m', hex, ha⟩
    · exact Or.inl hF
    · exact absurd ⟨c', m', hex, hok _ _ _ _ _ hex, F.allows_fs ha⟩ hu
  · exact hex ▸ h c m l

/-! ## Spans -/

/-- The value of a register after the writes `ws.map (r, f r)`: `f r` if listed. -/
theorem regAfter_map (e : Effect) (c : State) (ws : List Reg) (f : Reg → Word)
    (he : e.regs = ws.map fun r => (r, f r)) (r : Reg) :
    e.regAfter c r = if r ∈ ws then f r else c.read r := by
  unfold Effect.regAfter
  rw [he]
  split
  · rename_i p hf
    have hm := List.mem_of_find?_eq_some hf
    have hp : p.1 = r := by simpa using List.find?_some hf
    rw [List.mem_reverse, List.mem_map] at hm
    obtain ⟨q, hq, rfl⟩ := hm
    simp only at hp
    subst hp
    simp [hq]
  · rename_i hf
    have : r ∉ ws := by
      intro hr
      have := List.find?_eq_none.1 hf (r, f r) (by simp [hr])
      simp at this
    simp [this]

theorem ofOpt_allows (v : Option Bool) (x : Option Bool) : (FlagP.ofOpt v).Allows x v := by
  cases v <;> trivial

theorem ofFlags_allows (f x : Flags) : (FlagEff.ofFlags f).Allows x f :=
  ⟨ofOpt_allows .., ofOpt_allows .., ofOpt_allows .., ofOpt_allows .., ofOpt_allows ..,
    ofOpt_allows ..⟩

theorem keepAll_allows (x : Flags) : FlagEff.keepAll.Allows x x :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Span.admits_of (S : Span) {c : State} {m m' : Memory} {l : Nat} {x : Word}
    (hF : S.Frame c l)
    (hw : writeAll m ((S.wr c l x).toList.map fun p => (p.1.toNat, leBytes p.2.2 p.2.1)) =
      some m') :
    (S.effOf c l x).Admits c m (S.post c l x) m' where
  rip := rfl
  regs r _ := by
    rw [regAfter_map _ c S.ws (fun r => (S.post c l x).read r) rfl]
    split
    · rfl
    · exact hF.regs x r (by assumption)
  flags := by
    unfold Span.effOf
    cases h : S.setsFlags
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hF.flags h x]; exact keepAll_allows _
    · simp only [↓reduceIte]
      exact ofFlags_allows _ _
  fsBase := hF.fsBase x
  mem := hw

theorem Span.sem_runOf (S : Span) {c : State} {m : Memory} {l : Nat} {x : Word}
    (hF : S.Frame c l) (hv : S.val c m l = x) :
    S.toEffSpec.toFormSpec.sem c m l (S.runOf c m l x) := by
  unfold Span.runOf
  split
  · rename_i a k v hw
    split
    · rename_i m' hs
      right
      refine ⟨_, _, rfl, ?_⟩
      show (S.eff c m l).Admits c m _ _
      unfold Span.eff
      rw [hv]
      apply Span.admits_of S hF
      simp only [hw, Option.toList_some, List.map_cons, List.map_nil, writeAll]
      simp only [storeN] at hs
      simp [hs]
    · rename_i hs
      left
      show S.unspecB c m l = true
      simp [Span.unspecB, hv, hw, hs]
  · rename_i hw
    right
    refine ⟨_, _, rfl, ?_⟩
    show (S.eff c m l).Admits c m _ _
    unfold Span.eff
    rw [hv]
    apply Span.admits_of S hF
    simp [hw, writeAll]

/-- **The loose spec of a span allows the result of its reference executor.** -/
theorem Span.sem_run (S : Span) {c : State} {m : Memory} {l : Nat} (hF : S.Frame c l) :
    S.toEffSpec.toFormSpec.sem c m l (S.run c m l) := by
  unfold Span.run
  split
  · rename_i a k hr
    split
    · rename_i x hx
      exact Span.sem_runOf S hF (by simp [Span.val, hr, hx])
    · rename_i hx
      left
      show S.unspecB c m l = true
      simp [Span.unspecB, hr, hx]
  · rename_i hr
    exact Span.sem_runOf S hF (by simp [Span.val, hr])

/-! ## The string forms -/

theorem execStr_eq (i : Str) (c : State) (m : Memory) (l : Nat) :
    execStr i c m (next c l) = (strSpan i).run c m l := by
  cases i
  · simp only [execStr, Span.run, Span.runOf, strSpan, movsbSpan]
    cases loadN m (c.read .rsi) 1 with
    | none => rfl
    | some v =>
      simp only
      cases storeN m (c.read .rdi) 1 v <;> rfl
  · simp only [execStr, Span.run, Span.runOf, strSpan, repMovsqSpan]
    by_cases h : c.read .rcx = 0
    · simp [h]
    · simp only [h, ↓reduceIte]
      cases loadN m (c.read .rsi) 8 with
      | none => rfl
      | some v =>
        simp only [Silmaril.X86.Str9.repElem]
        cases storeN m (c.read .rdi) 8 v <;> rfl
  · simp only [execStr, Span.run, Span.runOf, strSpan, repStosqSpan]
    by_cases h : c.read .rcx = 0
    · simp [h]
    · simp only [h, ↓reduceIte, Silmaril.X86.Str9.repElem]
      cases storeN m (c.read .rdi) 8 (c.read .rax) <;> rfl

theorem elemCore_read (src : Bool) (c : State) (nx : Word) (r : Reg) (h1 : r ≠ .rdi)
    (h2 : r ≠ .rcx) (h3 : src = true → r ≠ .rsi) : (elemCore src c nx).read r = c.read r := by
  unfold elemCore
  cases src
  · simp [State.read_write_other _ _ _ _ h1, State.read_write_other _ _ _ _ h2]
  · simp [State.read_write_other _ _ _ _ h1, State.read_write_other _ _ _ _ h2,
      State.read_write_other _ _ _ _ (h3 rfl)]

theorem frame (i : Str) (c : State) (l : Nat) : (strSpan i).Frame c l := by
  cases i
  · refine ⟨fun _ r hr => ?_, fun _ => rfl, fun _ _ => rfl⟩
    simp only [strSpan, movsbSpan, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [strSpan, movsbSpan]
    simp [State.read_write_other _ _ _ _ hr.1, State.read_write_other _ _ _ _ hr.2]
  · refine ⟨fun _ r hr => ?_, fun _ => ?_, fun _ _ => ?_⟩
    · simp only [strSpan, repMovsqSpan, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hr
      simp only [strSpan, repMovsqSpan]
      split
      · rfl
      · exact elemCore_read true c _ r hr.2.1 hr.2.2 fun _ => hr.1
    · simp only [strSpan, repMovsqSpan]
      split
      · rfl
      · simp [elemCore]
    · simp only [strSpan, repMovsqSpan]
      split
      · rfl
      · simp [elemCore]
  · refine ⟨fun _ r hr => ?_, fun _ => ?_, fun _ _ => ?_⟩
    · simp only [strSpan, repStosqSpan, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hr
      simp only [strSpan, repStosqSpan]
      split
      · rfl
      · exact elemCore_read false c _ r hr.1 hr.2 (by simp)
    · simp only [strSpan, repStosqSpan]
      split
      · rfl
      · simp [elemCore]
    · simp only [strSpan, repStosqSpan]
      split
      · rfl
      · simp [elemCore]

/-- **Every string form of `Σ v1` allows the result of `Str9`.** -/
theorem sem_str (i : Str) (c : State) (m : Memory) (l : Nat) :
    (strSpec i).toFormSpec.sem c m l (Silmaril.X86.Str9.exec (.str i) c m l) := by
  show (strSpan i).toEffSpec.toFormSpec.sem c m l (execStr i c m (next c l))
  rw [execStr_eq]
  exact Span.sem_run _ (frame i c l)

end Silmaril.Proofs.X86.Exact
