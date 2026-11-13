module

public import Silmaril.Servers.Core.Defs
public import Silmaril.Proofs.Servers.Core.Lin

/-!
# Proofs: the converse of `Hom.lin_trace`

If `h : A ⟶ B` sees every response of `A` (`h.resp` surjective), a trace of `B` whose view in
`A` is linearizable for `S` is linearizable for the translation `h.seq S`.

The annotated trace of `B` is built along the annotated trace of `A`: a handler run takes its
`B` request from the `B` monitor's pending request, and its `B` response from the first
response the `B` trace sends to that identity afterwards (`firstSend`); if none is sent, any
preimage of the `A` response. `future` shows that the response sent later is seen as the one
the handler run computed.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Core

open Silmaril.Servers

variable {A B : Sig} (h : Hom A B)

/-- The first response a trace sends to the identity `i`. -/
def firstSend (i : ReqId) : Trace B → Option B.Resp
  | [] => none
  | .send j s :: t => if j = i then some s else firstSend i t
  | .recv _ _ :: t => firstSend i t

theorem trace_eq_cons {t : Trace B} {e : Event A} {l : Trace A} (he : h.trace t = e :: l) :
    ∃ eB t', t = eB :: t' ∧ h.event eB = e ∧ h.trace t' = l := by
  cases t with
  | nil => cases he
  | cons eB t' =>
    simp only [Hom.trace, List.map_cons, List.cons.injEq] at he
    exact ⟨eB, t', rfl, he.1, he.2⟩

theorem trace_eq_nil {t : Trace B} (he : h.trace t = []) : t = [] := by
  cases t with
  | nil => rfl
  | cons => cases he

/-- The linearization monitor's step is deterministic. -/
theorem step_det {m x y : LMon A} {e : LEvent A} (hx : LMon.Step m e x) (hy : LMon.Step m e y) :
    x = y := by
  cases hx <;> cases hy <;> rfl

theorem lInv_step {m m' : LMon A} {e : LEvent A} (hI : LInv m) (hs : LMon.Step m e m') :
    LInv m' := by
  obtain ⟨hP, hR⟩ := hI
  cases hs with
  | @recv i r hreq =>
    have hri : m.ready i = none := by
      cases hr : m.ready i with
      | none => rfl
      | some s' => obtain ⟨r', hr'⟩ := hR i s' hr; rw [hr'] at hreq; cases hreq
    refine ⟨fun j r' hj => ?_, fun j s' hj => ?_⟩
    · by_cases hji : j = i
      · subst hji; simp at hj; subst hj; simp [hri]
      · simp [hji] at hj ⊢; exact hP j r' hj
    · by_cases hji : j = i
      · subst hji; rw [hri] at hj; cases hj
      · simp [hji]; exact hR j s' hj
  | @lin i r s hp =>
    obtain ⟨hreq, _⟩ := hP i r hp
    refine ⟨fun j r' hj => ?_, fun j s' hj => ?_⟩
    · by_cases hji : j = i
      · subst hji; simp at hj
      · simp [hji] at hj ⊢; exact hP j r' hj
    · by_cases hji : j = i
      · subst hji; exact ⟨r, hreq⟩
      · simp [hji] at hj; exact hR j s' hj
  | @send i s hr =>
    refine ⟨fun j r' hj => ?_, fun j s' hj => ?_⟩
    · by_cases hji : j = i
      · subst hji
        have := (hP j r' hj).2; rw [this] at hr; cases hr
      · simp [hji]; exact hP j r' hj
    · by_cases hji : j = i
      · subst hji; simp at hj
      · simp [hji] at hj; exact hR j s' hj

theorem step_lmap {m m' : LMon B} {e : LEvent B} (hs : LMon.Step m e m') :
    LMon.Step (mmap h m) (lmap h e) (mmap h m') := by
  have := steps_lmap h (.cons hs (.nil _))
  cases this with
  | cons hs' hn => cases hn; exact hs'

theorem mmap_init : mmap h (LMon.init B) = LMon.init A := rfl

/-- **The response a handler run computes is the one sent later.** -/
theorem future {i : ReqId} {s : A.Resp} {mA mA' : LMon A} {t' : List (LEvent A)}
    (hs : Steps LMon.Step mA t' mA') :
    ∀ rest : Trace B, mA.ready i = some s → mA.pending i = none → mA.req i ≠ none →
      LEvent.erase t' = h.trace rest → ∀ sB, firstSend i rest = some sB → h.resp sB = s := by
  induction hs with
  | nil =>
    intro rest _ _ _ he sB hf
    rw [trace_eq_nil h he.symm] at hf; cases hf
  | @cons m₁ m₂ m₃ e es hst _ ih =>
    intro rest hr hp hq he sB hf
    cases hst with
    | @recv j r hreq =>
      have hji : j ≠ i := by rintro rfl; exact hq hreq
      obtain ⟨eB, rest', rfl, hev, hrest⟩ := trace_eq_cons h he.symm
      cases eB with
      | send => cases hev
      | recv j' rB =>
        exact ih rest' (by simpa using hr) (by simp [Function.update_of_ne hji.symm, hp])
          (by simp [Function.update_of_ne hji.symm, hq]) hrest.symm sB hf
    | @lin j r' s' hp' =>
      have hji : j ≠ i := by rintro rfl; rw [hp] at hp'; cases hp'
      exact ih rest (by simp [Function.update_of_ne hji.symm, hr])
        (by show Function.update m₁.pending j none i = none
            rw [Function.update_of_ne hji.symm]; exact hp) hq he sB hf
    | @send j s' hr' =>
      obtain ⟨eB, rest', rfl, hev, hrest⟩ := trace_eq_cons h he.symm
      cases eB with
      | recv => cases hev
      | send j' sB' =>
        simp only [Hom.event, Event.send.injEq] at hev
        obtain ⟨rfl, rfl⟩ := hev
        by_cases hji : j' = i
        · subst hji
          have hf' : sB' = sB := by simpa [firstSend] using hf
          subst hf'
          rw [hr] at hr'; cases hr'; rfl
        · simp only [firstSend, hji, ite_false] at hf
          exact ih rest' (by simp [Function.update_of_ne (Ne.symm hji), hr]) hp hq hrest.symm sB hf

/-- **The annotated trace of `B`**, built along the annotated trace of `A`. -/
theorem unmap (hsur : Function.Surjective h.resp) {mA mA' : LMon A} {tA : List (LEvent A)}
    (hs : Steps LMon.Step mA tA mA') :
    ∀ (mB : LMon B) (rest : Trace B), LInv mA → mmap h mB = mA →
      (∀ i b sB, mB.ready i = some b → firstSend i rest = some sB → b = sB) →
      LEvent.erase tA = h.trace rest →
      ∃ tB mB', Steps LMon.Step mB tB mB' ∧ LEvent.erase tB = rest ∧
        h.history (LEvent.lins tB) = LEvent.lins tA := by
  induction hs with
  | nil =>
    intro mB rest _ _ _ he
    exact ⟨[], mB, .nil _, (trace_eq_nil h he.symm).symm, rfl⟩
  | @cons m₁ m₂ m₃ e es hst hrest ih =>
    intro mB rest hI hm hinv he
    subst hm
    have hI₂ := lInv_step hI hst
    cases e with
    | ev e =>
      obtain ⟨eB, rest', rfl, hev, hrest'⟩ := trace_eq_cons h he.symm
      cases eB with
      | recv i rB =>
        subst hev
        have hreq : (mmap h mB).req i = none := by cases hst; assumption
        have hreqB : mB.req i = none := by simpa [mmap] using hreq
        have hB := LMon.Step.recv (r := rB) hreqB
        have h₂ := step_det hst (step_lmap h hB)
        subst h₂
        obtain ⟨tB, mB', hB', heB, hl⟩ := ih _ rest' hI₂ rfl (fun j b sB hb hf => hinv j b sB hb hf)
          hrest'.symm
        refine ⟨_, mB', .cons hB hB', ?_, ?_⟩
        · simp only [LEvent.erase, List.filterMap_cons] at heB ⊢; rw [heB]
        · simp only [LEvent.lins, List.filterMap_cons] at hl ⊢; exact hl
      | send i sB =>
        subst hev
        have hr : (mmap h mB).ready i = some (h.resp sB) := by cases hst; assumption
        obtain ⟨b, hb, -⟩ : ∃ b, mB.ready i = some b ∧ h.resp b = h.resp sB := by
          simpa [mmap] using hr
        have hbs := hinv i b sB hb (by simp [firstSend])
        subst hbs
        have hB := LMon.Step.send (i := i) hb
        have h₂ := step_det hst (step_lmap h hB)
        subst h₂
        obtain ⟨tB, mB', hB', heB, hl⟩ := ih _ rest' hI₂ rfl (fun j b' sB' hb' hf => by
          by_cases hji : j = i
          · subst hji; simp at hb'
          · simp only [Function.update_of_ne hji] at hb'
            exact hinv j b' sB' hb' (by simpa [firstSend, Ne.symm hji] using hf))
          hrest'.symm
        refine ⟨_, mB', .cons hB hB', ?_, ?_⟩
        · simp only [LEvent.erase, List.filterMap_cons] at heB ⊢; rw [heB]
        · simp only [LEvent.lins, List.filterMap_cons] at hl ⊢; exact hl
    | lin i r s =>
      have hp : (mmap h mB).pending i = some r := by cases hst; assumption
      obtain ⟨rB, hpB, hrB⟩ : ∃ rB, mB.pending i = some rB ∧ h.req rB = r := by
        simpa [mmap] using hp
      have hq : (mmap h mB).req i ≠ none := by rw [(hI.1 i r hp).1]; simp
      have he' : LEvent.erase es = h.trace rest := he
      -- the `B` response: the one sent later, or any preimage
      let b : B.Resp := match firstSend i rest with
        | some sB => sB
        | none => Classical.choose (hsur s)
      have hb : h.resp b = s := by
        cases hf : firstSend i rest with
        | none => simp only [b, hf]; exact Classical.choose_spec (hsur s)
        | some sB =>
          simp only [b, hf]
          have h₂ : LMon.Step (mmap h mB) (.lin i r s) _ := LMon.Step.lin hp
          have hd := step_det hst h₂
          subst hd
          exact future h hrest rest (by simp) (by simp) hq he' sB hf
      have hB := LMon.Step.lin (s := b) hpB
      have hmap : lmap h (.lin i rB b) = .lin i r s := by simp [lmap, hrB, hb]
      have h₂ := step_det hst (hmap ▸ step_lmap h hB)
      subst h₂
      obtain ⟨tB, mB', hB', heB, hl⟩ := ih _ rest hI₂ rfl (fun j b' sB' hb' hf => by
          by_cases hji : j = i
          · subst hji
            simp only [Function.update_self, Option.some.injEq] at hb'
            subst hb'
            simp only [b, hf]
          · simp only [Function.update_of_ne hji] at hb'
            exact hinv j b' sB' hb' hf)
        he'
      refine ⟨_, mB', .cons hB hB', ?_, ?_⟩
      · simp only [LEvent.erase, List.filterMap_cons] at heB ⊢; exact heB
      · have e₁ : LEvent.lins (LEvent.lin i rB b :: tB) = (rB, b) :: LEvent.lins tB := rfl
        have e₂ : LEvent.lins (LEvent.lin i r s :: es) = (r, s) :: LEvent.lins es := rfl
        rw [e₁, e₂, ← hl]; simp [Hom.history, hrB, hb]

/-- **The converse of `lin_trace`**, for a morphism that sees every response. -/
theorem lin_of_trace (hsur : Function.Surjective h.resp) {S : SeqSpec A} {t : Trace B}
    (hl : Sen.lin S (h.trace t)) : Sen.lin (h.seq S) t := by
  obtain ⟨t', ⟨m, hm⟩, he, hS⟩ := hl
  obtain ⟨tB, mB', hB, heB, hh⟩ := unmap h hsur hm (LMon.init B) t lInv_init (mmap_init h)
    (fun _ _ _ hb => nomatch hb) he
  exact ⟨tB, ⟨mB', hB⟩, heB, by show S (h.history _); rw [hh]; exact hS⟩

end Silmaril.Proofs.Servers.Core
