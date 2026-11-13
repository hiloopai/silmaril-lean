module

public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Inv

/-!
# The checked semantics refines `dexec`

`bexec_dexec`: where `bexec nl` is defined, it is `KDrop.dexec` (`cev_eval` for expressions,
`bcall_dcall` for the built-in calls, `dloopN_mono` for loops).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun

open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (E S BI Out M32 upd)
open Silmaril.Wasm.JcoTool.KDrop (DSt dexec dcallBI)
open Silmaril.Wasm.Component.Streams.Drop (dstep)

variable {nl : Nat}

theorem bi_dcall {b : BI} {as : List Nat} {s : DSt} {q' : HQ} {m' : Nat → Nat} {res : List Nat}
    {dst : List Nat} (h : bi b as (s.st, s.rp) s.m = some (q', m', res)) (hl : dst.length = res.length) :
    dcallBI b as dst s = some (.norm, { s with st := q'.1, rp := q'.2, m := m', l := setLs s.l dst res }) := by
  unfold bi at h
  split at h
  · rename_i hd p n
    split at h
    · rename_i st' code xs hds
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨d, rfl⟩ : ∃ d, dst = [d] := by
          match dst, hl with
          | [d], _ => exact ⟨d, rfl⟩
        simp only [dcallBI, hds, hc, and_self, ↓reduceIte]
        rfl
      · cases h
    · rename_i st' r hds
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨d, rfl⟩ : ∃ d, dst = [d] := by
          match dst, hl with
          | [d], _ => exact ⟨d, rfl⟩
        simp only [dcallBI, hds, hc, ↓reduceIte]
        rfl
      · cases h
    · cases h
  · rename_i hd p n
    split at h
    · rename_i st' r hds
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨d, rfl⟩ : ∃ d, dst = [d] := by
          match dst, hl with
          | [d], _ => exact ⟨d, rfl⟩
        simp only [dcallBI, hds, hc, ↓reduceIte]
        rfl
      · cases h
    · cases h
  · rename_i hd
    cases hds : dstep s.st (.streamDropR hd) with
    | none => rw [hds] at h; cases h
    | some p =>
      rw [hds] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain rfl : dst = [] := List.eq_nil_of_length_eq_zero hl
      simp only [dcallBI, hds, Option.map_some]
      rfl
  · rename_i hd
    cases hds : dstep s.st (.streamDropW hd) with
    | none => rw [hds] at h; cases h
    | some p =>
      rw [hds] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain rfl : dst = [] := List.eq_nil_of_length_eq_zero hl
      simp only [dcallBI, hds, Option.map_some]
      rfl
  · cases h

theorem bcall_dcall {b : BI} {as dst : List Nat} {s : DSt} {r : Out × DSt}
    (h : bcall nl b as dst s = some r) : dcallBI b as dst s = some r := by
  unfold bcall at h
  split at h
  · split at h
    · rename_i q' m' res hbi
      split at h
      · rename_i hc
        rw [← h]
        exact bi_dcall hbi hc.1
      · cases h
    · cases h
  · cases h

theorem mapM_cev {s : DSt} : ∀ {args : List E} {as : List Nat}, args.mapM (cev nl s) = some as →
    as = args.map (·.eval s.down)
  | [], as, h => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; simp [← h]
  | e :: es, as, h => by
    simp only [List.mapM_cons] at h
    cases he : cev nl s e with
    | none => rw [he] at h; cases h
    | some a =>
      cases hs : es.mapM (cev nl s) with
      | none => rw [he, hs] at h; cases h
      | some as' =>
        rw [he, hs] at h
        have h' : a :: as' = as := Option.some.inj h
        rw [← h', cev_eval e he, mapM_cev hs]
        rfl

theorem dloopN_mono {b₁ b₂ : DSt → Option (Out × DSt)} (hb : ∀ s r, b₁ s = some r → b₂ s = some r) :
    ∀ (n : Nat) (s : DSt) (r : Out × DSt), dexec.dloopN b₁ n s = some r → dexec.dloopN b₂ n s = some r
  | 0, _, _, h => by simp [dexec.dloopN] at h
  | n + 1, s, r, h => by
    cases h₁ : b₁ s with
    | none => simp [dexec.dloopN, h₁] at h
    | some x =>
      have h₂ := hb s x h₁
      obtain ⟨o, s₁⟩ := x
      rcases o with _ | (_ | k) | v
      all_goals simp only [dexec.dloopN, h₁, h₂] at h ⊢
      all_goals first | exact h | exact dloopN_mono hb n s₁ r h

/-- **Where `bexec` is defined, it is `dexec`.** -/
theorem bexec_dexec : ∀ (S : S) (f : Nat) {s s' : DSt} {o : Out}, bexec nl S f s = some (o, s') →
    dexec S f s = some (o, s')
  | .nop, _, _, _, _, h => h
  | .unreachable, _, _, _, _, h => by simp [bexec] at h
  | .lset i e, f, s, s', o, h => by
    obtain ⟨-, v, hv, rfl, rfl⟩ := bexec_lset h
    rw [cev_eval e hv]; rfl
  | .gset i e, f, s, s', o, h => by
    obtain ⟨-, v, hv, rfl, rfl⟩ := bexec_gset h
    rw [cev_eval e hv]; rfl
  | .st8 a v, f, s, s', o, h => by
    obtain ⟨x, y, hx, hy, -, rfl, rfl⟩ := bexec_st8 h
    rw [cev_eval a hx, cev_eval v hy]; rfl
  | .mcopy d src n, f, s, s', o, h => by
    obtain ⟨x, y, z, hx, hy, hz, -, -, rfl, rfl⟩ := bexec_mcopy h
    rw [cev_eval d hx, cev_eval src hy, cev_eval n hz]; rfl
  | .seq a b, f, s, s', o, h => by
    obtain ⟨o₁, s₁, ha, hc⟩ := bexec_seq h
    have ha' : dexec a f s = some (o₁, s₁) := bexec_dexec a f ha
    rcases hc with ⟨rfl, hb⟩ | ⟨hn, ho, hs⟩
    · simp only [dexec, ha', bexec_dexec b f hb]
    · rw [ho, hs]
      rcases o₁ with _ | k | v
      · exact absurd rfl hn
      all_goals simp only [dexec, ha']
  | .ite c t e, f, s, s', o, h => by
    obtain ⟨v, o₁, hv, hr, rfl⟩ := bexec_ite h
    have hev : c.eval s.down = v := (cev_eval c hv).symm
    by_cases h0 : v ≠ 0
    · rw [ite_t h0] at hr
      simp only [dexec, hev, ite_t h0, bexec_dexec t f hr, dlab_some]
    · rw [ite_f h0] at hr
      simp only [dexec, hev, ite_f h0, bexec_dexec e f hr, dlab_some]
  | .block b, f, s, s', o, h => by
    obtain ⟨o₁, hb, rfl⟩ := bexec_block h
    simp only [dexec, bexec_dexec b f hb, dlab_some]
  | .loop b, f, s, s', o, h => by
    have h' : dexec.dloopN (bexec nl b f) f s = some (o, s') := by simpa only [bexec] using h
    exact dloopN_mono (fun s r hr => bexec_dexec b f hr) f s _ h'
  | .br k, f, s, s', o, h => by
    obtain ⟨-, rfl, rfl⟩ := bexec_br h
    rfl
  | .brIf k c, f, s, s', o, h => by
    obtain ⟨-, v, hv, rfl, rfl⟩ := bexec_brIf h
    simp only [dexec, ← cev_eval c hv]
    split <;> rfl
  | .ret e, f, s, s', o, h => by
    obtain ⟨v, hv, rfl, rfl⟩ := bexec_ret h
    simp only [dexec, ← cev_eval e hv]
  | .call b args dst, f, s, s', o, h => by
    cases hm : args.mapM (cev nl s) with
    | none => simp [bexec, hm] at h
    | some as =>
      have hb' : bcall nl b as dst s = some (o, s') := by simpa [bexec, hm] using h
      have hd := bcall_dcall hb'
      simp only [dexec, ← mapM_cev hm, hd]

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun
