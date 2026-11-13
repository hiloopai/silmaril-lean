module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Fits.Main

/-!
# Memories of `2 ^ 32 + 4 · max F R` bytes or more: every access is in bounds

Every load and store of the asyncified program has a 32-bit address operand and an offset of at
most `4 · max F R - 4` (`OffI`). That holds of every instruction of the program's bodies
(`envOff_asyncify`) and stays true of every frame along a target run (`offCfg_step`,
`offT_runN`). So an access ends below `2 ^ 32 + 4 · max F R`, and a memory at least that large
is never overrun, whatever the run does (`safe_wide`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

/-- An instruction whose loads and stores (also inside `if` arms) have offsets with
`offset + 4 ≤ B`. -/
inductive OffI (B : Nat) : Instr → Prop where
  | load {t : IntType} {pk : Option (PackSize × Signedness)} {m : MemIdx} {arg : MemArg} :
      arg.offset.val + 4 ≤ B → OffI B (.intLoad t pk m arg)
  | store {t : IntType} {pk : Option PackSize} {m : MemIdx} {arg : MemArg} :
      arg.offset.val + 4 ≤ B → OffI B (.intStore t pk m arg)
  | ifE {bt : BlockType} {t e : List Instr} : (∀ i ∈ t, OffI B i) → (∀ i ∈ e, OffI B i) →
      OffI B (.if_ bt t e)
  | free {i : Instr} : AccFree i → (∀ bt t e, i ≠ .if_ bt t e) → OffI B i

/-- Every instruction of every frame satisfies `OffI B`. -/
def OffCfg (B : Nat) (c : Cfg) : Prop := ∀ fr ∈ c.frames, ∀ i ∈ fr.code, OffI B i

/-- Every body of the program satisfies `OffI B`. -/
def EnvOff (B : Nat) (E : Env) : Prop := ∀ fn ∈ E.fns, ∀ i ∈ fn.body, OffI B i

theorem offI_free {B : Nat} {i : Instr} (h : AccFree i) (hif : ∀ bt t e, i ≠ .if_ bt t e) :
    OffI B i := .free h hif

/-- An access is a 32-bit operand plus the offset of an `i32` load or store. -/
theorem accessAt_some {i : Instr} {ops : List W} {a : Nat} (h : accessAt i ops = some a) :
    ∃ (w : W) (m : MemIdx) (arg : MemArg), a = w.toNat + arg.offset.val ∧
      (i = .intLoad .i32 none m arg ∨ i = .intStore .i32 none m arg) := by
  unfold accessAt at h
  split at h
  · rename_i m arg w _
    exact ⟨w, m, arg, (Option.some.inj h).symm, Or.inl rfl⟩
  · rename_i m arg _ w _
    exact ⟨w, m, arg, (Option.some.inj h).symm, Or.inr rfl⟩
  · cases h

/-- An access by an instruction with `OffI B` ends below `2 ^ 32 + B`. -/
theorem offI_access {B : Nat} {i : Instr} (h : OffI B i) {ops : List W} {a : Nat}
    (ha : accessAt i ops = some a) : a + 4 < 2 ^ 32 + B := by
  obtain ⟨w, m, arg, hae, hi⟩ := accessAt_some ha
  have hw := w.isLt
  rcases hi with rfl | rfl
  · cases h with
    | load hb => omega
    | free hf _ => rw [hf] at ha; cases ha
  · cases h with
    | store hb => omega
    | free hf _ => rw [hf] at ha; cases ha

/-- No access past `cap ≥ 2 ^ 32 + B` from a configuration with `OffCfg B`. -/
theorem not_oob_off {B cap : Nat} {c : Cfg} (h : OffCfg B c) (hcap : 2 ^ 32 + B ≤ cap) :
    ¬ OOB cap c := by
  rintro ⟨a, ha, hlt⟩
  unfold access at ha
  split at ha
  · rename_i fr rest hf
    split at ha
    · rename_i i code hc
      have hi : OffI B i := h fr (by simp [hf]) i (by simp [hc])
      have := offI_access hi ha
      omega
    · cases ha
  · cases ha

theorem ctlOf_if {i : Instr} {bt : BlockType} {t e : List Instr}
    (h : ctlOf i = some (.ifE bt t e)) : i = .if_ bt t e := by
  cases i <;> simp [ctlOf] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

theorem offCfg_ret {B : Nat} {c c' : Cfg} {fr : Frame} {rest : List Frame} {vs : List W}
    (hc : OffCfg B c) (hf : c.frames = fr :: rest) (h : ret c vs rest = .next c') :
    OffCfg B c' := by
  cases rest with
  | nil => cases h
  | cons caller rest' =>
    have hc' : c' = { c with frames := { caller with ops := vs ++ caller.ops } :: rest' } :=
      (Res.next.inj h).symm
    intro g hg
    rw [hc'] at hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact hc caller (by simp [hf])
    · exact hc g (by simp [hf, hg])

/-- The top frame continues with `code'`, other frames unchanged. -/
theorem offCfg_top {B : Nat} {c : Cfg} {fr : Frame} {rest : List Frame} {code' : List Instr}
    (hc : OffCfg B c) (hf : c.frames = fr :: rest) (hcode : ∀ i ∈ code', OffI B i)
    (fr' : Frame) (hfr' : fr'.code = code') (gs : List W) (m : Nat → W) :
    OffCfg B ⟨fr' :: rest, gs, m⟩ := by
  intro g hg
  simp only [List.mem_cons] at hg
  rcases hg with rfl | hg
  · rw [hfr']; exact hcode
  · exact hc g (by simp [hf, hg])

/-- The callee's entry frame on top of the caller past its `call`. -/
theorem offCfg_entry {B : Nat} {E : Env} (hE : EnvOff B E) {c : Cfg} {fr : Frame}
    {rest : List Frame} {code : List Instr} {fn : FnDef} (hc : OffCfg B c)
    (hf : c.frames = fr :: rest) (hcode : ∀ j ∈ code, OffI B j) (hfn : fn ∈ E.fns) (f : Nat)
    (args ops : List W) :
    OffCfg B (c.setTop (entry f fn args) ({ fr with ops := ops, code := code } :: rest)) := by
  intro g hg
  simp only [Cfg.setTop, List.mem_cons] at hg
  rcases hg with rfl | rfl | hg
  · exact hE fn hfn
  · exact hcode
  · exact hc g (by simp [hf, hg])

theorem offCfg_call {B : Nat} {E : Env} (hE : EnvOff B E) {c c' : Cfg} {fr : Frame}
    {rest : List Frame} {i : Instr} {code : List Instr} {f : Nat} (hc : OffCfg B c)
    (hf : c.frames = fr :: rest) (hcode : ∀ j ∈ code, OffI B j) (hctl : ctlOf i = some (.call f))
    (h : exec E c fr i code rest = .next c') : OffCfg B c' := by
  unfold exec at h
  rw [hctl] at h
  dsimp only at h
  split at h
  · split at h <;> cases h
  · split at h
    · cases h
    · rename_i fn hfn
      split at h
      · rw [← Res.next.inj h]
        exact offCfg_entry hE hc hf hcode (List.mem_of_getElem? hfn) _ _ _
      · cases h

theorem offCfg_if {B : Nat} {E : Env} {c c' : Cfg} {fr : Frame} {rest : List Frame} {i : Instr}
    {code : List Instr} {bt : BlockType} {t e : List Instr} (hc : OffCfg B c)
    (hf : c.frames = fr :: rest) (hcode : ∀ j ∈ code, OffI B j)
    (harms : (∀ j ∈ t, OffI B j) ∧ (∀ j ∈ e, OffI B j)) (hctl : ctlOf i = some (.ifE bt t e))
    (h : exec E c fr i code rest = .next c') : OffCfg B c' := by
  unfold exec at h
  rw [hctl] at h
  dsimp only at h
  split at h
  · rename_i x ops _
    rw [← Res.next.inj h]
    refine offCfg_top hc hf ?_ _ rfl _ _
    intro j hj
    rcases List.mem_append.1 hj with hj | hj
    · by_cases hx : x = 0
      · simp only [hx, ↓reduceIte] at hj; exact harms.2 j hj
      · simp only [hx, ↓reduceIte] at hj; exact harms.1 j hj
    · exact hcode j hj
  · cases h

theorem offCfg_seg {B : Nat} {E : Env} {c c' : Cfg} {fr : Frame} {rest : List Frame} {i : Instr}
    {code : List Instr} (hc : OffCfg B c) (hf : c.frames = fr :: rest)
    (hcode : ∀ j ∈ code, OffI B j) (hctl : ctlOf i = none)
    (h : exec E c fr i code rest = .next c') : OffCfg B c' := by
  unfold exec at h
  rw [hctl] at h
  dsimp only at h
  split at h
  · rw [← Res.next.inj h]
    exact offCfg_top hc hf hcode _ rfl _ _
  · cases h

theorem offI_arms {B : Nat} {i : Instr} {bt : BlockType} {t e : List Instr} (hi : OffI B i)
    (hie : i = .if_ bt t e) : (∀ j ∈ t, OffI B j) ∧ (∀ j ∈ e, OffI B j) := by
  subst hie
  cases hi with
  | ifE ht he => exact ⟨ht, he⟩
  | free _ hne => exact absurd rfl (hne bt t e)

theorem offCfg_exec {B : Nat} {E : Env} (hE : EnvOff B E) {c c' : Cfg} {fr : Frame}
    {rest : List Frame} {i : Instr} {code : List Instr} (hc : OffCfg B c)
    (hf : c.frames = fr :: rest) (hcode : fr.code = i :: code)
    (h : exec E c fr i code rest = .next c') : OffCfg B c' := by
  have hcode' : ∀ j ∈ code, OffI B j := fun j hj => hc fr (by simp [hf]) j (by simp [hcode, hj])
  have hi : OffI B i := hc fr (by simp [hf]) i (by simp [hcode])
  cases hctl : ctlOf i with
  | none => exact offCfg_seg hc hf hcode' hctl h
  | some k =>
    cases k with
    | call f => exact offCfg_call hE hc hf hcode' hctl h
    | ret =>
      unfold exec at h
      rw [hctl] at h
      exact offCfg_ret hc hf h
    | ifE bt t e => exact offCfg_if hc hf hcode' (offI_arms hi (ctlOf_if hctl)) hctl h

/-- **`OffCfg` is kept by machine steps.** -/
theorem offCfg_step {B : Nat} {E : Env} (hE : EnvOff B E) {c c' : Cfg} (hc : OffCfg B c)
    (h : step E c = .next c') : OffCfg B c' := by
  unfold step at h
  split at h
  · cases h
  · rename_i fr rest hf
    split at h
    · exact offCfg_ret hc hf h
    · rename_i i code hcode
      exact offCfg_exec hE hc hf hcode h

/-- One step of the target system keeps `OffCfg`, the host's re-entry included. -/
theorem offT_step {B : Nat} {E : Env} (hE : EnvOff B E) (H : Host σ) {t t' : TSt σ}
    (ht : OffCfg B t.cfg) (hs : tgtStep E H t = .next t') : OffCfg B t'.cfg := by
  unfold tgtStep at hs
  split at hs
  · rename_i c' hst
    rw [← SRes.next.inj hs]
    exact offCfg_step hE ht hst
  · dsimp only at hs
    split at hs
    · split at hs
      · rename_i fn _ hfn
        rw [← SRes.next.inj hs]
        intro g hg
        have hg' : g = entry t.fid fn t.args := by simpa using hg
        rw [hg']
        exact hE fn (List.mem_of_getElem? hfn)
      · cases hs
    · cases hs
  · cases hs
  · cases hs

/-- **`OffCfg` is kept along target runs.** -/
theorem offT_runN {B : Nat} {E : Env} (hE : EnvOff B E) (H : Host σ) :
    ∀ (n : Nat) (t : TSt σ), OffCfg B t.cfg → ∀ y, runN (tgtStep E H) n t = .next y →
      OffCfg B y.cfg
  | 0, t, ht, y, hy => by cases hy; exact ht
  | n + 1, t, ht, y, hy => by
    cases hs : tgtStep E H t with
    | stop o => simp only [runN, hs] at hy; cases hy
    | next t' =>
      have hy' : runN (tgtStep E H) n t' = .next y := by simpa only [runN, hs] using hy
      exact offT_runN hE H n t' (offT_step hE H ht hs) y hy'

end Silmaril.Wasm.FX.Asyncify.Tool
