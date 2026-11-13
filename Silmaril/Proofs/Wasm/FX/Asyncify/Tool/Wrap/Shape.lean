module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Fits.WideEnv

/-!
# Large offsets are only used from address `0`

`Fits/Wide` bounds every access of the asyncified program by `2 ^ 32 + 4 · max F R`: an access
is a 32-bit operand plus an offset of the generated code. The offsets of at least `4 F` are
those of the request area (`reqArgs`, `pushAns`), and their address operand is always the
constant `0` pushed right before them (`c32 0, local.get a, st o` and `c32 0, ld o`). This
module turns that shape into an invariant of target runs:

* `CodeOK F R l`: every load and store of `l` (also inside `if` arms) either has an offset with
  `o + 4 ≤ 4 F`, or is a request access `c32 0 :: ld o` / `c32 0 :: local.get a :: st o` with
  `o + 4 ≤ 4 R`;
* `FrOK`: the top frame is `CodeOK`, or in the middle of a request access with the `0` on its
  operand stack; `CfgOK`: the top frame is `FrOK`, the frames below are `CodeOK`;
* `cfgOK_step`, `cfgOK_runN`: kept along target runs, the host's re-entry included;
* `not_oob_ok`: from `CfgOK`, an access ends at or below `2 ^ 32 - 1 + 4 F` (a `sp`-relative
  record word) or at or below `4 R` (the request area).

So a memory of `cap` bytes with `2 ^ 32 + 4 F ≤ cap + 1` and `4 R ≤ cap` is never overrun
(`safe_shape`), sharpening `safe_wide` (which needs `2 ^ 32 + 4 · max F R ≤ cap`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

/-- Code whose large-offset accesses are request accesses from address `0`. -/
inductive CodeOK (F R : Nat) : List Instr → Prop where
  | nil : CodeOK F R []
  | small {i : Instr} {l : List Instr} : OffI (4 * F) i → (∀ bt t e, i ≠ .if_ bt t e) →
      CodeOK F R l → CodeOK F R (i :: l)
  | ifE {bt : BlockType} {t e l : List Instr} : CodeOK F R t → CodeOK F R e → CodeOK F R l →
      CodeOK F R (.if_ bt t e :: l)
  | ld0 {o : Nat} {l : List Instr} : o + 4 ≤ 4 * R → o < 2 ^ 64 → CodeOK F R l →
      CodeOK F R (c32 0 :: ld o :: l)
  | st0 {a : LocalIdx} {o : Nat} {l : List Instr} : o + 4 ≤ 4 * R → o < 2 ^ 64 → CodeOK F R l →
      CodeOK F R (c32 0 :: .localGet a :: st o :: l)

/-- The top frame: `CodeOK`, or inside a request access with the address `0` on the stack. -/
def FrOK (F R : Nat) (fr : Frame) : Prop :=
  CodeOK F R fr.code ∨
  (∃ o l ops, fr.code = ld o :: l ∧ o + 4 ≤ 4 * R ∧ o < 2 ^ 64 ∧ CodeOK F R l ∧
    fr.ops = 0 :: ops) ∨
  (∃ a o l ops, fr.code = .localGet a :: st o :: l ∧ o + 4 ≤ 4 * R ∧ o < 2 ^ 64 ∧
    CodeOK F R l ∧ fr.ops = 0 :: ops) ∨
  (∃ v o l ops, fr.code = st o :: l ∧ o + 4 ≤ 4 * R ∧ o < 2 ^ 64 ∧ CodeOK F R l ∧
    fr.ops = v :: 0 :: ops)

/-- The top frame is `FrOK`, the frames below are `CodeOK`. -/
def CfgOK (F R : Nat) (c : Cfg) : Prop :=
  match c.frames with
  | [] => True
  | fr :: rest => FrOK F R fr ∧ ∀ g ∈ rest, CodeOK F R g.code

/-- Every body of the program is `CodeOK`. -/
def EnvOK (F R : Nat) (E : Env) : Prop := ∀ fn ∈ E.fns, CodeOK F R fn.body

theorem CodeOK.append {F R : Nat} {a b : List Instr} (ha : CodeOK F R a) (hb : CodeOK F R b) :
    CodeOK F R (a ++ b) := by
  induction ha with
  | nil => exact hb
  | small hi hif _ ih => exact .small hi hif ih
  | ifE ht he _ _ _ ih => exact .ifE ht he ih
  | ld0 h1 h2 _ ih => exact .ld0 h1 h2 ih
  | st0 h1 h2 _ ih => exact .st0 h1 h2 ih

theorem cfgOK_of {F R : Nat} {fr : Frame} {rest : List Frame} {gs : List W} {m : Nat → W}
    (h : FrOK F R fr) (hr : ∀ g ∈ rest, CodeOK F R g.code) : CfgOK F R ⟨fr :: rest, gs, m⟩ :=
  ⟨h, hr⟩

/-! ## Steps keep `CfgOK` -/

/-- A straight-line step: the top frame's code becomes `code`, the frames below are unchanged. -/
theorem exec_none_inv {E : Env} {c c' : Cfg} {fr : Frame} {rest : List Frame} {i : Instr}
    {code : List Instr} (hctl : ctlOf i = none) (h : exec E c fr i code rest = .next c') :
    ∃ s, segCore i (fr.ls c) = some s ∧
      c' = ⟨{ fr with locals := s.locals, ops := s.ops, code := code } :: rest, s.globals, s.mem⟩ := by
  unfold exec at h
  rw [hctl] at h
  dsimp only at h
  split at h
  · rename_i s hs
    exact ⟨s, hs, (Res.next.inj h).symm⟩
  · cases h

theorem cfgOK_ret {F R : Nat} {c c' : Cfg} {rest : List Frame} {vs : List W}
    (hr : ∀ g ∈ rest, CodeOK F R g.code) (h : ret c vs rest = .next c') : CfgOK F R c' := by
  cases rest with
  | nil => cases h
  | cons caller rest' =>
    have hc' : c' = { c with frames := { caller with ops := vs ++ caller.ops } :: rest' } :=
      (Res.next.inj h).symm
    rw [hc']
    exact ⟨Or.inl (hr caller (by simp)), fun g hg => hr g (by simp [hg])⟩

/-- A straight-line step to a `CodeOK` continuation. -/
theorem cfgOK_seg {F R : Nat} {E : Env} {c c' : Cfg} {fr : Frame} {rest : List Frame}
    {i : Instr} {code : List Instr} (hr : ∀ g ∈ rest, CodeOK F R g.code) (hl : CodeOK F R code)
    (hctl : ctlOf i = none) (h : exec E c fr i code rest = .next c') : CfgOK F R c' := by
  obtain ⟨s, -, rfl⟩ := exec_none_inv hctl h
  exact cfgOK_of (Or.inl hl) hr

theorem cfgOK_call {F R : Nat} {E : Env} (hE : EnvOK F R E) {c c' : Cfg} {fr : Frame}
    {rest : List Frame} {i : Instr} {code : List Instr} {f : Nat}
    (hr : ∀ g ∈ rest, CodeOK F R g.code) (hl : CodeOK F R code) (hctl : ctlOf i = some (.call f))
    (h : exec E c fr i code rest = .next c') : CfgOK F R c' := by
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
        refine ⟨Or.inl (hE fn (List.mem_of_getElem? hfn)), fun g hg => ?_⟩
        simp only [List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact hl
        · exact hr g hg
      · cases h

theorem cfgOK_if {F R : Nat} {E : Env} {c c' : Cfg} {fr : Frame} {rest : List Frame}
    {code : List Instr} {bt : BlockType} {t e : List Instr} (hr : ∀ g ∈ rest, CodeOK F R g.code)
    (hl : CodeOK F R code) (ht : CodeOK F R t) (he : CodeOK F R e)
    (h : exec E c fr (.if_ bt t e) code rest = .next c') : CfgOK F R c' := by
  unfold exec at h
  simp only [ctlOf] at h
  split at h
  · rename_i x ops _
    rw [← Res.next.inj h]
    refine ⟨Or.inl ?_, hr⟩
    by_cases hx : x = 0
    · simpa only [hx, ↓reduceIte] using he.append hl
    · simpa only [hx, ↓reduceIte] using ht.append hl
  · cases h

/-- An instruction that is not an `if`: its control class is a call, a return or none. -/
theorem cfgOK_plain {F R : Nat} {E : Env} (hE : EnvOK F R E) {c c' : Cfg} {fr : Frame}
    {rest : List Frame} {i : Instr} {code : List Instr} (hr : ∀ g ∈ rest, CodeOK F R g.code)
    (hl : CodeOK F R code) (hif : ∀ bt t e, i ≠ .if_ bt t e)
    (h : exec E c fr i code rest = .next c') : CfgOK F R c' := by
  cases hctl : ctlOf i with
  | none => exact cfgOK_seg hr hl hctl h
  | some k =>
    cases k with
    | call f => exact cfgOK_call hE hr hl hctl h
    | ret =>
      unfold exec at h
      rw [hctl] at h
      exact cfgOK_ret hr h
    | ifE bt t e => exact absurd (ctlOf_if hctl) (hif bt t e)

theorem segCore_c32 {n : Nat} {s s' : LS} (h : segCore (c32 n) s = some s') :
    s'.ops = BitVec.ofNat 32 n :: s.ops := by
  have h' : segStep (c32 n) s = some s' := h
  rw [segStep_c32] at h'
  rw [← Option.some.inj h']

theorem segCore_get {a : LocalIdx} {s s' : LS} (h : segCore (.localGet a) s = some s') :
    ∃ v, s'.ops = v :: s.ops := by
  cases hv : s.locals[a.value.val]? with
  | none => simp [segCore, pexec, hv] at h
  | some v =>
    have h' : some { s with ops := v :: s.ops } = some s' := by
      simpa [segCore, pexec, hv] using h
    exact ⟨v, by rw [← Option.some.inj h']⟩

/-- A request access: `c32 0` pushes the address `0`. -/
theorem cfgOK_ld0 {F R : Nat} {E : Env} {c c' : Cfg} {fr : Frame} {rest : List Frame} {o : Nat}
    {l : List Instr} (hr : ∀ g ∈ rest, CodeOK F R g.code) (h1 : o + 4 ≤ 4 * R) (h2 : o < 2 ^ 64)
    (hl : CodeOK F R l) (h : exec E c fr (c32 0) (ld o :: l) rest = .next c') : CfgOK F R c' := by
  obtain ⟨s, hs, rfl⟩ := exec_none_inv rfl h
  have hops : s.ops = 0 :: fr.ops := segCore_c32 hs
  exact cfgOK_of (Or.inr (Or.inl ⟨o, l, fr.ops, rfl, h1, h2, hl, hops⟩)) hr

theorem cfgOK_st0 {F R : Nat} {E : Env} {c c' : Cfg} {fr : Frame} {rest : List Frame}
    {a : LocalIdx} {o : Nat} {l : List Instr} (hr : ∀ g ∈ rest, CodeOK F R g.code)
    (h1 : o + 4 ≤ 4 * R) (h2 : o < 2 ^ 64) (hl : CodeOK F R l)
    (h : exec E c fr (c32 0) (.localGet a :: st o :: l) rest = .next c') : CfgOK F R c' := by
  obtain ⟨s, hs, rfl⟩ := exec_none_inv rfl h
  have hops : s.ops = 0 :: fr.ops := segCore_c32 hs
  exact cfgOK_of (Or.inr (Or.inr (Or.inl ⟨a, o, l, fr.ops, rfl, h1, h2, hl, hops⟩))) hr

theorem cfgOK_get {F R : Nat} {E : Env} {c c' : Cfg} {fr : Frame} {rest : List Frame}
    {a : LocalIdx} {o : Nat} {l : List Instr} {ops : List W} (hr : ∀ g ∈ rest, CodeOK F R g.code)
    (h1 : o + 4 ≤ 4 * R) (h2 : o < 2 ^ 64) (hl : CodeOK F R l) (hops : fr.ops = 0 :: ops)
    (h : exec E c fr (.localGet a) (st o :: l) rest = .next c') : CfgOK F R c' := by
  obtain ⟨s, hs, rfl⟩ := exec_none_inv rfl h
  obtain ⟨v, hv⟩ := segCore_get hs
  have hops' : s.ops = v :: 0 :: ops := by rw [hv]; simp [Frame.ls, hops]
  exact cfgOK_of (Or.inr (Or.inr (Or.inr ⟨v, o, l, ops, rfl, h1, h2, hl, hops'⟩))) hr

/-- A top frame with `CodeOK` code. -/
theorem cfgOK_exec_code {F R : Nat} {E : Env} (hE : EnvOK F R E) {c c' : Cfg} {fr : Frame}
    {rest : List Frame} {i : Instr} {code : List Instr} (hr : ∀ g ∈ rest, CodeOK F R g.code)
    (hc : CodeOK F R (i :: code)) (h : exec E c fr i code rest = .next c') : CfgOK F R c' := by
  cases hc with
  | small _ hif hl => exact cfgOK_plain hE hr hl hif h
  | ifE ht he hl => exact cfgOK_if hr hl ht he h
  | ld0 h1 h2 hl => exact cfgOK_ld0 hr h1 h2 hl h
  | st0 h1 h2 hl => exact cfgOK_st0 hr h1 h2 hl h

/-- **`CfgOK` is kept by machine steps.** -/
theorem cfgOK_step {F R : Nat} {E : Env} (hE : EnvOK F R E) {c c' : Cfg} (hc : CfgOK F R c)
    (h : step E c = .next c') : CfgOK F R c' := by
  unfold step at h
  unfold CfgOK at hc
  split at h
  · cases h
  · rename_i fr rest hf
    rw [hf] at hc
    obtain ⟨htop, hr⟩ := hc
    split at h
    · exact cfgOK_ret hr h
    · rename_i i code hcode
      rcases htop with hok | ⟨o, l, ops, hl, -, -, hlo, -⟩ | ⟨a, o, l, ops, hl, h1, h2, hlo, hops⟩ |
        ⟨v, o, l, ops, hl, -, -, hlo, -⟩
      · exact cfgOK_exec_code hE hr (hcode ▸ hok) h
      · obtain ⟨rfl, rfl⟩ := List.cons.inj (hcode.symm.trans hl)
        exact cfgOK_seg hr hlo rfl h
      · obtain ⟨rfl, rfl⟩ := List.cons.inj (hcode.symm.trans hl)
        exact cfgOK_get hr h1 h2 hlo hops h
      · obtain ⟨rfl, rfl⟩ := List.cons.inj (hcode.symm.trans hl)
        exact cfgOK_seg hr hlo rfl h

/-- One step of the target system keeps `CfgOK`, the host's re-entry included. -/
theorem cfgOK_tgt {F R : Nat} {E : Env} (hE : EnvOK F R E) (H : Host σ) {t t' : TSt σ}
    (ht : CfgOK F R t.cfg) (hs : tgtStep E H t = .next t') : CfgOK F R t'.cfg := by
  unfold tgtStep at hs
  split at hs
  · rename_i c' hst
    rw [← SRes.next.inj hs]
    exact cfgOK_step hE ht hst
  · dsimp only at hs
    split at hs
    · split at hs
      · rename_i fn _ hfn
        rw [← SRes.next.inj hs]
        exact cfgOK_of (Or.inl (hE fn (List.mem_of_getElem? hfn))) (by simp)
      · cases hs
    · cases hs
  · cases hs
  · cases hs

/-- **`CfgOK` is kept along target runs.** -/
theorem cfgOK_runN {F R : Nat} {E : Env} (hE : EnvOK F R E) (H : Host σ) :
    ∀ (n : Nat) (t : TSt σ), CfgOK F R t.cfg → ∀ y, runN (tgtStep E H) n t = .next y →
      CfgOK F R y.cfg
  | 0, t, ht, y, hy => by cases hy; exact ht
  | n + 1, t, ht, y, hy => by
    cases hs : tgtStep E H t with
    | stop o => simp only [runN, hs] at hy; cases hy
    | next t' =>
      have hy' : runN (tgtStep E H) n t' = .next y := by simpa only [runN, hs] using hy
      exact cfgOK_runN hE H n t' (cfgOK_tgt hE H ht hs) y hy'

/-! ## No access past `cap` from `CfgOK` -/

theorem accessAt_c32_none {n : Nat} {ops : List W} : accessAt (c32 n) ops = none := rfl

theorem accessAt_if_none {bt : BlockType} {t e : List Instr} {ops : List W} :
    accessAt (.if_ bt t e) ops = none := rfl

/-- The next access of a `CodeOK` frame ends below `2 ^ 32 + 4 F`. -/
theorem codeOK_access {F R : Nat} {i : Instr} {l : List Instr} (hc : CodeOK F R (i :: l))
    {ops : List W} {a : Nat} (ha : accessAt i ops = some a) : a + 4 < 2 ^ 32 + 4 * F := by
  cases hc with
  | small hi _ _ => exact offI_access hi ha
  | ifE => rw [accessAt_if_none] at ha; cases ha
  | ld0 => rw [accessAt_c32_none] at ha; cases ha
  | st0 => rw [accessAt_c32_none] at ha; cases ha

theorem access_ld0 {o a : Nat} {ops : List W} (ho : o < 2 ^ 64)
    (ha : accessAt (ld o) (0 :: ops) = some a) : a = o := by
  have hacc : accessAt (ld o) (0 :: ops) = some o := by rw [accessAt_ld ho]; simp
  exact Option.some.inj (ha.symm.trans hacc)

theorem access_st0 {o a : Nat} {v : W} {ops : List W} (ho : o < 2 ^ 64)
    (ha : accessAt (st o) (v :: 0 :: ops) = some a) : a = o := by
  have hacc : accessAt (st o) (v :: 0 :: ops) = some o := by rw [accessAt_st ho]; simp
  exact Option.some.inj (ha.symm.trans hacc)

/-- The next access of an `FrOK` frame ends at or below `cap`. -/
theorem frOK_access {F R cap : Nat} {fr : Frame} {i : Instr} {code : List Instr}
    (h : FrOK F R fr) (hcode : fr.code = i :: code) (hF : 2 ^ 32 + 4 * F ≤ cap + 1)
    (hR : 4 * R ≤ cap) {a : Nat} (ha : accessAt i fr.ops = some a) : a + 4 ≤ cap := by
  rcases h with hok | ⟨o, l, ops, hl, h1, h2, -, hops⟩ | ⟨b, o, l, ops, hl, -, -, -, -⟩ |
    ⟨v, o, l, ops, hl, h1, h2, -, hops⟩
  · have hlt : a + 4 < 2 ^ 32 + 4 * F := codeOK_access (hcode ▸ hok) ha
    omega
  · have hi : i = ld o := (List.cons.inj (hcode.symm.trans hl)).1
    have hao : a = o := access_ld0 h2 (by rw [← hops, ← hi]; exact ha)
    omega
  · have hi : i = .localGet b := (List.cons.inj (hcode.symm.trans hl)).1
    rw [hi] at ha
    cases ha
  · have hi : i = st o := (List.cons.inj (hcode.symm.trans hl)).1
    have hao : a = o := access_st0 h2 (by rw [← hops, ← hi]; exact ha)
    omega

/-- **No access past `cap`** from `CfgOK` when `2 ^ 32 + 4 F ≤ cap + 1` and `4 R ≤ cap`. -/
theorem not_oob_ok {F R cap : Nat} {c : Cfg} (h : CfgOK F R c) (hF : 2 ^ 32 + 4 * F ≤ cap + 1)
    (hR : 4 * R ≤ cap) : ¬ OOB cap c := by
  rintro ⟨a, ha, hlt⟩
  unfold access at ha
  unfold CfgOK at h
  split at ha
  · rename_i fr rest hf
    have htop : FrOK F R fr := by rw [hf] at h; exact h.1
    split at ha
    · rename_i i code hcode
      have hle : a + 4 ≤ cap := frOK_access htop hcode hF hR ha
      omega
    · cases ha
  · cases ha

end Silmaril.Wasm.FX.Asyncify.Tool
