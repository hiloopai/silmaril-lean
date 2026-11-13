module

public import Silmaril.Wasm.FX.Asyncify.Tool.Fits.Defs
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Main

/-!
# In-bounds runs: machine steps that never access memory past `cap`

`StepsS cap E n c c'` is `Steps E n c c'` in which no state before a step accesses memory past
`cap` (`OOB`). `SafeT cap E H n t` says the same of the first `n` states of a target run. The
generated code's segments are run with `steps_segS` under `SegSafe` (every access of the segment
ends at or below `cap`), which holds for segments without loads and stores (`segSafe_free`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

/-! ## Instructions without memory access -/

/-- Instruction `i` never accesses memory. -/
def AccFree (i : Instr) : Prop := ∀ ops, accessAt i ops = none

theorem accFree_of_pure {S : Nat} {i : Instr} (hi : PureShape S i) : AccFree i := by
  intro ops
  cases hi <;> rfl

theorem accFree_get (a : LocalIdx) : AccFree (.localGet a) := fun _ => rfl
theorem accFree_set (a : LocalIdx) : AccFree (.localSet a) := fun _ => rfl
theorem accFree_c32 (n : Nat) : AccFree (c32 n) := fun _ => rfl
theorem accFree_gget (g : GlobalIdx) : AccFree (.globalGet g) := fun _ => rfl
theorem accFree_gset (g : GlobalIdx) : AccFree (.globalSet g) := fun _ => rfl
theorem accFree_rel (op : IntRelOp) : AccFree (.intRelOp .i32 op) := fun _ => rfl
theorem accFree_bin (op : IntBinOp) : AccFree (.intBinOp .i32 op) := fun _ => rfl

/-! ## Segments -/

/-- Every access of segment `is` from state `s` ends at or below `cap`. -/
def SegSafe (cap : Nat) : List Instr → LS → Prop
  | [], _ => True
  | i :: is, s => (∀ a, accessAt i s.ops = some a → a + 4 ≤ cap) ∧
      ∀ s1, segStep i s = some s1 → SegSafe cap is s1

theorem segSafe_free {cap : Nat} : ∀ {is : List Instr} {s : LS}, (∀ i ∈ is, AccFree i) →
    SegSafe cap is s
  | [], _, _ => trivial
  | i :: is, s, h => by
    refine ⟨fun a ha => ?_, fun s1 _ => segSafe_free fun j hj => h j (by simp [hj])⟩
    rw [h i (by simp)] at ha
    cases ha

theorem segSafe_append {cap : Nat} : ∀ {a b : List Instr} {s : LS}, SegSafe cap a s →
    (∀ s', runSeg a s = some s' → SegSafe cap b s') → SegSafe cap (a ++ b) s
  | [], b, s, _, h => h s rfl
  | i :: a, b, s, ⟨h1, h2⟩, h => by
    refine ⟨h1, fun s1 hs1 => segSafe_append (h2 s1 hs1) fun s' hs' => h s' ?_⟩
    simp only [runSeg, hs1, Option.bind_some]
    exact hs'

/-! ## Machine steps that stay in bounds -/

/-- `n` machine steps, none from a state that accesses memory past `cap`. -/
inductive StepsS (cap : Nat) (E : Env) : Nat → Cfg → Cfg → Prop where
  | refl (c : Cfg) : StepsS cap E 0 c c
  | cons {n : Nat} {c c₁ c₂ : Cfg} : ¬ OOB cap c → step E c = .next c₁ → StepsS cap E n c₁ c₂ →
      StepsS cap E (n + 1) c c₂

theorem StepsS.trans {cap : Nat} {E : Env} {m n : Nat} {a b c : Cfg} (h1 : StepsS cap E m a b)
    (h2 : StepsS cap E n b c) : StepsS cap E (m + n) a c := by
  induction h1 with
  | refl => simpa using h2
  | cons ho hs _ ih => rw [Nat.add_right_comm]; exact .cons ho hs (ih h2)

theorem StepsS.one {cap : Nat} {E : Env} {a b : Cfg} (ho : ¬ OOB cap a)
    (h : step E a = .next b) : StepsS cap E 1 a b := .cons ho h (.refl b)

theorem StepsS.steps {cap : Nat} {E : Env} {n : Nat} {a b : Cfg} (h : StepsS cap E n a b) :
    Steps E n a b := by
  induction h with
  | refl => exact .refl _
  | cons _ hs _ ih => exact .cons hs ih

/-- No access past `cap` at a state whose next instruction is `i` with operands `ops`. -/
theorem not_oob_head {cap : Nat} {c : Cfg} {fr : Frame} {rest : List Frame} {i : Instr}
    {code : List Instr} (hf : c.frames = fr :: rest) (hc : fr.code = i :: code)
    (h : ∀ a, accessAt i fr.ops = some a → a + 4 ≤ cap) : ¬ OOB cap c := by
  rintro ⟨a, ha, hlt⟩
  have hacc : access c = accessAt i fr.ops := by simp [access, hf, hc]
  have := h a (hacc ▸ ha)
  omega

theorem not_oob_free {cap : Nat} {c : Cfg} {fr : Frame} {rest : List Frame} {i : Instr}
    {code : List Instr} (hf : c.frames = fr :: rest) (hc : fr.code = i :: code) (hi : AccFree i) :
    ¬ OOB cap c :=
  not_oob_head hf hc fun a ha => by rw [hi] at ha; cases ha

theorem not_oob_nil {cap : Nat} {c : Cfg} {fr : Frame} {rest : List Frame}
    (hf : c.frames = fr :: rest) (hc : fr.code = []) : ¬ OOB cap c := by
  rintro ⟨a, ha, -⟩
  simp [access, hf, hc] at ha

theorem not_oob_empty {cap : Nat} {c : Cfg} (hf : c.frames = []) : ¬ OOB cap c := by
  rintro ⟨a, ha, -⟩
  simp [access, hf] at ha

/-- In-bounds segments run as in-bounds machine steps. -/
theorem steps_segS {cap : Nat} {E : Env} : ∀ {is : List Instr} {fr : Frame} {rest : List Frame}
    {code : List Instr} {g : List W} {m : Nat → W} {s' : LS},
    runSeg is ⟨fr.locals, fr.ops, g, m⟩ = some s' → SegSafe cap is ⟨fr.locals, fr.ops, g, m⟩ →
    StepsS cap E is.length ⟨{ fr with code := is ++ code } :: rest, g, m⟩
      ⟨{ fr with locals := s'.locals, ops := s'.ops, code := code } :: rest, s'.globals, s'.mem⟩
  | [], fr, rest, code, g, m, s', h, _ => by
    simp only [runSeg, Option.some.injEq] at h
    subst h
    exact .refl _
  | i :: is, fr, rest, code, g, m, s', h, ⟨hacc, hsafe⟩ => by
    simp only [runSeg, Option.bind_eq_some_iff] at h
    obtain ⟨s1, h1, h2⟩ := h
    have hs := step_seg (E := E) (c := ⟨{ fr with code := (i :: is) ++ code } :: rest, g, m⟩)
      (fr := { fr with code := (i :: is) ++ code }) (rest := rest) (s' := s1) (i := i)
      (code := is ++ code) rfl rfl h1
    have ho : ¬ OOB cap ⟨{ fr with code := (i :: is) ++ code } :: rest, g, m⟩ :=
      not_oob_head (fr := { fr with code := (i :: is) ++ code }) rfl rfl hacc
    have ih := steps_segS (E := E) (is := is) (fr := { fr with locals := s1.locals, ops := s1.ops })
      (rest := rest) (code := code) (g := s1.globals) (m := s1.mem) (s' := s') h2 (hsafe s1 h1)
    simp only [List.length_cons]
    exact .cons ho hs ih

theorem steps_iteS {cap : Nat} {E : Env} {fr : Frame} {rest : List Frame} {g : List W}
    {m : Nat → W} {seg t e K : List Instr} {x : W} {ops : List W} {ls : List W} {g' : List W}
    (h : runSeg seg ⟨fr.locals, fr.ops, g, m⟩ = some ⟨ls, x :: ops, g', m⟩)
    (hfree : ∀ i ∈ seg, AccFree i) :
    StepsS cap E (seg.length + 1) ⟨{ fr with code := seg ++ .if_ .empty t e :: K } :: rest, g, m⟩
      ⟨{ fr with locals := ls, ops := ops, code := (if x = 0 then e else t) ++ K } :: rest, g', m⟩ := by
  let fr' : Frame := { fr with locals := ls, ops := x :: ops, code := .if_ .empty t e :: K }
  have h1 : StepsS cap E seg.length ⟨{ fr with code := seg ++ .if_ .empty t e :: K } :: rest, g, m⟩
      ⟨fr' :: rest, g', m⟩ :=
    steps_segS (E := E) (fr := fr) (rest := rest) (code := .if_ .empty t e :: K) h
      (segSafe_free hfree)
  have h2 : step E ⟨fr' :: rest, g', m⟩ =
      .next ⟨{ fr with locals := ls, ops := ops, code := (if x = 0 then e else t) ++ K } :: rest,
        g', m⟩ :=
    step_if (fr := fr') rfl rfl rfl
  have ho : ¬ OOB cap ⟨fr' :: rest, g', m⟩ := not_oob_free (fr := fr') rfl rfl fun _ => rfl
  exact h1.trans (.one ho h2)

theorem steps_guardS {cap : Nat} {E : Env} {fr : Frame} {rest : List Frame} {g : List W}
    {m : Nat → W} {seg t K : List Instr} {x : W} {ops : List W} {ls : List W}
    (h : runSeg seg ⟨fr.locals, fr.ops, g, m⟩ = some ⟨ls, x :: ops, g, m⟩)
    (hfree : ∀ i ∈ seg, AccFree i) :
    StepsS cap E (seg.length + 1) ⟨{ fr with code := seg ++ ifThen t :: K } :: rest, g, m⟩
      ⟨{ fr with locals := ls, ops := ops, code := (if x = 0 then [] else t) ++ K } :: rest, g, m⟩ :=
  steps_iteS h hfree

/-! ## Target runs that stay in bounds -/

/-- The first `n` states of the target run from `t` access memory only below `cap`. -/
def SafeT (cap : Nat) (E : Env) (H : Host σ) (n : Nat) (t : TSt σ) : Prop :=
  ∀ m < n, ∀ y, runN (tgtStep E H) m t = .next y → ¬ OOB cap y.cfg

theorem SafeT.zero {cap : Nat} {E : Env} {H : Host σ} (t : TSt σ) : SafeT cap E H 0 t :=
  fun _ hm => absurd hm (Nat.not_lt_zero _)

theorem SafeT.trans {cap : Nat} {E : Env} {H : Host σ} {k n : Nat} {t t' : TSt σ}
    (h : runN (tgtStep E H) k t = .next t') (h1 : SafeT cap E H k t) (h2 : SafeT cap E H n t') :
    SafeT cap E H (k + n) t := by
  intro m hm y hy
  by_cases hmk : m < k
  · exact h1 m hmk y hy
  · have hsplit : m = k + (m - k) := by omega
    have hy' : runN (tgtStep E H) (m - k) t' = .next y := by
      rw [hsplit, runN_add_next h] at hy; exact hy
    exact h2 (m - k) (by omega) y hy'

theorem SafeT.one {cap : Nat} {E : Env} {H : Host σ} {t : TSt σ} (h : ¬ OOB cap t.cfg) :
    SafeT cap E H 1 t := by
  intro m hm y hy
  have hm0 : m = 0 := by omega
  subst hm0
  have hty : t = y := SRes.next.inj hy
  exact hty ▸ h

theorem SafeT.mono {cap : Nat} {E : Env} {H : Host σ} {n n' : Nat} {t : TSt σ}
    (h : SafeT cap E H n t) (hle : n' ≤ n) : SafeT cap E H n' t :=
  fun m hm y hy => h m (by omega) y hy

/-- In-bounds machine steps are an in-bounds prefix of the target run. -/
theorem StepsS.safeT {cap : Nat} {E : Env} {H : Host σ} {n : Nat} {a b : Cfg}
    (h : StepsS cap E n a b) : ∀ {t : TSt σ}, t.cfg = a → SafeT cap E H n t := by
  induction h with
  | refl => intro t _; exact SafeT.zero t
  | @cons n c c₁ c₂ ho hs _ ih =>
    intro t ht
    have hstep : runN (tgtStep E H) 1 t = .next { t with cfg := c₁ } := by
      simp only [runN, tgtStep, ht, hs]
    have h1 : SafeT cap E H 1 t := SafeT.one (ht ▸ ho)
    have h2 : SafeT cap E H n { t with cfg := c₁ } := ih rfl
    have := SafeT.trans hstep h1 h2
    rwa [Nat.add_comm] at this

/-! ## Fitting source states -/

theorem FitsIn.next {cap : Nat} {P : Prog} {H : Host σ} {x x' : Cfg × σ} (h : FitsIn cap P H x)
    (hx : srcStep P.env H x = .next x') : FitsIn cap P H x' := by
  intro n y hy
  exact h (n + 1) y (by simp only [runN, hx]; exact hy)

theorem FitsIn.now {cap : Nat} {P : Prog} {H : Host σ} {x : Cfg × σ} (h : FitsIn cap P H x) :
    P.sb + 4 * P.frameWords * x.1.frames.length ≤ cap :=
  h 0 x rfl

end Silmaril.Wasm.FX.Asyncify.Tool
