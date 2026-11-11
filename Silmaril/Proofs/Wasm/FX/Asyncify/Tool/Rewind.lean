module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Unwind

/-!
# Rewinding: re-entering the saved frames, outermost first
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-! ## Reading records back -/

theorem writeRecs_lt {F : Nat} {x : Nat} : ∀ {mem : Nat → W} {a : Nat} {rs : List (List W)},
    x < a → writeRecs F mem a rs x = mem x
  | _, _, [], _ => rfl
  | mem, a, r :: rs, h => by
    simp only [writeRecs]
    rw [writeRecs_lt (by omega), writeWords_lt h]

theorem readWords_congr {m1 m2 : Nat → W} {a n : Nat}
    (h : ∀ j < n, m1 (a + 4 * j) = m2 (a + 4 * j)) : readWords m1 a n = readWords m2 a n := by
  apply List.ext_getElem (by simp [readWords])
  intro j h1 _
  simp only [readWords, List.getElem_map, List.getElem_range]
  exact h j (by simpa [readWords] using h1)

/-- Records `rs` of the waiting frames `tw` are at `a, a + 4F, …`. -/
def RecsAt (F : Nat) (M : Nat → W) : Nat → List Nat → List Frame → Prop
  | a, k :: ks, w :: tw => readWords M a F = recOf F k w.locals ∧ RecsAt F M (a + 4 * F) ks tw
  | _, _, _ => True

theorem recsAt_writeRecs {F : Nat} (hF : 1 ≤ F) : ∀ {mem : Nat → W} {a : Nat} {ks : List Nat}
    {tw : List Frame}, (∀ w ∈ tw, w.locals.length = F) →
    RecsAt F (writeRecs F mem a (recs F ks tw)) a ks tw
  | _, _, [], _, _ => by simp [RecsAt]
  | _, _, _ :: _, [], _ => by simp [RecsAt]
  | mem, a, k :: ks, w :: tw, hl => by
    simp only [RecsAt, recs, writeRecs]
    refine ⟨?_, recsAt_writeRecs hF (fun v hv => hl v (by simp [hv]))⟩
    rw [readWords_congr (m2 := writeWords mem a (recOf F k w.locals)) (fun j hj => writeRecs_lt
      (by omega))]
    have := readWords_writeWords (mem := mem) (a := a) (ws := recOf F k w.locals)
    rw [recOf_length (hl w (by simp)) hF] at this
    exact this

/-- `RecsAt` survives writes below its base. -/
theorem recsAt_mono {F : Nat} {M M' : Nat → W} : ∀ {a : Nat} {ks : List Nat} {tw : List Frame},
    (∀ x, a ≤ x → M' x = M x) → RecsAt F M a ks tw → RecsAt F M' a ks tw
  | _, [], _, _, _ => by simp [RecsAt]
  | _, _ :: _, [], _, _ => by simp [RecsAt]
  | a, k :: ks, w :: tw, h, ⟨h1, h2⟩ => by
    refine ⟨?_, recsAt_mono (fun x hx => h x (by omega)) h2⟩
    rw [← h1]
    exact readWords_congr fun j _ => h _ (by omega)

/-! ## Rewind-mode segments -/

theorem seg_eq2_rw (ls ops : List W) (sp : W) (m : Nat → W) :
    runSeg [gState, c32 2, eqI] ⟨ls, ops, [2, sp], m⟩ = some ⟨ls, 1 :: ops, [2, sp], m⟩ := rfl

theorem seg_ne2_rw (ls ops : List W) (sp : W) (m : Nat → W) :
    runSeg [gState, c32 2, neI] ⟨ls, ops, [2, sp], m⟩ = some ⟨ls, 0 :: ops, [2, sp], m⟩ := rfl

theorem bool32_beq_ofNat {k j : Nat} (hk : k < 2 ^ 32) (hj : j < 2 ^ 32) :
    Numerics.bool32 (BitVec.ofNat 32 k == BitVec.ofNat 32 j) = if k = j then 1 else 0 := by
  by_cases h : k = j
  · subst h; simp [Numerics.bool32]
  · have : (BitVec.ofNat 32 k == BitVec.ofNat 32 j) = false := by
      rw [beq_eq_false_iff_ne]; exact ofNat32_ne hk hj h
    simp [Numerics.bool32, this, h]

theorem seg_sel {ls ops : List W} {g : List W} {m : Nat → W} {F k j : Nat}
    (hl : ls.length = F) (hF : 1 ≤ F) (hF2 : F < 2 ^ 32) (hsel : ls[F - 1]? = some (BitVec.ofNat 32 k))
    (hk : k < 2 ^ 32) (hj : j < 2 ^ 32) :
    runSeg [.localGet (lidx (F - 1)), c32 j, eqI] ⟨ls, ops, g, m⟩ =
      some ⟨ls, (if k = j then 1 else 0) :: ops, g, m⟩ := by
  have h1 : (lidx (F - 1)).value.val = F - 1 := lidx_val (by omega)
  have h2 : ls[F - 1] = BitVec.ofNat 32 k := by
    rw [List.getElem?_eq_getElem (by omega)] at hsel; exact Option.some.inj hsel
  simp only [runSeg, segStep, ctlOf, segCore, pexec, h1, List.getElem?_eq_getElem
    (show F - 1 < ls.length by omega), Option.map_some, Option.bind_some, c32, eqI,
    Numerics.intRelOp, h2]
  rw [← bool32_beq_ofNat hk hj]
  rfl

theorem steps_ite {E : Env} {fr : Frame} {rest : List Frame} {g : List W} {m : Nat → W}
    {seg t e K : List Instr} {x : W} {ops : List W} {ls : List W} {g' : List W}
    (h : runSeg seg ⟨fr.locals, fr.ops, g, m⟩ = some ⟨ls, x :: ops, g', m⟩) :
    Steps E (seg.length + 1) ⟨{ fr with code := seg ++ .if_ .empty t e :: K } :: rest, g, m⟩
      ⟨{ fr with locals := ls, ops := ops, code := (if x = 0 then e else t) ++ K } :: rest, g', m⟩ := by
  have h1 := steps_seg (E := E) (fr := fr) (rest := rest) (code := .if_ .empty t e :: K) h
  have h2 : step E ⟨{ fr with locals := ls, ops := x :: ops, code := .if_ .empty t e :: K } :: rest,
      g', m⟩ = .next ⟨{ fr with locals := ls, ops := ops, code := (if x = 0 then e else t) ++ K } ::
        rest, g', m⟩ :=
    step_if (fr := { fr with locals := ls, ops := x :: ops, code := .if_ .empty t e :: K }) rfl rfl rfl
  exact h1.trans (.one h2)

theorem sub_ofNat32 (a b : Nat) : BitVec.ofNat 32 (a + b) - BitVec.ofNat 32 b = BitVec.ofNat 32 a := by
  rw [← BitVec.ofNat_add_ofNat]; simp

/-- The prologue in rewind mode: pop a record and reload the locals. -/
theorem steps_prologue_rw {E : Env} {fr : Frame} {rest : List Frame} {K : List Instr} {F a : Nat}
    {M : Nat → W} (hl : fr.locals.length = F) (ha : a + 4 * F < 2 ^ 32) :
    ∃ n, Steps E n ⟨{ fr with code := prologue F ++ K } :: rest, [2, BitVec.ofNat 32 (a + 4 * F)], M⟩
      ⟨{ fr with locals := readWords M a F, code := K } :: rest, [2, BitVec.ofNat 32 a], M⟩ := by
  have e1 := steps_ite (E := E) (fr := fr) (rest := rest) (t := restoreCode F) (e := []) (K := K)
    (seg_eq2_rw fr.locals fr.ops (BitVec.ofNat 32 (a + 4 * F)) M)
  have hseg : runSeg (restoreCode F) ⟨fr.locals, fr.ops, [2, BitVec.ofNat 32 (a + 4 * F)], M⟩ =
      some ⟨readWords M a F, fr.ops, [2, BitVec.ofNat 32 a], M⟩ := by
    unfold restoreCode
    rw [runSeg_append]
    have h1 : runSeg [gSp, c32 (4 * F), subI, sSp] ⟨fr.locals, fr.ops, [2, BitVec.ofNat 32 (a + 4 * F)],
        M⟩ = some ⟨fr.locals, fr.ops, [2, BitVec.ofNat 32 a], M⟩ := by
      have hs := sub_ofNat32 a (4 * F)
      simp only [runSeg, segStep, ctlOf, segCore, gSp, sSp, c32, subI, pexec, Numerics.intBinOp]
      simp only [Option.bind_some]
      rw [← hs]; rfl
    rw [h1, Option.bind_some, loadLocals_seg (sp := BitVec.ofNat 32 a) rfl (by simp [hl])
      (by omega), toNat_ofNat32 (by omega)]
    simp
  have e2 := steps_seg (E := E) (fr := { fr with code := [] }) (rest := rest) (code := K) hseg
  refine ⟨_, Steps.trans (by simpa [prologue, ifThen] using e1) (by simpa using e2)⟩

end Silmaril.Wasm.FX.Asyncify.Tool
