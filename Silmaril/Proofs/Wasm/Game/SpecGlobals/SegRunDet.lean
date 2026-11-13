module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Det
public import Silmaril.Proofs.Wasm.Game.Machine.SoftJoin

/-!
# Deterministic instructions under an arbitrary profile

Under an arbitrary silmaril profile `P`, a host-free step whose first non-value is a `Good`
instruction is unique (`good_step_uniq`). `Good` instructions are the integer binary
operators, global reads, the reference and aggregate constant instructions, `table.set`,
`table.init`, `elem.drop`, the stores, `memory.init` and `data.drop`: the instructions of
segment initialisation and of constant expressions. The profile only enters floating-point,
vector and `grow` rules, none of which is `Good`.

Source: the family comparisons reuse silmaril-lean's `fam_det` tactics
(`Silmaril/Wasm/SingleThreaded/Determinism/FamDet*.lean`, pinned revision) with the profile
left arbitrary; the reduction to heads follows `Silmaril.Proofs.Wasm.Game.Choice.headDec_soft`.
New.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded.Det Silmaril.Proofs.Wasm.Game.Choice

variable {H : Type}

/-- The instructions whose steps are unique under every profile. -/
def Good : Instr → Prop
  | .intBinOp _ _ | .globalGet _ | .refFunc _ | .refNull _ | .refI31 | .anyConvertExtern
  | .externConvertAny | .structNew _ | .structNewDefault _ | .arrayNew _ | .arrayNewDefault _
  | .arrayNewFixed _ _ | .tableSet _ | .tableInit _ _ | .elemDrop _ | .intStore _ _ _ _
  | .memoryInit _ _ | .dataDrop _ => True
  | _ => False

theorem good_fam {i : Instr} (hg : Good i) : famOf (.plain i) ≠ .control := by
  cases i <;> first | exact hg.elim | (intro h; cases h)

theorem numeric_det_int {P : Profile} {l₁ l₂ r₁ r₂ : List Admin} {p : List Val} {t : IntType}
    {op : IntBinOp} (h₁ : NumericStep P l₁ r₁) (h₂ : NumericStep P l₂ r₂)
    (hl : l₁ = vals p ++ l₂) (hlast : l₂.getLast? = some (.plain (.intBinOp t op))) :
    p = [] ∧ r₁ = r₂ := by
  cases h₁ <;> cases h₂ <;> first | (simp at hlast; done) | fam_det

theorem table_det_nogrow {P : Profile} {s : Store H} {f : Frame} {l₁ l₂ : List Admin}
    {c₁ c₂ : Config H} {p : List Val} (h₁ : TableStep P ⟨s, f, l₁⟩ c₁)
    (h₂ : TableStep P ⟨s, f, l₂⟩ c₂) (hl : l₁ = vals p ++ l₂)
    (hng : ∀ x, l₂.getLast? ≠ some (.plain (.tableGrow x))) : p = [] ∧ c₁ = c₂ := by
  cases h₁ <;> cases h₂ <;> first | (exfalso; exact hng _ rfl) | fam_det

set_option linter.unusedTactic false in
theorem memory_det_nogrow {P : Profile} {s : Store H} {f : Frame} {l₁ l₂ : List Admin}
    {c₁ c₂ : Config H} {p : List Val} (h₁ : MemoryStep P ⟨s, f, l₁⟩ c₁)
    (h₂ : MemoryStep P ⟨s, f, l₂⟩ c₂) (hl : l₁ = vals p ++ l₂)
    (hng : ∀ x, l₂.getLast? ≠ some (.plain (.memoryGrow x))) : p = [] ∧ c₁ = c₂ := by
  cases h₁ <;> cases h₂ <;> first
    | (exfalso; exact hng _ rfl)
    | (fam_pre ; all_goals first
      | fam_post
      | (have := Memory.load_bound ‹_›; (try simp_all); (try casesm* _ ∧ _); (try subst_vars);
         (try omega))
      | (have := Memory.store_bound ‹_›; (try simp_all); (try casesm* _ ∧ _); (try subst_vars);
         (try omega)))

theorem getLast_args (args : List Val) (e : Admin) : (vals args ++ [e]).getLast? = some e := by
  simp

/-- Two choice-family heads at the same `Good` instruction. -/
theorem good_choice_det {P : Profile} {s : Store H} {f : Frame} {args₁ args₂ p : List Val}
    {i : Instr} {c₁ c₂ : Config H} (hg : Good i) (hk : ChoiceFam (famOf (.plain i)))
    (f₁ : FamRel P (famOf (.plain i)) s f (vals args₁ ++ [.plain i]) c₁)
    (f₂ : FamRel P (famOf (.plain i)) s f (vals args₂ ++ [.plain i]) c₂)
    (hp : args₁ = p ++ args₂) : p = [] ∧ c₁ = c₂ := by
  have hl : vals args₁ ++ [Admin.plain i] = vals p ++ (vals args₂ ++ [.plain i]) := by
    subst hp; simp
  have hlast := getLast_args args₂ (.plain i)
  cases i <;> try first | exact hg.elim | exact hk.elim
  all_goals simp only [famOf] at f₁ f₂
  case intBinOp =>
    obtain ⟨_, n₁, rfl⟩ := f₁
    obtain ⟨_, n₂, rfl⟩ := f₂
    obtain ⟨hp', he⟩ := numeric_det_int n₁ n₂ hl hlast
    exact ⟨hp', by rw [he]⟩
  case tableSet | tableInit | elemDrop =>
    exact table_det_nogrow f₁ f₂ hl (fun x h => by rw [hlast] at h; cases h)
  case intStore | memoryInit | dataDrop =>
    exact memory_det_nogrow f₁ f₂ hl (fun x h => by rw [hlast] at h; cases h)

/-- Two heads at the same `Good` instruction. -/
theorem good_head_det {P : Profile} {s : Store H} {f : Frame} {args₁ args₂ p : List Val}
    {i : Instr} {c₁ c₂ : Config H} (hg : Good i) (hh₁ : Head P s f args₁ (.plain i) c₁)
    (hh₂ : Head P s f args₂ (.plain i) c₂) (hp : args₁ = p ++ args₂) : p = [] ∧ c₁ = c₂ := by
  have hc := good_fam hg
  by_cases hk : ChoiceFam (famOf (.plain i))
  · exact good_choice_det hg hk (hh₁.fam_inv hc) (hh₂.fam_inv hc) hp
  · exact det_fam_free hc hk hh₁ hh₂ hp

/-- A step at a `Good` first non-value is a head step. -/
theorem good_headDec {P : Profile} {s : Store H} {f : Frame} {W : List Val} {i : Instr}
    {R : List Admin} {c : Config H} (hg : Good i)
    (h : Step P noHost ⟨s, f, vals W ++ .plain i :: R⟩ c) :
    ∃ vs args c₀, W = vs ++ args ∧ Head P s f args (.plain i) c₀ ∧
      c = ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ R⟩ := by
  have hf : fnv (vals W ++ .plain i :: R) = (W, .plain i :: R) := by
    simp [fnv_cons_of_none (a := .plain i) (by cases i <;> first | exact hg.elim | rfl)]
  rcases Step.decomp h with hd | hb
  · obtain ⟨vs, args, e, rest, c₀, hf', -, hh, hc⟩ := fnv_headDec hd
    have heq : vs ++ args = W ∧ e = .plain i ∧ rest = R := by
      simpa only [Prod.mk.injEq, List.cons.injEq] using hf'.symm.trans hf
    obtain ⟨hW, he, hR⟩ := heq
    refine ⟨vs, args, c₀, hW.symm, he ▸ hh, ?_⟩
    rw [hc, hR]
  · obtain ⟨p, q, u, r, -, ⟨hf', -, -⟩ | ⟨a, hf', -, -⟩⟩ := fnv_bubble hb
    · have e := hf'.symm.trans hf
      simp only [Prod.mk.injEq, List.cons.injEq, reduceCtorEq, false_and, and_false] at e
    · have e := hf'.symm.trans hf
      simp only [Prod.mk.injEq, List.cons.injEq, Admin.plain.injEq] at e
      obtain ⟨-, rfl, -⟩ := e
      exact hg.elim

/-- **Steps at a `Good` first non-value are unique**, every profile. -/
theorem good_step_uniq {P : Profile} {s : Store H} {f : Frame} {W : List Val} {i : Instr}
    {R : List Admin} {c₁ c₂ : Config H} (hg : Good i)
    (h₁ : Step P noHost ⟨s, f, vals W ++ .plain i :: R⟩ c₁)
    (h₂ : Step P noHost ⟨s, f, vals W ++ .plain i :: R⟩ c₂) : c₁ = c₂ := by
  obtain ⟨vs₁, a₁, d₁, hW₁, hh₁, rfl⟩ := good_headDec hg h₁
  obtain ⟨vs₂, a₂, d₂, hW₂, hh₂, rfl⟩ := good_headDec hg h₂
  have hva : vs₁ ++ a₁ = vs₂ ++ a₂ := hW₁.symm.trans hW₂
  rcases append_eq_append_suffix hva with ⟨p, hp⟩ | ⟨p, hp⟩
  · obtain ⟨hp0, rfl⟩ := good_head_det hg hh₁ hh₂ hp
    have ha : a₁ = a₂ := by simpa [hp0] using hp
    have hvs : vs₁ = vs₂ := List.append_cancel_right (ha ▸ hva)
    rw [hvs]
  · obtain ⟨hp0, rfl⟩ := good_head_det hg hh₂ hh₁ hp
    have ha : a₂ = a₁ := by simpa [hp0] using hp
    have hvs : vs₁ = vs₂ := List.append_cancel_right (ha ▸ hva)
    rw [hvs]

end Silmaril.Proofs.Wasm.Game.SpecGlobals
