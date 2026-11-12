module

public import Silmaril.Proofs.Machine.OfLambdaSSA.Backward
public import Silmaril.Proofs.Machine.OfLambdaSSA.Sound

/-!
# The function at the root

The compiled function's block `0` holds what the root region compiled to, and
every block the compilation emitted sits at its label. The root region is
either compiled directly, as block `0`, or it is the wrapper
`cfg (br 0 (var 0)) 1 blocks`, whose block becomes block `0` itself. In both
cases a run from block `0` returns or traps exactly when the region leaves
through label `0` or `1`.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.OfLambdaSSA

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (extend)

variable {sigs : List Silmaril.Machine.RTL.Signature} {oracle : CallOracle}

/-- The compiler's initial state for a function taking `params` words. -/
def start (params : ℕ) : Emit := { nextReg := params, nextLabel := 1, blocks := [] }

/-- The function `ofLambdaSSA?` assembles around a compiled root. -/
def rootFn (params results : ℕ) (ops : List (Op ℕ)) (t : Term ℕ) (e : Emit) : SSA.Func ℕ :=
  { sig := ⟨params, results⟩, entry := 0,
    blocks := assemble e.nextLabel ((0, ⟨freshRegs 0 params, ops, t⟩) :: e.blocks) }

/-- The labels the root of a function exits through: return and trap. -/
abbrev rootLabels (results : ℕ) : List (Target × ℕ) := [(.ret, results), (.trap, 0)]

/-- **Every emitted block is at its label.** -/
theorem inst_root {r : Region (Opcode sigs)} {a : Ann} {ρ : List (List ℕ)} {L : List (Target × ℕ)}
    {params results : ℕ} {ops : List (Op ℕ)} {t : Term ℕ} {e : Emit}
    (h : regionOps r a ρ L (start params) = some (ops, t, e)) :
    Inst (rootFn params results ops t e) ((0, ⟨freshRegs 0 params, ops, t⟩) :: e.blocks) := by
  obtain ⟨-, hl, pre, hb, hk, hkn, -, -⟩ := regionOps_grew r a ρ L _ _ h
  simp only [start, List.append_nil] at hb hl hk
  have hnd : (((0, (⟨freshRegs 0 params, ops, t⟩ : SSA.Block ℕ)) :: e.blocks).map Prod.fst).Nodup := by
    rw [hb, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => by
      obtain ⟨q, hq, hq0⟩ := List.mem_map.mp hm
      have := (hk q hq).1
      omega, hkn⟩
  intro p hp
  have hlt : p.1 < e.nextLabel := by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hl
    · exact (hk p (hb ▸ hp)).2
  show (assemble _ _)[p.1]? = some p.2
  rw [assemble_getElem? hlt, lookup_of_mem hnd hp]
  rfl

/-- Setting a register to the word it holds changes nothing. -/
theorem set_self {fr : Frame ℕ} {x : ℕ} {w : Word} (h : fr.get x = some w) : fr.set x w = fr := by
  cases fr with
  | mk regs =>
    show Frame.mk _ = _
    congr 1
    funext y
    by_cases hy : y = x
    · subst hy
      simpa [Frame.get] using h.symm
    · simp [hy]

/-- Writing a frame's own words back changes nothing. -/
theorem writeAll_self {fr : Frame ℕ} :
    ∀ {ps : List ℕ} {vs : List Word}, fr.readAll ps = some vs → fr.writeAll ps vs = some fr
  | [], _, h => by
    obtain rfl : _ = [] := (Option.some.inj h).symm
    rfl
  | p :: ps, _, h => by
    obtain ⟨w, ws, hw, hws, rfl⟩ := readAll_cons_eq_some.mp h
    show (fr.set p w).writeAll ps ws = some fr
    rw [set_self hw]
    exact writeAll_self hws

variable (oracle) in
/-- What a run of a compiled function does, given how its root region left. -/
def RootOutcome (fn : SSA.Func ℕ) (fr : Frame ℕ) (m : Memory) (ℓ : ℕ) (v : Value Word)
    (m' : Memory) : Prop :=
  (ℓ = 0 ∧ ∃ vs, v = packValues vs ∧ Func.Exec oracle fn 0 fr m (.returned vs m')) ∨
    (ℓ = 1 ∧ v = .unit ∧ Func.Exec oracle fn 0 fr m (.trapped m'))

/-- The outcome a root exit selects. -/
def rootExit (ℓ : ℕ) (vs : List Word) (m' : Memory) : Exit :=
  if ℓ = 0 then .returned vs m' else .trapped m'

/-- Leaving the root through a label it has is a run to the matching exit. -/
theorem cont_root {E : Label → Frame ℕ → Memory → Exit → Prop} {fn : SSA.Func ℕ} {results ℓ : ℕ}
    {vs ws : List Word} {frX : Frame ℕ} {m' : Memory} (hvs : packValues vs = packValues ws) :
    ℓ < 2 → Cont fn E (rootLabels results) ℓ ws frX m' (rootExit ℓ vs m') := by
  intro hℓ
  obtain rfl := packValues_injective hvs
  match ℓ, hℓ with
  | 0, _ => rfl
  | 1, _ => rfl

/-- A root exit, read back as an outcome. -/
theorem outcome_of_exit {fn : SSA.Func ℕ} {fr : Frame ℕ} {m m' : Memory} {results : ℕ}
    {ℓ : ℕ} {vs : List Word} (hok : ExitOk [results, 0] ℓ (packValues vs))
    (hex : Func.Exec oracle fn 0 fr m (rootExit ℓ vs m')) :
    RootOutcome oracle fn fr m ℓ (packValues vs) m' := by
  obtain ⟨w, ws, hw, hv, hlen⟩ := hok
  obtain rfl := packValues_injective hv
  match ℓ, hw with
  | 0, _ => exact Or.inl ⟨rfl, vs, rfl, hex⟩
  | 1, hw =>
    obtain rfl : w = 0 := by simpa using hw.symm
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hlen
    exact Or.inr ⟨rfl, rfl, hex⟩

end Silmaril.Proofs.Machine.OfLambdaSSA
