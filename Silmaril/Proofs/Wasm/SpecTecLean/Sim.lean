module

public import Silmaril.Proofs.Wasm.SpecTecLean.Corr
public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Thms

/-!
# Their rules against our declarative reading of the pinned IL

Each Core shape of `Defs` is simulated by our reading of SpecTec's whole `Step` relation
(`FwdP`, from the existing forward lemmas of `Silmaril.Wasm.SpecTec.Sim.IntNumeric`), and a firing
of the same rule of our `Step_pure` (`Fires (simEnv B) "Step_pure" k`) at the image of a Core
sequence has that shape (the inversions here follow the `bwd_*` proofs of `BackwardParam`, but
keep the rule's shape). Composed with `Corr`, their rule implies our whole step, and our rule
implies theirs.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTecLean

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.IntNumeric
open Silmaril.Wasm.Numerics (intBinOp)

variable {H : Type} {hn : H → String} {B : Builtins} {s : Store H} {f : Frame}
  {is js : List Admin} {I J : List SpecTecLean.instr} {w : Value}

/-! ## Core shape to our whole step -/

theorem fwd_coreUnreachable (T : TypingFacts (simEnv B) hn) (h : CoreUnreachable is js) :
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, js⟩ := by
  obtain ⟨rfl, rfl⟩ := h
  exact fwd_parametric T .unreachable

theorem fwd_coreNop (T : TypingFacts (simEnv B) hn) (h : CoreNop is js) :
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, js⟩ := by
  obtain ⟨rfl, rfl⟩ := h
  exact fwd_parametric T .nop

theorem fwd_coreDrop (T : TypingFacts (simEnv B) hn) (h : CoreDrop is js) :
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, js⟩ := by
  obtain ⟨v, rfl, rfl⟩ := h
  exact fwd_parametric T (.drop v)

theorem fwd_coreSelectTrue (T : TypingFacts (simEnv B) hn) (h : CoreSelectTrue is js) :
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, js⟩ := by
  obtain ⟨v₁, v₂, c, ts, hc, rfl, rfl⟩ := h
  exact fwd_parametric T (.selectTrue hc)

theorem fwd_coreSelectFalse (T : TypingFacts (simEnv B) hn) (h : CoreSelectFalse is js) :
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, js⟩ := by
  obtain ⟨v₁, v₂, ts, rfl, rfl⟩ := h
  exact fwd_parametric T (.selectFalse v₁ v₂ ts)

theorem fwd_coreAdd (hB : IntB B) (T : TypingFacts (simEnv B) hn) (h : CoreAdd is js) :
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, js⟩ := by
  obtain ⟨t, x, y, rfl, rfl⟩ := h
  exact fwd_intBinOp hB (intTyping_simEnv B) T rfl

/-! ## Our rule to the Core shape -/

theorem fires_unreachable_inv
    (hf : Fires (simEnv B) "Step_pure" 0 (.tuple [.list (adminsToV is), w])) :
    ∃ js, w = .list (adminsToV js) ∧ CoreUnreachable is js := by
  obtain ⟨σ, -, he, -⟩ := fires_body (hasPureRules_simEnv B).unreachable hf
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  obtain ⟨vs, hvs, h1⟩ := evalExp_listE_inv hl
  have hw : w = .list [.case "TRAP" (.tuple [])] := rhs_trap_inv hr
  rcases h1 with _ | ⟨e₁, h1⟩
  cases h1
  obtain rfl := evalExp_nullary_inv e₁
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_one (Value.list.inj hvs)
  obtain ⟨i, rfl, hi⟩ := dec_admin_plain ha (by decide)
  obtain rfl := dec_unreachable hi
  exact ⟨[.trap], hw, rfl, rfl⟩

theorem fires_nop_inv (hf : Fires (simEnv B) "Step_pure" 1 (.tuple [.list (adminsToV is), w])) :
    ∃ js, w = .list (adminsToV js) ∧ CoreNop is js := by
  obtain ⟨σ, -, he, -⟩ := fires_body (hasPureRules_simEnv B).nop hf
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  obtain ⟨vs, hvs, h1⟩ := evalExp_listE_inv hl
  obtain ⟨ws, hws, h2⟩ := evalExp_listE_inv hr
  rcases h1 with _ | ⟨e₁, h1⟩
  cases h1
  cases h2
  obtain rfl := evalExp_nullary_inv e₁
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_one (Value.list.inj hvs)
  obtain ⟨i, rfl, hi⟩ := dec_admin_plain ha (by decide)
  obtain rfl := dec_nop hi
  exact ⟨[], hws, rfl, rfl⟩

theorem fires_drop_inv (hf : Fires (simEnv B) "Step_pure" 2 (.tuple [.list (adminsToV is), w])) :
    ∃ js, w = .list (adminsToV js) ∧ CoreDrop is js := by
  obtain ⟨σ, hq, he, -⟩ := fires_body (hasPureRules_simEnv B).drop hf
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  obtain ⟨v, rfl⟩ := drop_lhs_inv hq hl
  obtain ⟨ws, hws, h2⟩ := evalExp_listE_inv hr
  cases h2
  exact ⟨[], hws, v, rfl, rfl⟩

theorem fires_selectTrue_inv
    (hf : Fires (simEnv B) "Step_pure" 3 (.tuple [.list (adminsToV is), w])) :
    ∃ js, w = .list (adminsToV js) ∧ CoreSelectTrue is js := by
  obtain ⟨σ, hq, he, hp⟩ := fires_body (hasPureRules_simEnv B).selectTrue hf
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  obtain ⟨v₁, v₂, b, ts, rfl, h₁, -, hc⟩ := select_lhs_inv hq hl
  obtain ⟨ws, hws, h1⟩ := evalExp_listE_inv hr
  rcases h1 with _ | ⟨e₅, h1⟩
  cases h1
  have h₅ : _ = some _ := evalExp_varE_iff.1 (evalExp_subE_iff.1 e₅)
  rw [h₁] at h₅
  cases h₅
  obtain ⟨x₁, x₂, hx₁, hx₂, hne⟩ := evalExp_cmpE_iff.1 (prem_if hp)
  obtain rfl := payload_eq hc hx₁
  obtain rfl := evalExp_numE_iff.1 hx₂
  have hb : b ≠ 0 := fun h0 => by subst h0; simp [cmpValues, natV] at hne
  exact ⟨[v₁.toAdmin], hws, v₁, v₂, b, ts, hb, rfl, rfl⟩

theorem fires_selectFalse_inv
    (hf : Fires (simEnv B) "Step_pure" 4 (.tuple [.list (adminsToV is), w])) :
    ∃ js, w = .list (adminsToV js) ∧ CoreSelectFalse is js := by
  obtain ⟨σ, hq, he, hp⟩ := fires_body (hasPureRules_simEnv B).selectFalse hf
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  obtain ⟨v₁, v₂, b, ts, rfl, -, h₂, hc⟩ := select_lhs_inv hq hl
  obtain ⟨ws, hws, h1⟩ := evalExp_listE_inv hr
  rcases h1 with _ | ⟨e₅, h1⟩
  cases h1
  have h₅ : _ = some _ := evalExp_varE_iff.1 (evalExp_subE_iff.1 e₅)
  rw [h₂] at h₅
  cases h₅
  obtain ⟨v, hx₁, hx₂⟩ := evalExp_eq_true (prem_if hp)
  obtain rfl := payload_eq hc hx₁
  have h0 : b.toNat = 0 := by simpa [natV] using evalExp_numE_iff.1 hx₂
  obtain rfl : b = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
  exact ⟨[v₂.toAdmin], hws, v₁, v₂, ts, rfl, rfl⟩

/-- `binop-val` at the image of a Core sequence: an integer operator that does not trap, or a
float operator (which the fragment excludes). -/
theorem fires_binopVal_inv (hB : IntB B)
    (hf : Fires (simEnv B) "Step_pure" 48 (.tuple [.list (adminsToV is), w])) :
    (∃ (t : IntType) (bop : IntBinOp) (x y z : BitVec t.width), intBinOp t bop x y = .ok z ∧
      is = [.plain (.intConst t x), .plain (.intConst t y), .plain (.intBinOp t bop)] ∧
      w = .list (adminsToV [.plain (.intConst t z)])) ∨
      (∃ t op, Admin.plain (.floatBinOp t op) ∈ is) := by
  obtain ⟨σ, -, he, hp⟩ := fires_body (hasNumericRules_simEnv B).binopVal hf
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := list3_inv hl
  rcases binop_dec h₁ h₂ h₃ with ⟨t, bop, x, y, rfl, rfl, rfl, hnt, hx, hy, hop⟩ |
    ⟨t, bop, rfl⟩
  · obtain ⟨z, hz, rfl⟩ := binopVal_finish hB hnt hx hy hop hr hp
    exact .inl ⟨t, bop, x, y, z, hz, rfl, rfl⟩
  · exact .inr ⟨t, bop, by simp⟩

/-! ## Their rule implies our whole step; our rule implies theirs -/

theorem fwd_of_slUnreachable (T : TypingFacts (simEnv B) hn) (hI : slAdmins? is = some I)
    (hJ : slAdmins? js = some J) (h : SLUnreachable I J) :
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, js⟩ :=
  fwd_coreUnreachable T ((slUnreachable_iff hI hJ).1 h)

theorem fwd_of_slNop (T : TypingFacts (simEnv B) hn) (hI : slAdmins? is = some I)
    (hJ : slAdmins? js = some J) (h : SLNop I J) : FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, js⟩ :=
  fwd_coreNop T ((slNop_iff hI hJ).1 h)

theorem fwd_of_slDrop (T : TypingFacts (simEnv B) hn) (hI : slAdmins? is = some I)
    (hJ : slAdmins? js = some J) (h : SLDrop I J) : FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, js⟩ :=
  fwd_coreDrop T ((slDrop_iff hI hJ).1 h)

theorem fwd_of_slSelectTrue (T : TypingFacts (simEnv B) hn) (hI : slAdmins? is = some I)
    (hJ : slAdmins? js = some J) (h : SLSelectTrue I J) :
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, js⟩ :=
  fwd_coreSelectTrue T ((slSelectTrue_iff hI hJ).1 h)

theorem fwd_of_slSelectFalse (T : TypingFacts (simEnv B) hn) (hI : slAdmins? is = some I)
    (hJ : slAdmins? js = some J) (h : SLSelectFalse I J) :
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, js⟩ :=
  fwd_coreSelectFalse T ((slSelectFalse_iff hI hJ).1 h)

theorem fwd_of_slBinopVal (hB : IntB B) (T : TypingFacts (simEnv B) hn)
    (hI : slAdmins? is = some I) (hJ : slAdmins? js = some J) (h : SLBinopVal I J) :
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, js⟩ :=
  fwd_coreAdd hB T ((slBinopVal_add_iff hI hJ).1 h)

theorem sl_of_fires_unreachable (hI : slAdmins? is = some I)
    (hf : Fires (simEnv B) "Step_pure" 0 (.tuple [.list (adminsToV is), w])) :
    ∃ js J, w = .list (adminsToV js) ∧ slAdmins? js = some J ∧ SLUnreachable I J := by
  obtain ⟨js, hw, hc⟩ := fires_unreachable_inv hf
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨[.trap], [.TRAP], hw, rfl, (slUnreachable_iff hI rfl).2 ⟨rfl, rfl⟩⟩

theorem sl_of_fires_nop (hI : slAdmins? is = some I)
    (hf : Fires (simEnv B) "Step_pure" 1 (.tuple [.list (adminsToV is), w])) :
    ∃ js J, w = .list (adminsToV js) ∧ slAdmins? js = some J ∧ SLNop I J := by
  obtain ⟨js, hw, hc⟩ := fires_nop_inv hf
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨[], [], hw, rfl, (slNop_iff hI rfl).2 ⟨rfl, rfl⟩⟩

theorem sl_of_fires_drop (hI : slAdmins? is = some I)
    (hf : Fires (simEnv B) "Step_pure" 2 (.tuple [.list (adminsToV is), w])) :
    ∃ js J, w = .list (adminsToV js) ∧ slAdmins? js = some J ∧ SLDrop I J := by
  obtain ⟨js, hw, hc⟩ := fires_drop_inv hf
  obtain ⟨v, rfl, rfl⟩ := hc
  exact ⟨[], [], hw, rfl, (slDrop_iff hI rfl).2 ⟨v, rfl, rfl⟩⟩

theorem sl_of_fires_selectTrue (hI : slAdmins? is = some I)
    (hf : Fires (simEnv B) "Step_pure" 3 (.tuple [.list (adminsToV is), w])) :
    ∃ js J, w = .list (adminsToV js) ∧ slAdmins? js = some J ∧ SLSelectTrue I J := by
  obtain ⟨js, hw, hc⟩ := fires_selectTrue_inv hf
  obtain ⟨v₁, v₂, k, ts, hk, rfl, rfl⟩ := hc
  obtain ⟨t₁, b₁, t₂, b₂, rfl, rfl, rfl, -⟩ := select_img hI
  exact ⟨_, _, hw, rfl, (slSelectTrue_iff hI rfl).2 ⟨_, _, k, none, hk, rfl, rfl⟩⟩

theorem sl_of_fires_selectFalse (hI : slAdmins? is = some I)
    (hf : Fires (simEnv B) "Step_pure" 4 (.tuple [.list (adminsToV is), w])) :
    ∃ js J, w = .list (adminsToV js) ∧ slAdmins? js = some J ∧ SLSelectFalse I J := by
  obtain ⟨js, hw, hc⟩ := fires_selectFalse_inv hf
  obtain ⟨v₁, v₂, ts, rfl, rfl⟩ := hc
  obtain ⟨t₁, b₁, t₂, b₂, rfl, rfl, rfl, -⟩ := select_img hI
  exact ⟨_, _, hw, rfl, (slSelectFalse_iff hI rfl).2 ⟨_, _, none, rfl, rfl⟩⟩

/-- An operator of the fragment is `add`. -/
theorem slAdmin?_intBinOp {t : IntType} {bop : IntBinOp} {x : SpecTecLean.instr}
    (h : slAdmin? (.plain (.intBinOp t bop)) = some x) : bop = .add := by
  cases bop <;> first | rfl | cases h

theorem sl_of_fires_binopVal (hB : IntB B) (hI : slAdmins? is = some I)
    (hf : Fires (simEnv B) "Step_pure" 48 (.tuple [.list (adminsToV is), w])) :
    ∃ js J, w = .list (adminsToV js) ∧ slAdmins? js = some J ∧ SLBinopVal I J := by
  rcases fires_binopVal_inv hB hf with ⟨t, bop, x, y, z, hz, rfl, hw⟩ | ⟨t, op, hmem⟩
  · obtain ⟨x₃, h₃⟩ := slAdmins?_mem hI (a := .plain (.intBinOp t bop)) (by simp)
    obtain rfl := slAdmin?_intBinOp h₃
    obtain rfl : z = x + y := (Except.ok.inj hz).symm
    exact ⟨_, _, hw, rfl, (slBinopVal_add_iff hI rfl).2 ⟨t, x, y, rfl, rfl⟩⟩
  · exact absurd (slAdmins?_mem hI hmem) (by simp [slAdmin?, slInstr?])

end Silmaril.Wasm.SpecTecLean
