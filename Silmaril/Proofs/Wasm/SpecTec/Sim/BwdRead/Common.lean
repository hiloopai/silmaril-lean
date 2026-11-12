module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdRead.Variable
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Values

/-!
# Shared readers for the table and memory rules

* `decode_aconst`: an instruction whose image is `CONST at (% p)` is an address-typed integer
  constant (a float's payload is `POS`/`NEG`, never `%`).
* `pct_of_proj`: the premise operand `i!%.0`, read back.
* `table_inv`, `tableLen_inv`, `elemLen_inv`: `$table(z, x)`, `|$table(z, x).REFS|` and
  `|$elem(z, y).REFS|` on an encoded state, read back into Core's `Store.table?`/`Store.elem?`.
* `gt_nat_inv`, `ge_nat_inv`, `lt_nat_inv`, `add_nat_inv`: the comparisons and the disjunction of the premises.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdRead

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV)

variable {H : Type} {hn : H → String}

/-- **An address-typed constant, decoded.** -/
theorem decode_aconst {a : Admin} {AT P : Value}
    (h : adminToV a = .case "CONST" (.tuple [AT, .case "%" P])) :
    ∃ (t : AddrType) (b : BitVec t.intType.width), a = aconst t b ∧ AT = Encode.toValue t ∧
      P = .tuple [.num (.natN b.toNat)] := by
  rcases Typing.head_const (Typing.adminToV_case h).symm with ⟨t, b, rfl⟩ | ⟨t, b, rfl⟩
  · cases t with
    | i32 =>
      have h' : valV (.num ⟨.int .i32, b⟩) = _ := h
      simp only [valV, numV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, and_true,
        Equiv.Execution.pctV, true_and] at h'
      exact ⟨.i32, b, rfl, h'.1.symm, h'.2.symm⟩
    | i64 =>
      have h' : valV (.num ⟨.int .i64, b⟩) = _ := h
      simp only [valV, numV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, and_true,
        Equiv.Execution.pctV, true_and] at h'
      exact ⟨.i64, b, rfl, h'.1.symm, h'.2.symm⟩
  · have h' : valV (.num ⟨.float t, b⟩) = _ := h
    simp only [valV, numV, floatV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq] at h'
    split at h' <;> simp at h'

/-- The operand `i!%.0` of a premise, read back from the binding of `i`. -/
theorem pct_of_proj {env : Env} {ρ : VarEnv} {x : IL.Id} {I v : Value}
    (fx : ρ.findVal? x = some I) (h : EvalExp env ρ (.projE (.uncaseE (.varE x) "%") 0) v) :
    ∃ vs, I = .case "%" (.tuple vs) ∧ vs[0]? = some v := by
  obtain ⟨vs, hvs, -, hv⟩ := evalExp_projE_iff.1 h
  exact ⟨vs, EvalExp.unique (evalExp_var fx) (evalExp_uncaseE_iff.1 hvs), hv⟩

/-- `p ≥ q` on natural numerals, read back. -/
theorem ge_nat_inv {p q : Nat}
    (h : cmpValues .geOp (.num (.natN p)) (.num (.natN q)) = .ok (.bool true)) : q ≤ p := by
  simpa [cmpValues, Num.cmp, Res.ofOption] using h

/-- `p < q` on natural numerals, read back. -/
theorem lt_nat_inv {p q : Nat}
    (h : cmpValues .ltOp (.num (.natN p)) (.num (.natN q)) = .ok (.bool true)) : p < q := by
  simpa [cmpValues, Num.cmp, Res.ofOption] using h

/-- `p > q` on natural numerals, read back. -/
theorem gt_nat_inv {p q : Nat}
    (h : cmpValues .gtOp (.num (.natN p)) (.num (.natN q)) = .ok (.bool true)) : q < p := by
  simpa [cmpValues, Num.cmp, Res.ofOption] using h

/-- `p + n` on natural numerals, read back: the second operand is a natural numeral too. -/
theorem add_nat_inv {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {p : Nat} {v : Value}
    (h₁ : EvalExp env ρ e₁ (.num (.natN p)))
    (h : EvalExp env ρ (.binE .addOp (.numT .natT) e₁ e₂) v) :
    ∃ q, EvalExp env ρ e₂ (.num (.natN q)) ∧ v = .num (.natN (p + q)) := by
  obtain ⟨v₁, h₁', hs | ⟨-, v₂, h₂, hb⟩⟩ := evalExp_binE_iff.1 h
  · simp [boolShort] at hs
  · have e₁ : v₁ = .num (.natN p) := EvalExp.unique h₁' h₁
    subst e₁
    cases v₂ with
    | num m =>
      cases m <;> simp [binValues, Num.bin, Res.ofOption] at hb
      exact ⟨_, h₂, hb.symm⟩
    | _ => simp [binValues] at hb

/-- The image of a four-instruction sequence. -/
theorem adminsToV_eq_quad {is : List Admin} {v₁ v₂ v₃ v₄ : Value}
    (h : adminsToV is = [v₁, v₂, v₃, v₄]) :
    ∃ a₁ a₂ a₃ a₄, is = [a₁, a₂, a₃, a₄] ∧ adminToV a₁ = v₁ ∧ adminToV a₂ = v₂ ∧
      adminToV a₃ = v₃ ∧ adminToV a₄ = v₄ := by
  match is, h with
  | [a₁, a₂, a₃, a₄], h =>
      simp only [adminsToV, List.cons.injEq] at h
      exact ⟨a₁, a₂, a₃, a₄, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  | [], h => simp [adminsToV] at h
  | [_], h => simp [adminsToV] at h
  | [_, _], h => simp [adminsToV] at h
  | [_, _, _], h => simp [adminsToV] at h
  | _ :: _ :: _ :: _ :: _ :: _, h => simp [adminsToV] at h

/-- The configuration of a `Step_read` rule, read back. -/
theorem cfg_inv {s : Store H} {f : Frame} {is : List Admin} {Z : Value} {L : List Value}
    (h : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list L])) :
    Z = stV (storeV hn s) (frameV f) ∧ adminsToV is = L := by
  have h' : stV (storeV hn s) (frameV f) = Z ∧ adminsToV is = L := by
    simpa [configV, stateV] using h
  exact ⟨h'.1.symm, h'.2⟩

/-- The encoding of address types is injective. -/
theorem encode_addrType_inj {a b : AddrType} (h : (Encode.toValue a : Value) = Encode.toValue b) :
    a = b := by
  have e : ∀ c : AddrType, (Encode.toValue c : Value) = .case (if c = .i32 then "I32" else "I64")
      (.tuple []) := by
    intro c
    cases c <;> rfl
  rw [e a, e b] at h
  have h' := (Value.case.inj h).1
  cases a <;> cases b <;> simp_all

/-- The trap's image. -/
theorem trap_out {w : Value} (h : w = .list [.case "TRAP" (.tuple [])]) :
    w = .list (adminsToV [.trap]) := by
  simp [h, adminsToV, Equiv.Execution.caseNilV]

@[simp] theorem elemInstV_REFS (e : ElemInst) :
    (elemInstToValue CT e).field? "REFS" = some (.list (e.refs.map refToValue)) := rfl

section Store

variable (B : Builtins) (NA : NoAcc B) {ρ : VarEnv} {s : Store H} {f : Frame}
include NA

/-- **`$table(z, x)` on an encoded state, read back.** -/
theorem table_inv {zx : IL.Id} {x : TableIdx} {T : Value} (hρ : ρ.findDef? "table" = none)
    (fz : ρ.findVal? "z" = some (stV (storeV hn s) (frameV f)))
    (fx : ρ.findVal? zx = some (idxV x.toNat))
    (h : EvalExp (simEnv B) ρ (.callE "table" [.expA (.varE "z"), .expA (.varE zx)]) T) :
    ∃ ta ti, s.table? f x = some (ta, ti) ∧ T = tableInstToValue CT ti := by
  obtain ⟨Ls, M, As, ta, hLs, hM, hAs, hta, ht⟩ := evalExp_storeAcc_inv (State.stateDefs_simEnv B)
    (State.stateDefs_simEnv B).table hρ (NA.table _) (evalExp_var fz) (evalExp_var fx) h
  have hLs' : Ls = .list (s.tables.map (tableInstToValue CT)) := by simpa using hLs.symm
  have hM' : M = moduleInstToValue CT f.module := by simpa using hM.symm
  have hAs' : As = .list (f.module.tables.map fun a => .num (.natN a)) := by
    simpa [hM'] using hAs.symm
  obtain ⟨ti, h₁, h₂, rfl⟩ := idx_idx_map_inv (hAs' ▸ hta) (hLs' ▸ ht)
  exact ⟨ta, ti, by simp [Store.table?, h₁, h₂], rfl⟩

/-- **`$elem(z, y)` on an encoded state, read back.** -/
theorem elem_inv {zy : IL.Id} {y : ElemIdx} {E : Value} (hρ : ρ.findDef? "elem" = none)
    (fz : ρ.findVal? "z" = some (stV (storeV hn s) (frameV f)))
    (fy : ρ.findVal? zy = some (idxV y.toNat))
    (h : EvalExp (simEnv B) ρ (.callE "elem" [.expA (.varE "z"), .expA (.varE zy)]) E) :
    ∃ ea ei, s.elem? f y = some (ea, ei) ∧ E = elemInstToValue CT ei := by
  obtain ⟨Ls, M, As, ea, hLs, hM, hAs, hea, he⟩ := evalExp_storeAcc_inv (State.stateDefs_simEnv B)
    (State.stateDefs_simEnv B).elem hρ (NA.elem _) (evalExp_var fz) (evalExp_var fy) h
  have hLs' : Ls = .list (s.elems.map (elemInstToValue CT)) := by simpa using hLs.symm
  have hM' : M = moduleInstToValue CT f.module := by simpa using hM.symm
  have hAs' : As = .list (f.module.elems.map fun a => .num (.natN a)) := by
    simpa [hM'] using hAs.symm
  obtain ⟨ei, h₁, h₂, rfl⟩ := idx_idx_map_inv (hAs' ▸ hea) (hLs' ▸ he)
  exact ⟨ea, ei, by simp [Store.elem?, h₁, h₂], rfl⟩

/-- **`|$table(z, x).REFS|`, read back.** -/
theorem tableLen_inv {zx : IL.Id} {x : TableIdx} {v : Value} (hρ : ρ.findDef? "table" = none)
    (fz : ρ.findVal? "z" = some (stV (storeV hn s) (frameV f)))
    (fx : ρ.findVal? zx = some (idxV x.toNat))
    (h : EvalExp (simEnv B) ρ
      (.lenE (.dotE (.callE "table" [.expA (.varE "z"), .expA (.varE zx)]) "REFS")) v) :
    ∃ ta ti, s.table? f x = some (ta, ti) ∧ v = .num (.natN ti.refs.length) := by
  obtain ⟨rs, hrs, rfl⟩ := evalExp_lenE_iff.1 h
  obtain ⟨T, hT, hR⟩ := evalExp_dotE_iff.1 hrs
  obtain ⟨ta, ti, ht, rfl⟩ := table_inv B NA hρ fz fx hT
  have e : rs = ti.refs.map refToValue := by simpa using hR.symm
  exact ⟨ta, ti, ht, by simp [e]⟩

/-- **`|$elem(z, y).REFS|`, read back.** -/
theorem elemLen_inv {zy : IL.Id} {y : ElemIdx} {v : Value} (hρ : ρ.findDef? "elem" = none)
    (fz : ρ.findVal? "z" = some (stV (storeV hn s) (frameV f)))
    (fy : ρ.findVal? zy = some (idxV y.toNat))
    (h : EvalExp (simEnv B) ρ
      (.lenE (.dotE (.callE "elem" [.expA (.varE "z"), .expA (.varE zy)]) "REFS")) v) :
    ∃ ea ei, s.elem? f y = some (ea, ei) ∧ v = .num (.natN ei.refs.length) := by
  obtain ⟨rs, hrs, rfl⟩ := evalExp_lenE_iff.1 h
  obtain ⟨E, hE, hR⟩ := evalExp_dotE_iff.1 hrs
  obtain ⟨ea, ei, he, rfl⟩ := elem_inv B NA hρ fz fy hE
  have e : rs = ei.refs.map refToValue := by simpa using hR.symm
  exact ⟨ea, ei, he, by simp [e]⟩

end Store

end Silmaril.Wasm.SpecTec.Sim.BwdRead
