module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Transfer.Swap

/-!
# Round 6: the instances of `Step`'s rules 1–5 at the image of a configuration

For each of `Step`'s rules 1–5, the instance of its leading premise (`Inst`) when the left-hand
side is the image of a Core configuration `c`:

* `read` (1): `Step_read` at `c`'s image itself (`inst_read`);
* `ctxt-instrs`, `ctxt-label`, `ctxt-handler`, `ctxt-frame` (2–5): `Step` at the image of a
  configuration whose code is strictly smaller and whose redex is a cast only if `c`'s is
  (`SubInst`; `inst_ctxtInstrs`, `inst_ctxtLabel`, `inst_ctxtHandler`, `inst_ctxtFrame`).

The computations are those of `Bwd.inv_*` and `Round6.Target.bwdV_ctxt*C`, for any
interpretation of the premises.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Transfer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecStepRules
  (readRule ctxtInstrsRule ctxtLabelRule ctxtHandlerRule ctxtFrameRule)
open Silmaril.SpecTec.Equiv.Execution (iterPat valsPat evalExp_iterPat evalExp_valsPat)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Bwd (codeSize tuple2_inj configV_cfgV StructDecode stV_inj)
open Target (CastRedex)

variable {H : Type} {hn : H → String} {env : Env}

/-- **The premise of a context rule is at a smaller configuration**: `w` is a pair whose
left-hand side is the image of a configuration with smaller code, whose redex is a cast only if
`c`'s is. -/
def SubInst (hn : H → String) (c : Config H) (w : Value) : Prop :=
  ∃ (c' : Config H) (u : Value), w = .tuple [configV hn c', u] ∧
    codeSize c'.code < codeSize c.code ∧ (¬ CastRedex c.code → ¬ CastRedex c'.code)

/-- `read` (1): the premise is `Step_read` at the same left-hand side. -/
theorem inst_read {D : Interp} {els : Prop} {a b w : Value}
    (h : Inst env D els readRule (.tuple [a, b]) w) : ∃ u, w = .tuple [a, u] := by
  obtain ⟨σ, hq, he, hpe, -⟩ := h
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨is, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (.tail _ (.head _))
  obtain ⟨js, fj, -⟩ :=
    quant_list (x := "instr'*") (t := .varT "instr" []) hq (.tail _ (.tail _ (.head _)))
  have ei : EvalExp env _ (iterPat "instr" "instr*") (.list is) := evalExp_iterPat (by decide) fi
  have ej : EvalExp env _ (iterPat "instr'" "instr'*") (.list js) :=
    evalExp_iterPat (by decide) fj
  have ez := evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei)
  have hc : Value.tuple [a, b] = .tuple [cfgV z is, cfgV z js] :=
    EvalExp.unique he (evalExp_tup2 ez (evalExp_case (evalExp_tup2 (evalExp_var fz) ej)))
  have hw : w = .tuple [cfgV z is, .list js] := EvalExp.unique hpe (evalExp_tup2 ez ej)
  have ha : a = cfgV z is := (tuple2_inj hc).1
  exact ⟨.list js, by rw [hw, ha]⟩

/-- The shape of `ctxt-instrs`' instance, before decoding. -/
theorem inst_ctxtInstrs_shape {D : Interp} {els : Prop} {a b w : Value}
    (h : Inst env D els ctxtInstrsRule (.tuple [a, b]) w) :
    ∃ z z' vs is is' rest, (∃ ρ, ValsOnly ρ ∧ HasTyp env ρ valsT (.list vs)) ∧
      (vs ≠ [] ∨ rest ≠ []) ∧ a = cfgV z (vs ++ is ++ rest) ∧
      w = .tuple [cfgV z is, cfgV z' is'] := by
  obtain ⟨σ, hq, he, hpe, hr⟩ := h
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨vs, fv, tv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq (.tail _ (.head _))
  obtain ⟨is, fi, -⟩ :=
    quant_list (x := "instr*") (t := .varT "instr" []) hq (.tail _ (.tail _ (.head _)))
  obtain ⟨rest, fr, -⟩ := quant_list (x := "instr_1*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨z', fz', -⟩ :=
    quant_of (x := "z'") (t := stateT) hq (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨is', fi', -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have ev : EvalExp env _ (valsPat "val" "val*") (.list vs) := evalExp_valsPat (by decide) fv
  have ev' : EvalExp env _ (iterPat "val" "val*") (.list vs) := evalExp_iterPat (by decide) fv
  have ei : EvalExp env _ (iterPat "instr" "instr*") (.list is) := evalExp_iterPat (by decide) fi
  have ei' : EvalExp env _ (iterPat "instr'" "instr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have er : EvalExp env _ (iterPat "instr_1" "instr_1*") (.list rest) :=
    evalExp_iterPat (by decide) fr
  have hc : Value.tuple [a, b] =
      .tuple [cfgV z (vs ++ (is ++ rest)), cfgV z' (vs ++ (is' ++ rest))] :=
    EvalExp.unique he (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_cat ev (evalExp_cat ei er))))
      (evalExp_case (evalExp_tup2 (evalExp_var fz') (evalExp_cat ev (evalExp_cat ei' er)))))
  have hw : w = .tuple [cfgV z is, cfgV z' is'] := EvalExp.unique hpe
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (evalExp_tup2 (evalExp_var fz') ei')))
  have hb : Value.bool (decide (vs ≠ [] ∨ rest ≠ [])) = .bool true :=
    Bwd.ifPrem_true (hr _ (.head _)) (evalExp_or (evalExp_ne_nil ev') (evalExp_ne_nil er))
  have hne : vs ≠ [] ∨ rest ≠ [] := of_decide_eq_true (Value.bool.inj hb)
  have h₁ : a = cfgV z (vs ++ is ++ rest) := by rw [List.append_assoc]; exact (tuple2_inj hc).1
  exact ⟨z, z', vs, is, is', rest, ⟨_, valsOnly_bindVals σ, tv⟩, hne, h₁, hw⟩

/-- `ctxt-instrs` (2), at the image of a configuration. -/
theorem inst_ctxtInstrs (SD : StructDecode env) {D : Interp} {els : Prop} {c : Config H}
    {b w : Value} (h : Inst env D els ctxtInstrsRule (.tuple [configV hn c, b]) w) :
    SubInst hn c w := by
  obtain ⟨z, z', vs, is, is', rest, ⟨ρ, hρ, hvs⟩, hne, h₁, hw⟩ := inst_ctxtInstrs_shape h
  obtain ⟨s, f, code⟩ := c
  have e₁ : z = stateV hn s f ∧ vs ++ is ++ rest = adminsToV code := configV_cfgV h₁
  obtain ⟨A, I, R, hcode, hA, hI, hR⟩ := Bwd.adminsToV_split3 e₁.2.symm
  obtain ⟨vs₀, hv₀⟩ : ∃ vs₀, A = vals vs₀ := SD.vals ρ A hρ (hA ▸ hvs)
  have hneA : A ≠ [] ∨ R ≠ [] :=
    hne.imp (fun h he => h (by rw [← hA, he]; rfl)) (fun h he => h (by rw [← hR, he]; rfl))
  have e₂ : cfgV z is = configV hn ⟨s, f, I⟩ := by rw [Bwd.configV_eq, e₁.1, hI]
  have hsz : codeSize I < codeSize code := hcode ▸ Bwd.codeSize_mid hneA
  have hcr : ¬ CastRedex code → ¬ CastRedex I := fun hnc =>
    Target.not_castRedex_mid (vs := vs₀) (c := R) (hv₀ ▸ hcode ▸ hnc)
  exact ⟨⟨s, f, I⟩, cfgV z' is', by rw [hw, e₂], hsz, hcr⟩

/-- The shape of a label or handler rule's instance, before decoding. -/
theorem inst_ctxtLabel_shape {D : Interp} {els : Prop} {a b w : Value}
    (h : Inst env D els ctxtLabelRule (.tuple [a, b]) w) :
    ∃ z z' n cont is is', a = cfgV z [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is])] ∧
      w = .tuple [cfgV z is, cfgV z' is'] := by
  obtain ⟨σ, hq, he, hpe, -⟩ := h
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨n, fn, -⟩ := quant_of (x := "n") (t := nT) hq (.tail _ (.head _))
  obtain ⟨cont, fc, -⟩ :=
    quant_list (x := "instr_0*") (t := .varT "instr" []) hq (.tail _ (.tail _ (.head _)))
  obtain ⟨is, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨z', fz', -⟩ :=
    quant_of (x := "z'") (t := stateT) hq (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨is', fi', -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have ec : EvalExp env _ (iterPat "instr_0" "instr_0*") (.list cont) :=
    evalExp_iterPat (by decide) fc
  have ei : EvalExp env _ (iterPat "instr" "instr*") (.list is) := evalExp_iterPat (by decide) fi
  have ei' : EvalExp env _ (iterPat "instr'" "instr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have hc : Value.tuple [a, b] =
      .tuple [cfgV z [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is])],
        cfgV z' [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is'])]] :=
    EvalExp.unique he (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ec ei)))))
      (evalExp_case (evalExp_tup2 (evalExp_var fz')
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ec ei'))))))
  have hw : w = .tuple [cfgV z is, cfgV z' is'] := EvalExp.unique hpe
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (evalExp_tup2 (evalExp_var fz') ei')))
  exact ⟨z, z', n, cont, is, is', (tuple2_inj hc).1, hw⟩

/-- `ctxt-label` (3), at the image of a configuration. -/
theorem inst_ctxtLabel (SD : StructDecode env) {D : Interp} {els : Prop} {c : Config H}
    {b w : Value} (h : Inst env D els ctxtLabelRule (.tuple [configV hn c, b]) w) :
    SubInst hn c w := by
  obtain ⟨z, z', m, cont, is, is', h₁, hw⟩ := inst_ctxtLabel_shape h
  obtain ⟨s, f, code⟩ := c
  have e₁ := configV_cfgV h₁
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single e₁.2.symm
  obtain ⟨k, cont₀, body, rfl⟩ := SD.label a _ ha
  have hp : Value.num (.natN k) = m ∧ instrsToV cont₀ = cont ∧ adminsToV body = is := by
    simpa only [adminToV_label, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have e₂ : cfgV z is = configV hn ⟨s, f, body⟩ := by rw [Bwd.configV_eq, e₁.1, hp.2.2]
  exact ⟨⟨s, f, body⟩, cfgV z' is', by rw [hw, e₂], Bwd.codeSize_label k cont₀ body,
    Target.not_castRedex_label⟩

/-- The shape of the handler rule's instance, before decoding. -/
theorem inst_ctxtHandler_shape {D : Interp} {els : Prop} {a b w : Value}
    (h : Inst env D els ctxtHandlerRule (.tuple [a, b]) w) :
    ∃ z z' n cs is is', a = cfgV z [.case "HANDLER_%{%}%" (.tuple [n, .list cs, .list is])] ∧
      w = .tuple [cfgV z is, cfgV z' is'] := by
  obtain ⟨σ, hq, he, hpe, -⟩ := h
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨n, fn, -⟩ := quant_of (x := "n") (t := nT) hq (.tail _ (.head _))
  obtain ⟨cs, fc, -⟩ :=
    quant_list (x := "catch*") (t := .varT "catch" []) hq (.tail _ (.tail _ (.head _)))
  obtain ⟨is, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨z', fz', -⟩ :=
    quant_of (x := "z'") (t := stateT) hq (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨is', fi', -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have ec : EvalExp env _ (iterPat "catch" "catch*") (.list cs) := evalExp_iterPat (by decide) fc
  have ei : EvalExp env _ (iterPat "instr" "instr*") (.list is) := evalExp_iterPat (by decide) fi
  have ei' : EvalExp env _ (iterPat "instr'" "instr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have hc : Value.tuple [a, b] =
      .tuple [cfgV z [.case "HANDLER_%{%}%" (.tuple [n, .list cs, .list is])],
        cfgV z' [.case "HANDLER_%{%}%" (.tuple [n, .list cs, .list is'])]] :=
    EvalExp.unique he (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ec ei)))))
      (evalExp_case (evalExp_tup2 (evalExp_var fz')
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ec ei'))))))
  have hw : w = .tuple [cfgV z is, cfgV z' is'] := EvalExp.unique hpe
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (evalExp_tup2 (evalExp_var fz') ei')))
  exact ⟨z, z', n, cs, is, is', (tuple2_inj hc).1, hw⟩

/-- `ctxt-handler` (4), at the image of a configuration. -/
theorem inst_ctxtHandler (SD : StructDecode env) {D : Interp} {els : Prop} {c : Config H}
    {b w : Value} (h : Inst env D els ctxtHandlerRule (.tuple [configV hn c, b]) w) :
    SubInst hn c w := by
  obtain ⟨z, z', m, cs, is, is', h₁, hw⟩ := inst_ctxtHandler_shape h
  obtain ⟨s, f, code⟩ := c
  have e₁ := configV_cfgV h₁
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single e₁.2.symm
  obtain ⟨k, cs₀, body, rfl⟩ := SD.handler a _ ha
  have hp : Value.num (.natN k) = m ∧ cs₀.map Encode.toValue = cs ∧ adminsToV body = is := by
    simpa only [adminToV_handler, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have e₂ : cfgV z is = configV hn ⟨s, f, body⟩ := by rw [Bwd.configV_eq, e₁.1, hp.2.2]
  exact ⟨⟨s, f, body⟩, cfgV z' is', by rw [hw, e₂], Bwd.codeSize_handler k cs₀ body,
    Target.not_castRedex_handler⟩

/-- The shape of the frame rule's instance, before decoding. -/
theorem inst_ctxtFrame_shape {D : Interp} {els : Prop} {a b w : Value}
    (h : Inst env D els ctxtFrameRule (.tuple [a, b]) w) :
    ∃ sv sv' fv fr fr' n is is',
      a = cfgV (stV sv fv) [.case "FRAME_%{%}%" (.tuple [n, fr, .list is])] ∧
      w = .tuple [cfgV (stV sv fr) is, cfgV (stV sv' fr') is'] := by
  obtain ⟨σ, hq, he, hpe, -⟩ := h
  obtain ⟨sv, fs, -⟩ := quant_of (x := "s") (t := storeT) hq (.head _)
  obtain ⟨fv, ff, -⟩ := quant_of (x := "f") (t := frameT) hq (.tail _ (.head _))
  have ez : EvalExp env _ (.caseE "%;%" (.tupE [.varE "s", .varE "f"])) (stV sv fv) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ff))
  obtain ⟨n, fn, -⟩ := quant_of (x := "n") (t := nT) hq (.tail _ (.tail _ (.head _)))
  obtain ⟨fr, ffr, -⟩ :=
    quant_of (x := "f'") (t := frameT) hq (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨is, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨sv', fs', -⟩ := quant_of (x := "s'") (t := storeT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  obtain ⟨fr', ffr', -⟩ := quant_of (x := "f''") (t := frameT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  obtain ⟨is', fi', -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
  have ei : EvalExp env _ (iterPat "instr" "instr*") (.list is) := evalExp_iterPat (by decide) fi
  have ei' : EvalExp env _ (iterPat "instr'" "instr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have hc : Value.tuple [a, b] =
      .tuple [cfgV (stV sv fv) [.case "FRAME_%{%}%" (.tuple [n, fr, .list is])],
        cfgV (stV sv' fv) [.case "FRAME_%{%}%" (.tuple [n, fr', .list is'])]] :=
    EvalExp.unique he (evalExp_tup2
      (evalExp_case (evalExp_tup2 ez
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr) ei)))))
      (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ff)))
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr') ei'))))))
  have hw : w = .tuple [cfgV (stV sv fr) is, cfgV (stV sv' fr') is'] := EvalExp.unique hpe
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ffr)))
        ei))
      (evalExp_case (evalExp_tup2
        (evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ffr'))) ei')))
  exact ⟨sv, sv', fv, fr, fr', n, is, is', (tuple2_inj hc).1, hw⟩

/-- `ctxt-frame` (5), at the image of a configuration. -/
theorem inst_ctxtFrame (SD : StructDecode env) {D : Interp} {els : Prop} {c : Config H}
    {b w : Value} (h : Inst env D els ctxtFrameRule (.tuple [configV hn c, b]) w) :
    SubInst hn c w := by
  obtain ⟨sv, sv', fv, fr, fr', m, is, is', h₁, hw⟩ := inst_ctxtFrame_shape h
  obtain ⟨s, f, code⟩ := c
  have e₁ := configV_cfgV h₁
  have e₀ : sv = storeV hn s ∧ fv = frameV f := stV_inj e₁.1
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single e₁.2.symm
  obtain ⟨k, fi, body, rfl⟩ := SD.frame a _ ha
  have hp : Value.num (.natN k) = m ∧ frameV fi = fr ∧ adminsToV body = is := by
    simpa only [adminToV_frame, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have e₂ : cfgV (stV sv fr) is = configV hn ⟨s, fi, body⟩ := by
    rw [Bwd.configV_eq, e₀.1, ← hp.2.1, hp.2.2]
    rfl
  exact ⟨⟨s, fi, body⟩, cfgV (stV sv' fr') is', by rw [hw, e₂], Bwd.codeSize_frame k fi body,
    Target.not_castRedex_frame⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.Transfer
