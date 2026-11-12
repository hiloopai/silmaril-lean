module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.RMRead.Block

/-!
# Round 9, rm: `throw_ref-handler-catch` and `-catch_ref` at `configVD` (unrefined)

Round 6's `Exn.bwd_read_throwRefHandlerCatch` and `bwd_read_throwRefHandlerCatchRef`
(`Step_read` 17 and 18), re-run at `configVD`. Their premises read `$exninst(z)` and
`$tagaddr(z)`, single-clause projections of the store's `EXNS` and the frame's `MODULE.TAGS`, which a
`stateVD` image has as the `stateV` image does (`applies_exninstD`, `applies_tagaddrD`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMRead

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV iterPat valsPat valsNPat evalExp_iterPat
  evalExp_valsPat)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round7.MemSimd (configVD stateVD storeVD adminsToVD adminToVD adminsToVD_eq_single
  adminsToVD_append adminsToVD_vals)
open RMPure (toV_of_atomD handlerD_of valsD_of)

variable {H : Type} {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
  {host : HostSemantics H}

/-- `$exninst(z) = z.EXNS` at a `stateVD` image. -/
theorem applies_exninstD (B : Builtins) (s : Store H) (f : Frame) :
    Applies (simEnv B) "exninst" [.val (stateVD hn s f)] (.list (s.exns.map exnInstV)) :=
  Prims.applies_of_clause1 (Prims.projDefs_simEnv B).exninst State.matchArgs_statePat
    (evalExp_dotE_iff.2 ⟨_, evalExp_var rfl, rfl⟩)

/-- `$tagaddr(z) = z.MODULE.TAGS` at a `stateVD` image. -/
theorem applies_tagaddrD (B : Builtins) (s : Store H) (f : Frame) :
    Applies (simEnv B) "tagaddr" [.val (stateVD hn s f)]
      (.list (f.module.tags.map fun a => .num (.natN a))) :=
  Prims.applies_of_clause1 (Prims.projDefs_simEnv B).tagaddr State.matchArgs_statePat
    (evalExp_dotE_iff.2 ⟨_, evalExp_dotE_iff.2 ⟨_, evalExp_var rfl, rfl⟩, rfl⟩)

/-- The tag premise of `throw_ref-handler-catch(_ref)` at a `stateVD` image. -/
theorem tagMatchD_of_prem {B : Builtins} {ρ : VarEnv} {s : Store H} {f : Frame}
    {a : Nat} {x : TagIdx}
    (fz : ρ.findVal? "z" = some (stateVD hn s f)) (fa : ρ.findVal? "a" = some (.num (.natN a)))
    (fx : ρ.findVal? "x" = some (Encode.toValue x))
    (hd₁ : ρ.findDef? "exninst" = none) (hd₂ : ρ.findDef? "tagaddr" = none)
    (h : EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT
      (.dotE (.idxE (.callE "exninst" [.expA (.varE "z")]) (.varE "a")) "TAG")
      (.idxE (.callE "tagaddr" [.expA (.varE "z")]) (.projE (.uncaseE (.varE "x") "%") 0)))
      (.bool true)) :
    ∃ e ta, s.exns[a]? = some e ∧ f.module.tags[x.toNat]? = some ta ∧ e.tag = ta := by
  have hargs : EvalArgs (simEnv B) ρ [.expA (.varE "z")] [.val (stateVD hn s f)] :=
    Equiv.evalArgs_cons (evalExp_var fz) Equiv.evalArgs_nil
  obtain ⟨t₁, t₂, ht₁, ht₂, hcmp⟩ := evalExp_cmpE_iff.1 h
  have heq : t₁ = t₂ := Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hcmp
  obtain ⟨ei, hei, htag⟩ := evalExp_dotE_iff.1 ht₁
  obtain ⟨eis, j, heis, hj, hidxe⟩ := evalExp_idxE_iff.1 hei
  have hjv : ρ.findVal? "a" = some (.num (.natN j)) := evalExp_varE_iff.1 hj
  have hja : j = a := by
    rw [fa] at hjv
    simpa using hjv.symm
  have heis' : eis = .list (s.exns.map exnInstV) :=
    Equiv.ExecNumeric.Applies.unique
      ((Equiv.ExecNumeric.applies_iff_callDef hd₁ hargs).2 (evalExp_callE_iff.1 heis))
      (applies_exninstD B s f)
  obtain ⟨tas, i, htas, hi, hidxt⟩ := evalExp_idxE_iff.1 ht₂
  have hix : i = x.toNat := by
    obtain ⟨vs, hvs, h0⟩ := (Equiv.ExecReadControl.evalExp_idxProj_iff fx).1 hi
    have hvs' : vs = [.num (.natN x.toNat)] := (Value.tuple.inj (Value.case.inj hvs).2).symm
    subst hvs'
    simpa using h0.symm
  have htas' : tas = .list (f.module.tags.map fun a => .num (.natN a)) :=
    Equiv.ExecNumeric.Applies.unique
      ((Equiv.ExecNumeric.applies_iff_callDef hd₂ hargs).2 (evalExp_callE_iff.1 htas))
      (applies_tagaddrD B s f)
  subst heis' htas' hja hix heq
  simp only [Value.idx?, List.getElem?_map, Option.map_eq_some_iff] at hidxe hidxt
  obtain ⟨e, he, rfl⟩ := hidxe
  obtain ⟨ta, hta, hta'⟩ := hidxt
  refine ⟨e, ta, he, hta, ?_⟩
  have hf : (exnInstV e).field? "TAG" = some (.num (.natN e.tag)) := rfl
  rw [hf, ← hta'] at htag
  simpa using htag

/-- The fields premise of `throw_ref-handler-catch(_ref)` at a `stateVD` image. -/
theorem fieldsD_of_prem {B : Builtins} {ρ : VarEnv} {s : Store H} {f : Frame} {a : Nat}
    {e : ExnInst} {vs : List Value} (he : s.exns[a]? = some e)
    (fz : ρ.findVal? "z" = some (stateVD hn s f)) (fa : ρ.findVal? "a" = some (.num (.natN a)))
    (hd : ρ.findDef? "exninst" = none)
    (hvs : EvalExp (simEnv B) ρ (.iterE (.varE "val") (.mk .list [.mk "val" (.varE "val*")]))
      (.list vs))
    (h : EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT
      (.iterE (.varE "val") (.mk .list [.mk "val" (.varE "val*")]))
      (.dotE (.idxE (.callE "exninst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")) (.bool true)) :
    vs = e.fields.map valV := by
  obtain ⟨t₁, t₂, ht₁, ht₂, hcmp⟩ := evalExp_cmpE_iff.1 h
  have heq : t₁ = t₂ := Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hcmp
  have h₁ : t₁ = .list vs := EvalExp.unique ht₁ hvs
  have hex : EvalExp (simEnv B) ρ (.idxE (.callE "exninst" [.expA (.varE "z")]) (.varE "a"))
      (exnInstV e) :=
    evalExp_idxE_iff.2 ⟨_, a, evalExp_callE_iff.2 ((Equiv.ExecNumeric.applies_iff_callDef hd
      (Equiv.evalArgs_cons (evalExp_var fz) Equiv.evalArgs_nil)).mp (applies_exninstD B s f)),
      evalExp_var fa, by simp [Value.idx?, he]⟩
  have h₂ : t₂ = .list (e.fields.map valV) :=
    EvalExp.unique ht₂ (evalExp_dotE_iff.2 ⟨_, hex, rfl⟩)
  rw [h₁, h₂] at heq
  exact Value.list.inj heq

/-- The left-hand code `HANDLER_n{C x l catch'*} (REF.EXN_ADDR a) THROW_REF` at `adminsToVD`,
for `C` = `CATCH` (`cr = false`) or `CATCH_REF` (`cr = true`). -/
theorem catchLhsD_decode {B : Builtins} {ρ : VarEnv} {code : List Admin} {op : MixopS}
    (hop : op = "CATCH" ∨ op = "CATCH_REF")
    (h : EvalExp (simEnv B) ρ (.listE [.caseE "HANDLER_%{%}%" (.tupE [.varE "n",
      .catE (.listE [.caseE op (.tupE [.varE "x", .varE "l"])])
        (.iterE (.varE "catch'") (.mk .list [.mk "catch'" (.varE "catch'*")])),
      .listE [.caseE "REF.EXN_ADDR" (.varE "a"), .caseE "THROW_REF" (.tupE [])]])])
      (.list (adminsToVD code))) :
    ∃ n x l cs₀ k, (op = "CATCH" → code = [.handler n (.catch_ x l :: cs₀) (throwing k)]) ∧
      (op = "CATCH_REF" → code = [.handler n (.catchRef x l :: cs₀) (throwing k)]) ∧
      ρ.findVal? "x" = some (Encode.toValue x) ∧ ρ.findVal? "l" = some (Encode.toValue l) ∧
      ρ.findVal? "a" = some (.num (.natN k)) := by
  obtain ⟨x, hx, hxe⟩ := Exn.evalExp_list1_inv' h
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single hx
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 hxe
  obtain ⟨x', y', body, rfl⟩ := ctxD_of ha (.inr (.inl rfl))
  obtain ⟨n, cs, body', rfl, -, hcs, hb'⟩ := handlerD_of ha
  obtain ⟨-, h₂, h₃⟩ := Exn.evalExp_tup3_inv hu
  obtain ⟨c₀, cs₀, xw, rfl, hc₀, hxw⟩ := Exn.catch_head' (hcs ▸ h₂)
  obtain ⟨av, fa, hbl⟩ := Exn.evalExp_throwExn_inv (hb' ▸ h₃)
  obtain ⟨k, rfl, rfl⟩ := throwingD_of hbl
  rcases hop with rfl | rfl
  · obtain ⟨xi, l, rfl, rfl⟩ := (Exn.catch_decode hc₀).1 rfl
    obtain ⟨hx₁, hl₁⟩ := Exn.evalExp_tup2_inv hxw
    exact ⟨n, xi, l, cs₀, k, fun _ => rfl, fun h => by simp at h, evalExp_varE_iff.1 hx₁,
      evalExp_varE_iff.1 hl₁, fa⟩
  · obtain ⟨xi, l, rfl, rfl⟩ := (Exn.catch_decode hc₀).2.1 rfl
    obtain ⟨hx₁, hl₁⟩ := Exn.evalExp_tup2_inv hxw
    exact ⟨n, xi, l, cs₀, k, fun h => by simp at h, fun _ => rfl, evalExp_varE_iff.1 hx₁,
      evalExp_varE_iff.1 hl₁, fa⟩

theorem bwdRD_throwRefHandlerCatch (B : Builtins) : LeafRD B hn P host 17 := by
  rintro ⟨s, f, code⟩ w hf
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ :=
    Exn.fires_body (Exn.hasReadRules_simEnv B).throwRefHandlerCatch hf
  obtain rfl : VarEnv.empty = ρ₀ := Option.some.inj hps
  obtain ⟨hz, hce, hre⟩ := Exn.evalExp_concl_inv (Round7.MemSimd.configVD_eq hn _ ▸ he)
  obtain ⟨n, x, l, cs₀, k, hcode, -, fx, fl, fa⟩ := catchLhsD_decode (.inl rfl) hce
  obtain rfl := hcode rfl
  obtain ⟨vs, hvs, hvs', -⟩ := Exn.vals_quant hq (by simp)
  have fz : _ = some (stateVD hn s f) := evalExp_varE_iff.1 hz
  obtain ⟨e, ta, hek, hta, rfl⟩ : ∃ e ta, s.exns[k]? = some e ∧
      f.module.tags[x.toNat]? = some ta ∧ e.tag = ta := by
    cases hp _ (List.mem_cons_self ..) with
    | ifPr h => exact tagMatchD_of_prem fz fa fx rfl rfl h
  have hfields : vs = e.fields.map valV := by
    cases hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) with
    | ifPr h => exact fieldsD_of_prem hek fz fa rfl hvs' h
  refine ⟨vals e.fields ++ [.plain (.br l)], ?_, .throwRefHandlerCatch hek hta⟩
  rw [adminsToVD_append, adminsToVD_vals, adminsToV_vals, ← hfields]
  exact EvalExp.unique hre (evalExp_cat hvs (evalExp_list1 (evalExp_case (evalExp_var fl))))

theorem bwdRD_throwRefHandlerCatchRef (B : Builtins) : LeafRD B hn P host 18 := by
  rintro ⟨s, f, code⟩ w hf
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ :=
    Exn.fires_body (Exn.hasReadRules_simEnv B).throwRefHandlerCatchRef hf
  obtain rfl : VarEnv.empty = ρ₀ := Option.some.inj hps
  obtain ⟨hz, hce, hre⟩ := Exn.evalExp_concl_inv (Round7.MemSimd.configVD_eq hn _ ▸ he)
  obtain ⟨n, x, l, cs₀, k, -, hcode, fx, fl, fa⟩ := catchLhsD_decode (.inr rfl) hce
  obtain rfl := hcode rfl
  obtain ⟨vs, hvs, hvs', -⟩ := Exn.vals_quant hq (by simp)
  have fz : _ = some (stateVD hn s f) := evalExp_varE_iff.1 hz
  obtain ⟨e, ta, hek, hta, rfl⟩ : ∃ e ta, s.exns[k]? = some e ∧
      f.module.tags[x.toNat]? = some ta ∧ e.tag = ta := by
    cases hp _ (List.mem_cons_self ..) with
    | ifPr h => exact tagMatchD_of_prem fz fa fx rfl rfl h
  have hfields : vs = e.fields.map valV := by
    cases hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) with
    | ifPr h => exact fieldsD_of_prem hek fz fa rfl hvs' h
  refine ⟨vals e.fields ++ [.ref (.exn k), .plain (.br l)], ?_, .throwRefHandlerCatchRef hek hta⟩
  rw [adminsToVD_append, adminsToVD_vals, adminsToV_vals, ← hfields]
  exact EvalExp.unique hre
    (evalExp_cat hvs
      (evalExp_list2 (evalExp_case (evalExp_var fa)) (evalExp_case (evalExp_var fl))))

end Silmaril.Wasm.SpecTec.Sim.Round9.RMRead
