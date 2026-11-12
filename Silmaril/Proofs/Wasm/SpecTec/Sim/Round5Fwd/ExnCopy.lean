module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.Ctrl

/-!
# Round 5: family X's exception rules without `Exn.Helpers`

Family X's forward lemmas for `throw`, `try_table` and `throw_ref` caught by `catch`/`catch_ref`
or passing a non-matching clause took the whole `Exn.Helpers`, whose `expand` and `blocktype`
fields quantify over every Core type (and are refuted through `Residue.valtypes`/`TypeTyping`).
This file is a copy of those lemmas (`Exn/Forward.lean`, sections `Catch` and `Block`;
`Exn/Otherwise.lean`, section `Next`), each renamed with a suffix `C`, taking `HelpersC` (the
`Helpers` fields that are proved for the concrete `B`) and, for `throw` and `try_table`, the one
`expand`/`blocktype` fact they consume as an explicit hypothesis. The proofs are otherwise
unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (evalExp_iterPat evalExp_valsPat caseNilV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Exn

/-- **The `Exn.Helpers` fields proved for the concrete `B`** (all but `expand`, `blocktype` and
the backward `*_inv`). -/
structure HelpersC {H : Type} (env : Env) (hn : H → String) : Prop where
  /-- `$exninst(s; f) = s.EXNS`. -/
  exninst : ∀ (s : Store H) (f : Frame),
    Applies env "exninst" [.val (stateV hn s f)] (.list (s.exns.map exnInstV))
  /-- `$tagaddr(s; f) = f.MODULE.TAGS`. -/
  tagaddr : ∀ (s : Store H) (f : Frame),
    Applies env "tagaddr" [.val (stateV hn s f)] (.list (f.module.tags.map fun a => .num (.natN a)))
  /-- `$tag(z, x)`. -/
  tag : ∀ (s : Store H) (f : Frame) (x : TagIdx) (ta : Nat) (ti : TagInst),
    s.tag? f x = some (ta, ti) →
    Applies env "tag" [.val (stateV hn s f), .val (Encode.toValue x)] (Silmaril.SpecTec.Equiv.RuntimeBridge.tagInstToValue CT ti)
  /-- `$as_deftype(dt) = dt`. -/
  asDeftype : ∀ d : DefType, Applies env "as_deftype" [.val (CT.defType d)] (CT.defType d)
  /-- `$add_exninst(z, [exn])`. -/
  addExn : ∀ (s : Store H) (f : Frame) (e : ExnInst),
    Applies env "add_exninst" [.val (stateV hn s f), .val (.list [exnInstV e])]
      (stateV hn (s.addExn e) f)

section Catch

variable {H : Type} {env : Env} {hn : H → String}

/-- `$exninst(z)[a]`, at an encoded state whose store has the exception `e` at `a`. -/
theorem evalExp_exninstAtC (Hp : HelpersC env hn) {ρ : VarEnv} {s : Store H} {f : Frame}
    {a : Nat} {e : ExnInst} (he : s.exns[a]? = some e)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fa : ρ.findVal? "a" = some (.num (.natN a)))
    (hd : ρ.findDef? "exninst" = none) :
    EvalExp env ρ (.idxE (.callE "exninst" [.expA (.varE "z")]) (.varE "a")) (exnInstV e) :=
  evalExp_idxE_iff.2 ⟨_, a,
    evalExp_callE_iff.2 ((Equiv.ExecNumeric.applies_iff_callDef hd
      (Equiv.evalArgs_cons (evalExp_var fz) Equiv.evalArgs_nil)).mp (Hp.exninst s f)),
    evalExp_var fa, by simp [Value.idx?, he]⟩

/-- `$tagaddr(z)[x.0]`, at an encoded state whose frame has the tag address `ta` at `x`. -/
theorem evalExp_tagaddrAtC (Hp : HelpersC env hn) {ρ : VarEnv} {s : Store H} {f : Frame}
    {x : TagIdx} {ta : Nat} (ht : f.module.tags[x.toNat]? = some ta)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fx : ρ.findVal? "x" = some (Encode.toValue x))
    (hd : ρ.findDef? "tagaddr" = none) :
    EvalExp env ρ (.idxE (.callE "tagaddr" [.expA (.varE "z")])
      (.projE (.uncaseE (.varE "x") "%") 0)) (.num (.natN ta)) :=
  evalExp_idxE_iff.2 ⟨_, x.toNat,
    evalExp_callE_iff.2 ((Equiv.ExecNumeric.applies_iff_callDef hd
      (Equiv.evalArgs_cons (evalExp_var fz) Equiv.evalArgs_nil)).mp (Hp.tagaddr s f)),
    (Equiv.ExecReadControl.evalExp_idxProj_iff fx).2 ⟨_, rfl, rfl⟩,
    by simp [Value.idx?, ht]⟩

/-- The two premises of `throw_ref-handler-catch` and `-catch_ref`: the exception's tag is the
clause's, and `val*` is the exception's fields. -/
theorem dprem_catchTagC (Hp : HelpersC env hn) {O : ElseI} {els : Prop} {ρ : VarEnv}
    {s : Store H} {f : Frame} {x : TagIdx} {a : Nat} {e : ExnInst}
    (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fx : ρ.findVal? "x" = some (Encode.toValue x))
    (fa : ρ.findVal? "a" = some (.num (.natN a)))
    (fv : ρ.findVal? "val*" = some (.list (e.fields.map valV)))
    (hd₁ : ρ.findDef? "exninst" = none) (hd₂ : ρ.findDef? "tagaddr" = none) :
    ∀ p ∈ [Prem.ifPr (.cmpE .eqOp .boolT
         (.dotE (.idxE (.callE "exninst" [.expA (.varE "z")]) (.varE "a")) "TAG")
         (.idxE (.callE "tagaddr" [.expA (.varE "z")]) (.projE (.uncaseE (.varE "x") "%") 0))),
       Prem.ifPr (.cmpE .eqOp .boolT
         (.iterE (.varE "val") (.mk .list [.mk "val" (.varE "val*")]))
         (.dotE (.idxE (.callE "exninst" [.expA (.varE "z")]) (.varE "a")) "FIELDS"))],
      DPrem env O els ρ p := by
  have hx := evalExp_exninstAtC Hp he fz fa hd₁
  refine prems_two (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, ?_, evalExp_tagaddrAtC Hp ht fz fx hd₂,
    Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩))
    (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_iterPat (by decide) fv, ?_,
      Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩))
  · exact evalExp_dotE_iff.2 ⟨_, hx, rfl⟩
  · exact evalExp_dotE_iff.2 ⟨_, hx, rfl⟩

/-- `Step_read/throw_ref-handler-catch`, as a rule body,
under any reading of relations and `otherwise`. -/
theorem body_throwRefHandlerCatchC {O : ElseI} {els : Prop} (Hp : HelpersC env hn)
    {s : Store H} {f : Frame} {n a : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch}
    {e : ExnInst} (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag)
    (hz : TypedV env stateT (stateV hn s f)) (hn₀ : TypedV env nT (.num (.natN n)))
    (hx : TypedV env idxT (Encode.toValue x)) (hl : TypedV env labelidxT (Encode.toValue l))
    (hcs : TypedV env catchesT (.list (cs.map Encode.toValue)))
    (ha : TypedV env addrT (.num (.natN a))) (hvs : TypedV env valsT (.list (e.fields.map valV))) :
    RuleBody env (DDerives env O) els [] [] "%~>%" throwRefHandlerCatchRule
      (.tuple [cfgV (stateV hn s f) (adminsToV [.handler n (.catch_ x l :: cs) (throwing a)]),
        .list (adminsToV (vals e.fields ++ [.plain (.br l)]))]) := by
  let ρ := VarEnv.empty.bindVals [("z", stateV hn s f), ("n", .num (.natN n)),
    ("x", Encode.toValue x), ("l", Encode.toValue l), ("catch'*", .list (cs.map Encode.toValue)),
    ("a", .num (.natN a)), ("val*", .list (e.fields.map valV))]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stateV hn s f) := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN n)) := rfl
  have fx : ρ.findVal? "x" = some (Encode.toValue x) := rfl
  have fl : ρ.findVal? "l" = some (Encode.toValue l) := rfl
  have fc : ρ.findVal? "catch'*" = some (.list (cs.map Encode.toValue)) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  have fv : ρ.findVal? "val*" = some (.list (e.fields.map valV)) := rfl
  rw [adminsToV_append, adminsToV_vals]
  exact ruleBody_of
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hn₀ ρ hρ) (QuantsOk.cons fx (hx ρ hρ)
      (QuantsOk.cons fl (hl ρ hρ) (QuantsOk.cons fc (hcs ρ hρ)
      (QuantsOk.cons fa (ha ρ hρ) (QuantsOk.cons fv (hvs ρ hρ) QuantsOk.nil)))))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
          (evalExp_cat (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fx)
              (evalExp_var fl))))
            (evalExp_iterPat (by decide) fc))
          (evalExp_throwExn fa))))))
      (evalExp_cat (evalExp_valsPat (by decide) fv)
        (evalExp_list1 (evalExp_case (evalExp_var fl)))))
    fun pr hpr => dprem_toPremW ((dprem_catchTagC Hp he ht fz fx fa fv rfl rfl) pr hpr)

/-- `Step_read/throw_ref-handler-catch`, as a declarative derivation. -/
theorem sread_throwRefHandlerCatchC (Hp : HelpersC env hn)
    (hr : HasRuleAt env "Step_read" "%~>%" 17 throwRefHandlerCatchRule)
    {s : Store H} {f : Frame} {n a : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch}
    {e : ExnInst} (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag)
    (hz : TypedV env stateT (stateV hn s f)) (hn₀ : TypedV env nT (.num (.natN n)))
    (hx : TypedV env idxT (Encode.toValue x)) (hl : TypedV env labelidxT (Encode.toValue l))
    (hcs : TypedV env catchesT (.list (cs.map Encode.toValue)))
    (ha : TypedV env addrT (.num (.natN a))) (hvs : TypedV env valsT (.list (e.fields.map valV))) :
    SRead env (cfgV (stateV hn s f) (adminsToV [.handler n (.catch_ x l :: cs) (throwing a)]))
      (adminsToV (vals e.fields ++ [.plain (.br l)])) :=
  dderives_of_body hr (body_throwRefHandlerCatchC Hp he ht hz hn₀ hx hl hcs ha hvs)

/-- `Step_read/throw_ref-handler-catch_ref`, as a rule body,
under any reading of relations and `otherwise`. -/
theorem body_throwRefHandlerCatchRefC {O : ElseI} {els : Prop} (Hp : HelpersC env hn)
    {s : Store H} {f : Frame} {n a : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch}
    {e : ExnInst} (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag)
    (hz : TypedV env stateT (stateV hn s f)) (hn₀ : TypedV env nT (.num (.natN n)))
    (hx : TypedV env idxT (Encode.toValue x)) (hl : TypedV env labelidxT (Encode.toValue l))
    (hcs : TypedV env catchesT (.list (cs.map Encode.toValue)))
    (ha : TypedV env addrT (.num (.natN a))) (hvs : TypedV env valsT (.list (e.fields.map valV))) :
    RuleBody env (DDerives env O) els [] [] "%~>%" throwRefHandlerCatchRefRule
      (.tuple [cfgV (stateV hn s f) (adminsToV [.handler n (.catchRef x l :: cs) (throwing a)]),
        .list (adminsToV (vals e.fields ++ [.ref (.exn a), .plain (.br l)]))]) := by
  let ρ := VarEnv.empty.bindVals [("z", stateV hn s f), ("n", .num (.natN n)),
    ("x", Encode.toValue x), ("l", Encode.toValue l), ("catch'*", .list (cs.map Encode.toValue)),
    ("a", .num (.natN a)), ("val*", .list (e.fields.map valV))]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stateV hn s f) := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN n)) := rfl
  have fx : ρ.findVal? "x" = some (Encode.toValue x) := rfl
  have fl : ρ.findVal? "l" = some (Encode.toValue l) := rfl
  have fc : ρ.findVal? "catch'*" = some (.list (cs.map Encode.toValue)) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  have fv : ρ.findVal? "val*" = some (.list (e.fields.map valV)) := rfl
  rw [adminsToV_append, adminsToV_vals]
  exact ruleBody_of
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hn₀ ρ hρ) (QuantsOk.cons fx (hx ρ hρ)
      (QuantsOk.cons fl (hl ρ hρ) (QuantsOk.cons fc (hcs ρ hρ)
      (QuantsOk.cons fa (ha ρ hρ) (QuantsOk.cons fv (hvs ρ hρ) QuantsOk.nil)))))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
          (evalExp_cat (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fx)
              (evalExp_var fl))))
            (evalExp_iterPat (by decide) fc))
          (evalExp_throwExn fa))))))
      (evalExp_cat (evalExp_valsPat (by decide) fv)
        (evalExp_list2 (evalExp_case (evalExp_var fa)) (evalExp_case (evalExp_var fl)))))
    fun pr hpr => dprem_toPremW ((dprem_catchTagC Hp he ht fz fx fa fv rfl rfl) pr hpr)

/-- `Step_read/throw_ref-handler-catch_ref`, as a declarative derivation. -/
theorem sread_throwRefHandlerCatchRefC (Hp : HelpersC env hn)
    (hr : HasRuleAt env "Step_read" "%~>%" 18 throwRefHandlerCatchRefRule)
    {s : Store H} {f : Frame} {n a : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch}
    {e : ExnInst} (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag)
    (hz : TypedV env stateT (stateV hn s f)) (hn₀ : TypedV env nT (.num (.natN n)))
    (hx : TypedV env idxT (Encode.toValue x)) (hl : TypedV env labelidxT (Encode.toValue l))
    (hcs : TypedV env catchesT (.list (cs.map Encode.toValue)))
    (ha : TypedV env addrT (.num (.natN a))) (hvs : TypedV env valsT (.list (e.fields.map valV))) :
    SRead env (cfgV (stateV hn s f) (adminsToV [.handler n (.catchRef x l :: cs) (throwing a)]))
      (adminsToV (vals e.fields ++ [.ref (.exn a), .plain (.br l)])) :=
  dderives_of_body hr (body_throwRefHandlerCatchRefC Hp he ht hz hn₀ hx hl hcs ha hvs)

end Catch

section Block

variable {H : Type} {env : Env} {hn : H → String}

/-- `Step_read/try_table`: entering a `try_table` block installs its handler around a label. -/
theorem sread_tryTableC (_Hp : HelpersC env hn)
    (hr : HasRuleAt env "Step_read" "%~>%" 22 tryTableRule)
    {s : Store H} {f : Frame} {bt : BlockType} {cs : List Catch} {body : List Instr}
    {vs : List Val} {t₁ t₂ : List CValType} (_hbt : f.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length)
    (hz : TypedV env stateT (stateV hn s f)) (hmT : TypedV env mT (.num (.natN vs.length)))
    (hvs : TypedV env valsT (.list (vs.map valV)))
    (hbtT : TypedV env blocktypeT (Encode.toValue bt))
    (hcs : TypedV env catchesT (.list (cs.map Encode.toValue)))
    (hbody : TypedV env instrsT (.list (instrsToV body)))
    (hnT : TypedV env nT (.num (.natN t₂.length)))
    (hBT : ∃ v₁ v₂ : List Value, v₁.length = t₁.length ∧ v₂.length = t₂.length ∧
      TypedV env valtypesT (.list v₁) ∧ TypedV env valtypesT (.list v₂) ∧
      Applies env "blocktype_" [.val (stateV hn s f), .val (Encode.toValue bt)]
        (instrTypeV v₁ v₂)) :
    SRead env (cfgV (stateV hn s f) (vs.map valV ++ [instrToV (.tryTable bt cs body)]))
      [.case "HANDLER_%{%}%" (.tuple [.num (.natN t₂.length), .list (cs.map Encode.toValue),
        .list [.case "LABEL_%{%}%" (.tuple [.num (.natN t₂.length), .list [],
          .list (vs.map valV ++ instrsToV body)])]])] := by
  obtain ⟨v₁, v₂, hl₁, hl₂, hv₁, hv₂, happ⟩ := hBT
  let ρ := VarEnv.empty.bindVals [("z", stateV hn s f), ("m", .num (.natN vs.length)),
    ("val*", .list (vs.map valV)), ("bt", Encode.toValue bt),
    ("catch*", .list (cs.map Encode.toValue)), ("instr*", .list (instrsToV body)),
    ("n", .num (.natN t₂.length)), ("t_1*", .list v₁), ("t_2*", .list v₂)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stateV hn s f) := rfl
  have fm : ρ.findVal? "m" = some (.num (.natN vs.length)) := rfl
  have fv : ρ.findVal? "val*" = some (.list (vs.map valV)) := rfl
  have fb : ρ.findVal? "bt" = some (Encode.toValue bt) := rfl
  have fc : ρ.findVal? "catch*" = some (.list (cs.map Encode.toValue)) := rfl
  have fi : ρ.findVal? "instr*" = some (.list (instrsToV body)) := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN t₂.length)) := rfl
  have f₁ : ρ.findVal? "t_1*" = some (.list v₁) := rfl
  have f₂ : ρ.findVal? "t_2*" = some (.list v₂) := rfl
  have fm' : ρ.findVal? "m" = some (.num (.natN (vs.map valV).length)) := by
    rw [List.length_map]; exact fm
  have fm₁ : ρ.findVal? "m" = some (.num (.natN v₁.length)) := by rw [hl₁, ← hm]; exact fm
  have fn₂ : ρ.findVal? "n" = some (.num (.natN v₂.length)) := by rw [hl₂]; exact fn
  have ev : EvalExp env ρ (Equiv.Execution.valsNPat "val" "val*" "m") (.list (vs.map valV)) :=
    Exn.evalExp_valsNPat (by decide) fv fm'
  have ec : EvalExp env ρ (.iterE (.varE "catch") (.mk .list [.mk "catch" (.varE "catch*")]))
      (.list (cs.map Encode.toValue)) := evalExp_iterPat (by decide) fc
  have ei : EvalExp env ρ (.iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")]))
      (.list (instrsToV body)) := evalExp_iterPat (by decide) fi
  have hcall : EvalExp env ρ (.callE "blocktype_" [.expA (.varE "z"), .expA (.varE "bt")])
      (instrTypeV v₁ v₂) :=
    evalExp_callE_iff.2 ((Equiv.ExecNumeric.applies_iff_callDef rfl
      (Equiv.evalArgs_cons (evalExp_var fz) (Equiv.evalArgs_cons (evalExp_var fb)
        Equiv.evalArgs_nil))).mp happ)
  exact dderives_of_ruleAt hr _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fm (hmT ρ hρ) (QuantsOk.cons fv (hvs ρ hρ)
      (QuantsOk.cons fb (hbtT ρ hρ) (QuantsOk.cons fc (hcs ρ hρ)
      (QuantsOk.cons fi (hbody ρ hρ) (QuantsOk.cons fn (hnT ρ hρ)
      (QuantsOk.cons f₁ (hv₁ ρ hρ) (QuantsOk.cons f₂ (hv₂ ρ hρ) QuantsOk.nil)))))))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_cat ev (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fb)
          (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons ec evalExps_nil, rfl⟩)) ei))))))
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ec
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) evalExp_nil
          (evalExp_cat ev ei))))))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, hcall,
      evalExp_case (evalExp_tup3
        (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_varN (by decide) f₁ fm₁)
          evalExps_nil, rfl⟩))
        evalExp_nil
        (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_varN (by decide) f₂ fn₂)
          evalExps_nil, rfl⟩))),
      Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩)))

/-- `Store.tag?` finds the tag address in the frame's module. -/
theorem tags_of_tag?C {s : Store H} {f : Frame} {x : TagIdx} {ta : Nat} {ti : TagInst}
    (h : s.tag? f x = some (ta, ti)) : f.module.tags[x.toNat]? = some ta := by
  unfold Store.tag? at h
  cases ht : f.module.tags[x.toNat]? with
  | none => simp [ht] at h
  | some a => cases hs : s.tags[a]? <;> simp_all

/-- `Step/throw`: a new exception instance is allocated and thrown. -/
theorem sstep_throwC (Hp : HelpersC env hn)
    (hr : HasRuleAt env "Step" "%~>%" 10 Equiv.ExecStepRules.throwRule)
    {s : Store H} {f : Frame} {x : TagIdx} {vs : List Val} {ta : Nat} {ti : TagInst}
    {ts : Ty (.list .val)} (htag : s.tag? f x = some (ta, ti))
    (_hex : Expand ti.type (.func ts .nil)) (hlen : vs.length = ts.length)
    (hz : TypedV env stateT (stateV hn s f)) (hnT : TypedV env nT (.num (.natN vs.length)))
    (hvs : TypedV env valsT (.list (vs.map valV))) (hx : TypedV env idxT (Encode.toValue x))
    (hexn : TypedV env exninstT (exnInstV ⟨ta, vs⟩))
    (ha : TypedV env addrT (.num (.natN s.exns.length)))
    (hE : ∃ tvs : List Value, tvs.length = ts.length ∧ TypedV env valtypesT (.list tvs) ∧
      DDerives env (otherwise env) "Expand" "%~~%" [] (.tuple [CT.defType ti.type,
        Exn.funcTypeV tvs []])) :
    SStep env (cfgV (stateV hn s f) (vs.map valV ++ [instrToV (.throw x)]))
      (cfgV (stateV hn (s.addExn ⟨ta, vs⟩) f) (adminsToV (throwing s.exns.length))) := by
  obtain ⟨tvs, htl, htv, hexp⟩ := hE
  let ρ := VarEnv.empty.bindVals [("z", stateV hn s f), ("n", .num (.natN vs.length)),
    ("val*", .list (vs.map valV)), ("x", Encode.toValue x), ("exn", exnInstV ⟨ta, vs⟩),
    ("a", .num (.natN s.exns.length)), ("t*", .list tvs)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stateV hn s f) := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN vs.length)) := rfl
  have fv : ρ.findVal? "val*" = some (.list (vs.map valV)) := rfl
  have fx : ρ.findVal? "x" = some (Encode.toValue x) := rfl
  have fe : ρ.findVal? "exn" = some (exnInstV ⟨ta, vs⟩) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN s.exns.length)) := rfl
  have ft : ρ.findVal? "t*" = some (.list tvs) := rfl
  have fn' : ρ.findVal? "n" = some (.num (.natN (vs.map valV).length)) := by
    rw [List.length_map]; exact fn
  have fnt : ρ.findVal? "n" = some (.num (.natN tvs.length)) := by rw [htl, ← hlen]; exact fn
  have hz₁ : EvalArgs env ρ [.expA (.varE "z")] [.val (stateV hn s f)] :=
    Equiv.evalArgs_cons (evalExp_var fz) Equiv.evalArgs_nil
  have htagE : EvalExp env ρ (.callE "tag" [.expA (.varE "z"), .expA (.varE "x")])
      (Equiv.RuntimeBridge.tagInstToValue CT ti) :=
    evalExp_callE_iff.2 ((Equiv.ExecNumeric.applies_iff_callDef rfl
      (Equiv.evalArgs_cons (evalExp_var fz) (Equiv.evalArgs_cons (evalExp_var fx)
        Equiv.evalArgs_nil))).mp (Hp.tag s f x ta ti htag))
  have hdt : EvalExp env ρ (.callE "as_deftype"
      [.expA (.dotE (.callE "tag" [.expA (.varE "z"), .expA (.varE "x")]) "TYPE")])
      (CT.defType ti.type) :=
    evalExp_callE_iff.2 ((Equiv.ExecNumeric.applies_iff_callDef rfl
      (Equiv.evalArgs_cons (evalExp_dotE_iff.2 ⟨_, htagE, rfl⟩) Equiv.evalArgs_nil)).mp
      (Hp.asDeftype ti.type))
  have hexnE : EvalExp env ρ (.callE "exninst" [.expA (.varE "z")])
      (.list (s.exns.map exnInstV)) :=
    evalExp_callE_iff.2 ((Equiv.ExecNumeric.applies_iff_callDef rfl hz₁).mp (Hp.exninst s f))
  have haddE : EvalExp env ρ (.callE "add_exninst" [.expA (.varE "z"),
      .expA (.listE [.varE "exn"])]) (stateV hn (s.addExn ⟨ta, vs⟩) f) :=
    evalExp_callE_iff.2 ((Equiv.ExecNumeric.applies_iff_callDef rfl
      (Equiv.evalArgs_cons (evalExp_var fz) (Equiv.evalArgs_cons (evalExp_list1 (evalExp_var fe))
        Equiv.evalArgs_nil))).mp (Hp.addExn s f ⟨ta, vs⟩))
  have hp₁ : DPrem env (otherwise env) (otherwise env "Step" [] 10
      (.tuple [cfgV (stateV hn s f) (vs.map valV ++ [instrToV (.throw x)]),
        cfgV (stateV hn (s.addExn ⟨ta, vs⟩) f) (adminsToV (throwing s.exns.length))])) ρ
      (.rulePr "Expand" [] "%~~%" (.tupE [.callE "as_deftype"
          [.expA (.dotE (.callE "tag" [.expA (.varE "z"), .expA (.varE "x")]) "TYPE")],
        .caseE "FUNC%->%" (.tupE [.caseE "%" (.tupE [.iterE (.varE "t")
            (.mk (.listN (.varE "n") none) [.mk "t" (.varE "t*")])]),
          .caseE "%" (.tupE [.listE []])])])) :=
    .rulePr (evalArgs_nil _ _) (evalExp_tup2 hdt (evalExp_case (evalExp_tup2
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_varN (by decide) ft fnt)
        evalExps_nil, rfl⟩))
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons evalExp_nil evalExps_nil, rfl⟩)))))
      hexp
  refine dderives_of_ruleAt hr _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hnT ρ hρ) (QuantsOk.cons fv (hvs ρ hρ)
      (QuantsOk.cons fx (hx ρ hρ) (QuantsOk.cons fe (hexn ρ hρ)
      (QuantsOk.cons fa (ha ρ hρ) (QuantsOk.cons ft (htv ρ hρ) QuantsOk.nil)))))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_cat (Exn.evalExp_valsNPat (by decide) fv fn')
          (evalExp_list1 (evalExp_case (evalExp_var fx))))))
      (evalExp_case (evalExp_tup2 haddE (evalExp_throwExn fa))))
    ?_
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact hp₁
  · exact .ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_var fa,
      evalExp_lenE_iff.2 ⟨_, hexnE, by simp⟩, Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩)
  · exact .ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_var fe,
      evalExp_strE_iff.2 ⟨_, evalExpFields_two
        (evalExp_tagaddrAtC Hp (tags_of_tag?C htag) fz fx rfl)
        (evalExp_varN (by decide) fv fn'), rfl⟩,
      Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩)

end Block

section Next
variable {H : Type} {env : Env} {hn : H → String}
open Silmaril.SpecTec.Equiv.ExecRead

/-- The image of `HANDLER_n{catch*} (REF.EXN_ADDR a) THROW_REF`. -/
abbrev handlerThrowV (n : Nat) (cs : List Catch) (a : Nat) : Value :=
  .case "HANDLER_%{%}%" (.tuple [.num (.natN n), .list (cs.map Encode.toValue),
    .list [.case "REF.EXN_ADDR" (.num (.natN a)), caseNilV "THROW_REF"]])

theorem tagMatch_of_premC (Hp : HelpersC env hn) {ρ : VarEnv} {s : Store H} {f : Frame}
    {a : Nat} {x : TagIdx}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fa : ρ.findVal? "a" = some (.num (.natN a)))
    (fx : ρ.findVal? "x" = some (Encode.toValue x))
    (hd₁ : ρ.findDef? "exninst" = none) (hd₂ : ρ.findDef? "tagaddr" = none)
    (h : EvalExp env ρ (.cmpE .eqOp .boolT
      (.dotE (.idxE (.callE "exninst" [.expA (.varE "z")]) (.varE "a")) "TAG")
      (.idxE (.callE "tagaddr" [.expA (.varE "z")]) (.projE (.uncaseE (.varE "x") "%") 0)))
      (.bool true)) :
    ∃ e ta, s.exns[a]? = some e ∧ f.module.tags[x.toNat]? = some ta ∧ e.tag = ta := by
  have hargs : EvalArgs env ρ [.expA (.varE "z")] [.val (stateV hn s f)] :=
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
      (Hp.exninst s f)
  obtain ⟨tas, i, htas, hi, hidxt⟩ := evalExp_idxE_iff.1 ht₂
  have hix : i = x.toNat := by
    obtain ⟨vs, hvs, h0⟩ := (Equiv.ExecReadControl.evalExp_idxProj_iff fx).1 hi
    have hvs' : vs = [.num (.natN x.toNat)] := (Value.tuple.inj (Value.case.inj hvs).2).symm
    subst hvs'
    simpa using h0.symm
  have htas' : tas = .list (f.module.tags.map fun a => .num (.natN a)) :=
    Equiv.ExecNumeric.Applies.unique
      ((Equiv.ExecNumeric.applies_iff_callDef hd₂ hargs).2 (evalExp_callE_iff.1 htas))
      (Hp.tagaddr s f)
  subst heis' htas' hja hix heq
  simp only [Value.idx?, List.getElem?_map, Option.map_eq_some_iff] at hidxe hidxt
  obtain ⟨e, he, rfl⟩ := hidxe
  obtain ⟨ta, hta, hta'⟩ := hidxt
  refine ⟨e, ta, he, hta, ?_⟩
  have hf : (exnInstV e).field? "TAG" = some (.num (.natN e.tag)) := rfl
  rw [hf, ← hta'] at htag
  simpa using htag

/-- `throw_ref-handler-catch` does not fire on a clause that does not match. -/
theorem not_ruleBody_catchC (Hp : HelpersC env hn) {D : Interp} {els : Prop} {op : MixopS}
    {s : Store H} {f : Frame} {n a : Nat} {c : Catch} {cs : List Catch} {c' : Value}
    (hnm : ¬ CatchMatches s f a c) :
    ¬ RuleBody env D els [] [] op throwRefHandlerCatchRule
      (.tuple [cfgV (stateV hn s f) [handlerThrowV n (c :: cs) a], c']) := by
  rintro ⟨-, ρ₀, σ, hps, -, he, hp⟩
  obtain rfl : VarEnv.empty = ρ₀ := Option.some.inj hps
  obtain ⟨hz, hce, -⟩ := evalExp_concl_inv he
  obtain ⟨-, h3⟩ := evalExp_case_inv (evalExp_list1_inv hce)
  obtain ⟨-, hcs, hthrow⟩ := evalExp_tup3_inv h3
  obtain ⟨w, hcw, hw⟩ := catch_head hcs
  obtain ⟨x, l, rfl, hcm⟩ := catch_of_tag (H := H) hcw (.inl rfl)
  obtain ⟨hx, -⟩ := evalExp_tup2_inv hw
  obtain ⟨ha, -⟩ := evalExps_two_inv (evalExp_list_inv hthrow)
  obtain ⟨-, ha'⟩ := evalExp_case_inv ha
  cases hp _ (List.mem_cons_self ..) with
  | ifPr h =>
      exact hnm (hcm s f a (tagMatch_of_premC Hp (evalExp_varE_iff.1 hz) (evalExp_varE_iff.1 ha')
        (evalExp_varE_iff.1 hx) rfl rfl h))

/-- `throw_ref-handler-catch_ref` does not fire on a clause that does not match. -/
theorem not_ruleBody_catchRefC (Hp : HelpersC env hn) {D : Interp} {els : Prop} {op : MixopS}
    {s : Store H} {f : Frame} {n a : Nat} {c : Catch} {cs : List Catch} {c' : Value}
    (hnm : ¬ CatchMatches s f a c) :
    ¬ RuleBody env D els [] [] op throwRefHandlerCatchRefRule
      (.tuple [cfgV (stateV hn s f) [handlerThrowV n (c :: cs) a], c']) := by
  rintro ⟨-, ρ₀, σ, hps, -, he, hp⟩
  obtain rfl : VarEnv.empty = ρ₀ := Option.some.inj hps
  obtain ⟨hz, hce, -⟩ := evalExp_concl_inv he
  obtain ⟨-, h3⟩ := evalExp_case_inv (evalExp_list1_inv hce)
  obtain ⟨-, hcs, hthrow⟩ := evalExp_tup3_inv h3
  obtain ⟨w, hcw, hw⟩ := catch_head hcs
  obtain ⟨x, l, rfl, hcm⟩ := catch_of_tag (H := H) hcw (.inr rfl)
  obtain ⟨hx, -⟩ := evalExp_tup2_inv hw
  obtain ⟨ha, -⟩ := evalExps_two_inv (evalExp_list_inv hthrow)
  obtain ⟨-, ha'⟩ := evalExp_case_inv ha
  cases hp _ (List.mem_cons_self ..) with
  | ifPr h =>
      exact hnm (hcm s f a (tagMatch_of_premC Hp (evalExp_varE_iff.1 hz) (evalExp_varE_iff.1 ha')
        (evalExp_varE_iff.1 hx) rfl rfl h))

/-- `throw_ref-handler-catch_all(_ref)` do not fire on a clause that does not match (no clause
of either kind fails to match). -/
theorem not_ruleBody_catchAllC {D : Interp} {els : Prop} {op : MixopS} {nm : IL.Id}
    {qs : List Param} {op' cop : MixopS} {ze ne ae re ke rhs : Exp} {prems : List Prem}
    {s : Store H} {f : Frame} {z : Value} {n a : Nat} {c : Catch} {cs : List Catch} {c' : Value}
    (hop : cop = "CATCH_ALL" ∨ cop = "CATCH_ALL_REF") (hnm : ¬ CatchMatches s f a c) :
    ¬ RuleBody env D els [] [] op
      (.ruleD nm qs op' (.tupE [.caseE "%;%" (.tupE [ze, .listE [.caseE "HANDLER_%{%}%"
        (.tupE [ne, .catE (.listE [.caseE cop ke]) ae, re])]]), rhs]) prems)
      (.tuple [cfgV z [handlerThrowV n (c :: cs) a], c']) := by
  rintro ⟨-, ρ₀, σ, -, -, he, -⟩
  obtain ⟨-, hce, -⟩ := evalExp_concl_inv he
  obtain ⟨-, h3⟩ := evalExp_case_inv (evalExp_list1_inv hce)
  obtain ⟨-, hcs, -⟩ := evalExp_tup3_inv h3
  obtain ⟨w, hcw, -⟩ := catch_head hcs
  exact hnm (catchMatches_of_all hcw hop)

/-- `throw_ref-handler-empty` does not fire on a non-empty handler. -/
theorem not_ruleBody_emptyC {D : Interp} {els : Prop} {op : MixopS} {z : Value} {n a : Nat}
    {c : Catch} {cs : List Catch} {c' : Value} :
    ¬ RuleBody env D els [] [] op throwRefHandlerEmptyRule
      (.tuple [cfgV z [handlerThrowV n (c :: cs) a], c']) := by
  rintro ⟨-, ρ₀, σ, -, -, he, -⟩
  obtain ⟨-, hce, -⟩ := evalExp_concl_inv he
  obtain ⟨-, h3⟩ := evalExp_case_inv (evalExp_list1_inv hce)
  obtain ⟨-, hcs, -⟩ := evalExp_tup3_inv h3
  have := evalExps_nil_iff.1 (evalExp_list_inv hcs)
  simp at this

/-- `return_call_ref-handler` does not fire on a handler whose body is a thrown exception. -/
theorem not_ruleBody_returnCallRefHandlerC {D : Interp} {els : Prop} {op : MixopS} {z : Value}
    {n a : Nat} {cs : List Catch} {c' : Value} :
    ¬ RuleBody env D els [] [] op returnCallRefHandlerRule
      (.tuple [cfgV z [handlerThrowV n cs a], c']) := by
  refine not_ruleBody_of_code fun ρ h => ?_
  obtain ⟨-, h3⟩ := evalExp_case_inv (evalExp_list1_inv h)
  obtain ⟨-, -, hb⟩ := evalExp_tup3_inv h3
  obtain ⟨w, hw⟩ := shape_memCase hb
  simp [caseNilV] at hw

/-- **The `otherwise` premise of `throw_ref-handler-next`.** No earlier `Step_read` rule fires on
a handler whose first clause does not match the exception. -/
theorem otherwiseAt_handlerNextC (R : HasReadRules env) (Hp : HelpersC env hn) {s : Store H}
    {f : Frame} {n a : Nat} {c : Catch} {cs : List Catch} {b : Value}
    (hnm : ¬ CatchMatches s f a c) :
    otherwiseAt env "Step_read" [] 21
      (.tuple [cfgV (stateV hn s f) [handlerThrowV n (c :: cs) a], b]) := by
  rw [otherwiseAt]
  intro j hj ps op t rules r hrel hr w hsame
  obtain ⟨u, b₁, c', hv, rfl⟩ := hsame
  obtain ⟨rfl, -⟩ : cfgV (stateV hn s f) [handlerThrowV n (c :: cs) a] = u ∧ b = b₁ := by
    simpa using hv
  obtain rfl : ps = [] := by
    obtain ⟨ps', t', rules', hrel', hps', -⟩ := R.block
    rw [hrel] at hrel'
    simp only [Option.some.injEq, Prod.mk.injEq] at hrel'
    rw [hrel'.1, hps']
  have code : ∀ {nm qs op' ze ce re prems},
      (∀ ρ : VarEnv, ¬ EvalExp env ρ ce (.list [handlerThrowV n (c :: cs) a])) →
      ¬ RuleBody env (DDerives env noElse) (otherwiseAt env "Step_read" [] j
        (.tuple [cfgV (stateV hn s f) [handlerThrowV n (c :: cs) a], c'])) [] [] op
        (.ruleD nm qs op' (.tupE [.caseE "%;%" (.tupE [ze, ce]), re]) prems)
        (.tuple [cfgV (stateV hn s f) [handlerThrowV n (c :: cs) a], c']) := by
    intro nm qs op' ze ce re prems hce
    exact not_ruleBody_of_code hce
  match j, hj, hr with
  | 0, _, hr =>
    rw [rule_of_hasRuleAt R.block hrel hr]
    exact code fun _ h => absurd (shape_catCase h) (by decide)
  | 1, _, hr =>
    rw [rule_of_hasRuleAt R.loop hrel hr]
    exact code fun _ h => absurd (shape_catCase h) (by decide)
  | 2, _, hr =>
    rw [rule_of_hasRuleAt R.brOnCastSucceed hrel hr]
    exact code fun _ h => shape_list2 h
  | 3, _, hr =>
    rw [rule_of_hasRuleAt R.brOnCastFail hrel hr]
    exact code fun _ h => shape_list2 h
  | 4, _, hr =>
    rw [rule_of_hasRuleAt R.brOnCastFailSucceed hrel hr]
    exact code fun _ h => shape_list2 h
  | 5, _, hr =>
    rw [rule_of_hasRuleAt R.brOnCastFailFail hrel hr]
    exact code fun _ h => shape_list2 h
  | 6, _, hr =>
    rw [rule_of_hasRuleAt R.call hrel hr]
    exact code fun _ h => absurd (shape_list1Case h) (by decide)
  | 7, _, hr =>
    rw [rule_of_hasRuleAt R.returnCall hrel hr]
    exact code fun _ h => absurd (shape_list1Case h) (by decide)
  | 8, _, hr =>
    rw [rule_of_hasRuleAt R.returnCallRefLabel hrel hr]
    exact code fun _ h => absurd (shape_list1Case h) (by decide)
  | 9, _, hr =>
    rw [rule_of_hasRuleAt R.returnCallRefHandler hrel hr]
    exact not_ruleBody_returnCallRefHandlerC
  | 10, _, hr =>
    rw [rule_of_hasRuleAt R.returnCallRefFrameNull hrel hr]
    exact code fun _ h => absurd (shape_list1Case h) (by decide)
  | 11, _, hr =>
    rw [rule_of_hasRuleAt R.returnCallRefFrameAddr hrel hr]
    exact code fun _ h => absurd (shape_list1Case h) (by decide)
  | 12, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefNull hrel hr]
    exact code fun _ h => shape_list2 h
  | 13, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefInstrs hrel hr]
    exact code fun _ h => shape_cat2 h
  | 14, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefLabel hrel hr]
    exact code fun _ h => absurd (shape_list1Case h) (by decide)
  | 15, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefFrame hrel hr]
    exact code fun _ h => absurd (shape_list1Case h) (by decide)
  | 16, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefHandlerEmpty hrel hr]
    exact not_ruleBody_emptyC
  | 17, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefHandlerCatch hrel hr]
    exact not_ruleBody_catchC Hp hnm
  | 18, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefHandlerCatchRef hrel hr]
    exact not_ruleBody_catchRefC Hp hnm
  | 19, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefHandlerCatchAll hrel hr]
    exact not_ruleBody_catchAllC (.inl rfl) hnm
  | 20, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefHandlerCatchAllRef hrel hr]
    exact not_ruleBody_catchAllC (.inr rfl) hnm
  | k + 21, h, _ => omega

/-- `Step_read/throw_ref-handler-next`: a clause that does not match is dropped. -/
theorem sread_throwRefHandlerNextC (R : HasReadRules env) (Hp : HelpersC env hn)
    (hr : HasRuleAt env "Step_read" "%~>%" 21 throwRefHandlerNextRule)
    {s : Store H} {f : Frame} {n a : Nat} {c : Catch} {cs : List Catch}
    (hnm : ¬ CatchMatches s f a c) (hz : TypedV env stateT (stateV hn s f))
    (hn₀ : TypedV env nT (.num (.natN n))) (hc : TypedV env catchT (Encode.toValue c))
    (hcs : TypedV env catchesT (.list (cs.map Encode.toValue)))
    (ha : TypedV env addrT (.num (.natN a))) :
    SRead env (cfgV (stateV hn s f) (adminsToV [.handler n (c :: cs) (throwing a)]))
      (adminsToV [.handler n cs (throwing a)]) := by
  let ρ := VarEnv.empty.bindVals [("z", stateV hn s f), ("n", .num (.natN n)),
    ("catch", Encode.toValue c), ("catch'*", .list (cs.map Encode.toValue)),
    ("a", .num (.natN a))]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stateV hn s f) := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN n)) := rfl
  have fc : ρ.findVal? "catch" = some (Encode.toValue c) := rfl
  have fcs : ρ.findVal? "catch'*" = some (.list (cs.map Encode.toValue)) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  have ecs : EvalExp env ρ (.iterE (.varE "catch'") (.mk .list [.mk "catch'" (.varE "catch'*")]))
      (.list (cs.map Encode.toValue)) := evalExp_iterPat (by decide) fcs
  exact dderives_of_ruleAt hr _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hn₀ ρ hρ) (QuantsOk.cons fc (hc ρ hρ)
      (QuantsOk.cons fcs (hcs ρ hρ) (QuantsOk.cons fa (ha ρ hρ) QuantsOk.nil)))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
          (evalExp_cat (evalExp_list1 (evalExp_var fc)) ecs) (evalExp_throwExn fa))))))
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ecs (evalExp_throwExn fa)))))
    (prems_one (.elsePr (otherwiseAt_handlerNextC R Hp hnm)))

end Next

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
