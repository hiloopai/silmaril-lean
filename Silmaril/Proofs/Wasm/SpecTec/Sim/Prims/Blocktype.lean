module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Prims.Expand

/-!
# The concrete `B`: `$blocktype_`

`$blocktype_(z, _RESULT t?) = eps -> t?` is evaluated by its clause. `$blocktype_(z, _IDX x)`'s
clause binds `t_1*`, `t_2*` only through its `Expand` premise, so it definitely fails (the asserted
instance cannot be evaluated) and `callDef` takes `B`'s answer, the image of Core's
`blockType? (.typeIdx x)` read off the encoded module (`blocktypeCall`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Prims

variable {prof : Silmaril.Wasm.Numerics.Profile}

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef not_tryClauses_and_undef)
open Silmaril.SpecTec.Equiv.ExecBuiltins (matchExp_caseE_undef_of_ne)
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_inj)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- `t_1* ->_[] t_2*` with both sides iterated over a domain. -/
def btIter (x xs : IL.Id) : Exp := .iterE (.varE x) (.mk .list [.mk x (.varE xs)])

/-- The `Expand` premise of the `_IDX` clause. -/
def btPrem : Prem :=
  .rulePr "Expand" [] "%~~%" (.tupE [.callE "type" [.expA (.varE "z"), .expA (.varE "x")],
    .caseE "FUNC%->%" (.tupE [.caseE "%" (.tupE [btIter "t_1" "t_1*"]),
      .caseE "%" (.tupE [btIter "t_2" "t_2*"])])])

/-- `t?`, iterated. -/
def tOpt : Exp := .iterE (.varE "t") (.mk .opt [.mk "t" (.varE "t?")])

/-- The body of the `_RESULT` clause: `eps -> t?`. -/
def btBody₂ : Exp :=
  .caseE "%->_%%" (.tupE [.caseE "%" (.tupE [.listE []]), .listE [],
    .caseE "%" (.tupE [.liftE tOpt])])

/-- `$blocktype_` and `$type`, as the script has them. -/
structure BlocktypeDefs (env : Env) : Prop where
  blocktype : ∃ ps t q₁ body₁ q₂, env.findDef? "blocktype_" = some (ps, t,
    [.defD q₁ [.expA (.varE "z"), .expA (.caseE "_IDX" (.varE "x"))] body₁ [btPrem],
     .defD q₂ [.expA (.varE "z"), .expA (.caseE "_RESULT" tOpt)] btBody₂ []])
  type : State.HasClause1 env "type" State.zxPat
    (.idxE (.dotE (.dotE (.callE "fof" [.expA (.varE "z")]) "MODULE") "TYPES") State.idxPayload)

set_option maxRecDepth 100000 in
/-- `simEnv B` has them. -/
theorem blocktypeDefs_simEnv (B : Builtins) : BlocktypeDefs (simEnv B) :=
  ⟨⟨_, _, _, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩

/-- `instrTypeV [] T`. -/
theorem evalExp_btBody₂ {env : Env} {ρ : VarEnv} {o : Option Value}
    (h : ρ.findVal? "t?" = some (.opt o)) :
    EvalExp env ρ btBody₂ (Exn.instrTypeV [] o.toList) := by
  have ht : EvalExp env ρ tOpt (.opt o) :=
    IntNumeric.evalExp_iterOpt h (fun w hw => ⟨w, hw, evalExp_var rfl⟩) id
  exact evalExp_case (evalExp_tup3 (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons
    (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩) evalExps_nil, rfl⟩))
    (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩)
    (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_liftE_iff.2 ⟨o, ht, rfl⟩)
      evalExps_nil, rfl⟩)))

/-! ## Reading Core's block type off the image -/

/-- The module types of an encoded state. -/
theorem moduleTypesV_stateV (hn : H → String) (s : Store H) (f : Frame) :
    moduleTypesV? (stateV hn s f) = some (f.module.types.map tyV) := rfl

/-- `tyInv` reads back a list of images. -/
theorem mapM_tyInv {k : TKind} : ∀ l : List (Ty k), (l.map tyV).mapM (tyInv k) = some l
  | [] => rfl
  | t :: l => by simp [tyInv_tyV, mapM_tyInv l]

/-- `tyInv ∘ tyV` is `some`, on lists. -/
theorem mapM_tyInv_comp {k : TKind} : ∀ l : List (Ty k), l.mapM (tyInv k ∘ tyV) = some l
  | [] => rfl
  | t :: l => by simp [tyInv_tyV, mapM_tyInv_comp l]

/-- `funcType?` comes from a function type. -/
theorem funcType?_inv {d : DefType} {t₁ t₂ : List CValType} (h : DefType.funcType? d = some (t₁, t₂)) :
    ∃ ps rs : Ty (.list .val), d.expand? = some (.func ps rs) ∧ t₁ = ps.toList ∧ t₂ = rs.toList := by
  unfold DefType.funcType? at h
  split at h
  · rename_i ps rs he
    cases h
    exact ⟨ps, rs, he, rfl, rfl⟩
  · cases h

/-- `blocktypeCall` on images is Core's `blockType? (.typeIdx x)`. -/
theorem blocktypeCall_stateV (hn : H → String) (s : Store H) (f : Frame) (x : TypeIdx) :
    blocktypeCall (stateV hn s f) (Encode.toValue x) =
      (f.module.blockType? (.typeIdx x)).map fun p => Exn.instrTypeV (p.1.map tyV) (p.2.map tyV) := by
  simp only [blocktypeCall, moduleTypesV_stateV, ModuleInst.blockType?]
  simp [mapM_tyInv_comp, Encode.ofValue_toValue]
  cases f.module.types[x.toNat]? with
  | none => rfl
  | some d => cases h : DefType.funcType? d <;> simp [h]

/-! ## The forward direction -/

/-- `z` matches, `_IDX x` does not match `_RESULT …`. -/
theorem matchArgsUndef_idx {env : Env} {Z w : Value} :
    MatchArgsUndef env VarEnv.empty [.expA (.varE "z"), .expA (.caseE "_IDX" (.varE "x"))]
      [.val Z, .val (.case "_RESULT" w)] :=
  matchArgs_cons_undef_tail (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef_of_ne (by decide))))

/-- `z` matches, `_RESULT t?` does not match `_IDX …`. -/
theorem matchArgsUndef_result {env : Env} {Z w : Value} :
    MatchArgsUndef env VarEnv.empty [.expA (.varE "z"), .expA (.caseE "_RESULT" tOpt)]
      [.val Z, .val (.case "_IDX" w)] :=
  matchArgs_cons_undef_tail (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef_of_ne (by decide))))

/-- `$blocktype_(z, _RESULT t?)` evaluates its second clause. -/
theorem applies_blocktypeResult {env : Env} (D : BlocktypeDefs env) (Z : Value)
    (o : Option Value) :
    Applies env "blocktype_" [.val Z, .val (.case "_RESULT" (.opt o))]
      (Exn.instrTypeV [] o.toList) := by
  obtain ⟨ps, t, q₁, body₁, q₂, hd⟩ := D.blocktype
  have hm : ∃ ρ₀, MatchArgs env VarEnv.empty [.expA (.varE "z"), .expA (.caseE "_RESULT" tOpt)]
      [.val Z, .val (.case "_RESULT" (.opt o))] ρ₀ ∧ ρ₀.findVal? "t?" = some (.opt o) := by
    cases o with
    | none =>
      exact ⟨_, matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
        (matchArg_expA (matchExp_caseE (Silmaril.SpecTec.Equiv.Execution.matchExp_iterE_opt_iff.2
          (Or.inl ⟨rfl, matchExp_varE rfl⟩)))) matchArgs_nil), rfl⟩
    | some w =>
      exact ⟨_, matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
        (matchArg_expA (matchExp_caseE (Silmaril.SpecTec.Equiv.Execution.matchExp_iterE_opt_iff.2
          (Or.inr ⟨w, _, w, rfl, matchExp_varE rfl, rfl, matchExp_varE rfl⟩)))) matchArgs_nil),
        rfl⟩
  obtain ⟨ρ₀, hm, hρ₀⟩ := hm
  exact ⟨ps, t, _, hd, Or.inl (tryClauses_skip_match matchArgsUndef_idx
    (tryClauses_hit hm premsHold_nil (evalExp_btBody₂ hρ₀)))⟩

/-- `$type(z, x)` on an encoded state, in range. -/
theorem evalExp_type {env : Env} (D : BlocktypeDefs env) (S : State.StateDefs env)
    (hn : H → String) (s : Store H) (f : Frame) (x : TypeIdx) {d : DefType}
    (hx : f.module.types[x.toNat]? = some d) :
    EvalExp env ((VarEnv.empty.bindVal "z" (stateV hn s f)).bindVal "x" (Encode.toValue x))
      (.callE "type" [.expA (.varE "z"), .expA (.varE "x")]) (tyV d) :=
  State.evalExp_call1 D.type rfl (Equiv.evalArgs_cons (evalExp_var rfl)
      (Equiv.evalArgs_cons (evalExp_var rfl) Equiv.evalArgs_nil)) State.matchArgs_zxPat
    (evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2 ⟨_, evalExp_dotE_iff.2 ⟨_,
      State.evalExp_fof S rfl (evalExp_var rfl), rfl⟩, rfl⟩, State.evalExp_idxPayload rfl,
      by simp [Value.idx?, hx]⟩)

/-- `$blocktype_(z, _IDX x)`'s clauses definitely fail on an encoded state, `x` in range. -/
theorem blocktype_idx_undef {env : Env} (D : BlocktypeDefs env) (S : State.StateDefs env)
    (hn : H → String) (s : Store H) (f : Frame) (x : TypeIdx) {d : DefType}
    (hx : f.module.types[x.toNat]? = some d) :
    ∃ ps t cs, env.findDef? "blocktype_" = some (ps, t, cs) ∧
      TryClausesUndef env cs [.val (stateV hn s f), .val (.case "_IDX" (Encode.toValue x))] := by
  obtain ⟨ps, t, q₁, body₁, q₂, hd⟩ := D.blocktype
  refine ⟨ps, t, _, hd, IntNumeric.tryClausesUndef_skip_prem
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA
      (matchExp_caseE (matchExp_varE rfl))) matchArgs_nil)) ?_
    (IntNumeric.tryClausesUndef_skip_match matchArgsUndef_result IntNumeric.tryClausesUndef_nil)⟩
  exact premsUndef_rule (ws := []) Equiv.evalArgs_nil (evalExpUndef_tup (pre := [_]) (post := [])
    (evalExps_cons (evalExp_type D S hn s f x hx) evalExps_nil)
    (evalExpUndef_case (evalExpUndef_tup (pre := []) evalExps_nil (evalExpUndef_case
      (evalExpUndef_tup (pre := []) (post := []) evalExps_nil
        (evalExpUndef_iterList (evalExpUndef_var rfl)))))))

/-- `B` answers `$blocktype_(z, _IDX x)` by `blocktypeCall`. -/
theorem call_blocktype (hn : H → String) (host : HostSemantics H) (z w : Value) :
    (builtins prof hn host).call "blocktype_" [.val z, .val (.case "_IDX" w)] = blocktypeCall z w := by
  simp [builtins, call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]

/-- `$blocktype_(z, _IDX x)` on images: `B`'s answer. -/
theorem applies_blocktypeIdx (hn : H → String) (host : HostSemantics H) (s : Store H) (f : Frame)
    (x : TypeIdx) (t₁ t₂ : List CValType) (h : f.module.blockType? (.typeIdx x) = some (t₁, t₂)) :
    ∃ T₁ T₂ : List Value, T₁.length = t₁.length ∧ T₂.length = t₂.length ∧
      ((∃ ts : List ValType, T₁ = [] ∧ T₂ = ts.map Encode.toValue) ∨
        (∃ ps rs : Ty (.list .val), T₁ = ps.toList.map tyV ∧ T₂ = rs.toList.map tyV)) ∧
      Applies (simEnv (builtins prof hn host)) "blocktype_"
        [.val (stateV hn s f), .val (Encode.toValue (BlockType.typeIdx x))]
        (Exn.instrTypeV T₁ T₂) := by
  obtain ⟨d, hx, hft⟩ : ∃ d, f.module.types[x.toNat]? = some d ∧
      DefType.funcType? d = some (t₁, t₂) := by
    simpa only [ModuleInst.blockType?, Option.bind_eq_bind, Option.bind_eq_some_iff] using h
  obtain ⟨ps, rs, -, rfl, rfl⟩ := funcType?_inv hft
  obtain ⟨ps', t', cs, hd, hu⟩ := blocktype_idx_undef (blocktypeDefs_simEnv _)
    (State.stateDefs_simEnv _) hn s f x hx
  have hb : (builtins prof hn host).call "blocktype_" [.val (stateV hn s f),
      .val (.case "_IDX" (Encode.toValue x))] =
      some (Exn.instrTypeV (ps.toList.map tyV) (rs.toList.map tyV)) := by
    rw [call_blocktype, blocktypeCall_stateV, h]
    rfl
  exact ⟨_, _, List.length_map _, List.length_map _, Or.inr ⟨ps, rs, rfl, rfl⟩,
    ps', t', cs, hd, Or.inr ⟨hu, hb⟩⟩

/-- **`$blocktype_` on images**, for the concrete `B`: Core's block type, with the result types
encoded as source value types (`_RESULT`) or as images of closed types (`_IDX`). -/
theorem applies_blocktype (hn : H → String) (host : HostSemantics H) (s : Store H) (f : Frame)
    (bt : BlockType) (t₁ t₂ : List CValType) (h : f.module.blockType? bt = some (t₁, t₂)) :
    ∃ T₁ T₂ : List Value, T₁.length = t₁.length ∧ T₂.length = t₂.length ∧
      ((∃ ts : List ValType, T₁ = [] ∧ T₂ = ts.map Encode.toValue) ∨
        (∃ ps rs : Ty (.list .val), T₁ = ps.toList.map tyV ∧ T₂ = rs.toList.map tyV)) ∧
      Applies (simEnv (builtins prof hn host)) "blocktype_"
        [.val (stateV hn s f), .val (Encode.toValue bt)] (Exn.instrTypeV T₁ T₂) := by
  have D := blocktypeDefs_simEnv (builtins prof hn host)
  cases bt with
  | empty =>
    simp only [ModuleInst.blockType?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], [], rfl, rfl, Or.inl ⟨[], rfl, rfl⟩, applies_blocktypeResult D _ none⟩
  | value t =>
    simp only [ModuleInst.blockType?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], [Encode.toValue t], rfl, rfl, Or.inl ⟨[t], rfl, rfl⟩,
      applies_blocktypeResult D _ (some (Encode.toValue t))⟩
  | typeIdx x => exact applies_blocktypeIdx hn host s f x t₁ t₂ h

/-! ## The converse -/

/-- `instrTypeV` is injective. -/
theorem instrTypeV_inj {a b c d : List Value} (h : Exn.instrTypeV a b = Exn.instrTypeV c d) :
    a = c ∧ b = d := by
  simpa [Exn.instrTypeV] using h

/-- The `Expand` premise of the `_IDX` clause never holds: its asserted instance mentions `t_1*`,
which the clause does not bind. -/
theorem not_premsHold_btPrem {env : Env} {Z w : Value} {ρ' : VarEnv} :
    ¬ PremsHold env ((VarEnv.empty.bindVal "z" Z).bindVal "x" w) [btPrem] ρ' := by
  intro h
  obtain ⟨v, hv⟩ := evalExp_of_premsHold_rule h
  obtain ⟨u, hu⟩ := evalExp_of_tupE_mem hv (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  obtain ⟨u, hu⟩ := evalExp_of_caseE hu
  obtain ⟨u, hu⟩ := evalExp_of_tupE_mem hu List.mem_cons_self
  obtain ⟨u, hu⟩ := evalExp_of_caseE hu
  obtain ⟨u, hu⟩ := evalExp_of_tupE_mem hu (List.mem_singleton_self _)
  exact not_evalExp_of_undef (evalExpUndef_iterList (b := .varE "t_1") (x := "t_1")
    (evalExpUndef_var (x := "t_1*") rfl)) hu

/-- At `_IDX x`, the clauses of `$blocktype_` never give a value. -/
theorem not_tryClauses_blocktypeIdx {env : Env} (D : BlocktypeDefs env) {Z w v : Value} :
    ∃ ps t cs, env.findDef? "blocktype_" = some (ps, t, cs) ∧
      ¬ TryClauses env cs [.val Z, .val (.case "_IDX" w)] v := by
  obtain ⟨ps, t, q₁, body₁, q₂, hd⟩ := D.blocktype
  refine ⟨ps, t, _, hd, ?_⟩
  rintro ⟨n, hn⟩
  rcases tryClauses_cons_elim hn with ⟨ρ₀, ρ₁, hm, hp, -⟩ | ⟨n₂, hn₂⟩
  · have hm₀ : MatchArgs env VarEnv.empty [.expA (.varE "z"), .expA (.caseE "_IDX" (.varE "x"))]
        [.val Z, .val (.case "_IDX" w)] ((VarEnv.empty.bindVal "z" Z).bindVal "x" w) :=
      matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_varE rfl))) matchArgs_nil)
    rw [matchArgs_unique hm hm₀] at hp
    exact not_premsHold_btPrem hp
  · rcases tryClauses_cons_elim hn₂ with ⟨ρ₀, ρ₁, hm, -, -⟩ | ⟨n₃, hn₃⟩
    · exact not_matchArgs_of_undef matchArgsUndef_result hm
    · cases n₃ <;> simp [tryClauses] at hn₃

/-- `$blocktype_(z, _IDX x)` reads back to Core's block type. -/
theorem blocktype_inv_idx (hn : H → String) (host : HostSemantics H) (s : Store H) (f : Frame)
    (x : TypeIdx) (v₁ v₂ : List Value)
    (h : Applies (simEnv (builtins prof hn host)) "blocktype_"
      [.val (stateV hn s f), .val (.case "_IDX" (Encode.toValue x))] (Exn.instrTypeV v₁ v₂)) :
    ∃ t₁ t₂ : List CValType, f.module.blockType? (.typeIdx x) = some (t₁, t₂) ∧
      v₁.length = t₁.length ∧ v₂.length = t₂.length := by
  obtain ⟨ps, t, cs, hd, hc⟩ := h
  obtain ⟨ps', t', cs', hd', hn'⟩ := not_tryClauses_blocktypeIdx (blocktypeDefs_simEnv
    (builtins prof hn host)) (Z := stateV hn s f) (w := Encode.toValue x) (v := Exn.instrTypeV v₁ v₂)
  obtain ⟨rfl, rfl, rfl⟩ : ps' = ps ∧ t' = t ∧ cs' = cs := by simpa [hd'] using hd
  have hb : blocktypeCall (stateV hn s f) (Encode.toValue x) = some (Exn.instrTypeV v₁ v₂) := by
    rcases hc with hc | ⟨-, hb⟩
    · exact absurd hc hn'
    · exact (call_blocktype hn host _ _).symm.trans hb
  rw [blocktypeCall_stateV, Option.map_eq_some_iff] at hb
  obtain ⟨⟨t₁, t₂⟩, hbt, he⟩ := hb
  obtain ⟨rfl, rfl⟩ := instrTypeV_inj he.symm
  exact ⟨t₁, t₂, hbt, List.length_map _, List.length_map _⟩

/-- **`$blocktype_` reads back to Core's block type**, for the concrete `B`. -/
theorem blocktype_inv (hn : H → String) (host : HostSemantics H) (s : Store H) (f : Frame)
    (bt : BlockType) (v₁ v₂ : List Value)
    (h : Applies (simEnv (builtins prof hn host)) "blocktype_"
      [.val (stateV hn s f), .val (Encode.toValue bt)] (Exn.instrTypeV v₁ v₂)) :
    ∃ t₁ t₂ : List CValType, f.module.blockType? bt = some (t₁, t₂) ∧
      v₁.length = t₁.length ∧ v₂.length = t₂.length := by
  have D := blocktypeDefs_simEnv (builtins prof hn host)
  cases bt with
  | empty =>
    obtain ⟨rfl, rfl⟩ := instrTypeV_inj (Applies.unique h (applies_blocktypeResult D _ none))
    exact ⟨[], [], rfl, rfl, rfl⟩
  | value t =>
    obtain ⟨rfl, rfl⟩ :=
      instrTypeV_inj (Applies.unique h (applies_blocktypeResult D _ (some (Encode.toValue t))))
    exact ⟨_, _, rfl, rfl, rfl⟩
  | typeIdx x => exact blocktype_inv_idx hn host s f x v₁ v₂ h

end Silmaril.Wasm.SpecTec.Sim.Prims
