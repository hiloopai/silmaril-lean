module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.NumInt
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Convert

/-!
# The wasm-1.0 `$cvtop__`, at every V1 conversion

wasm-1.0's `$cvtop__` (`Original.d144`) has eight clauses, in the order `EXTEND` (`I32 → I64`),
`WRAP` (`I64 → I32`), `TRUNC sx` (`Fnn → Inn`), `PROMOTE` (`F32 → F64`), `DEMOTE` (`F64 → F32`),
`CONVERT sx` (`Inn → Fnn`), `REINTERPRET` (`Inn → Fnn`), `REINTERPRET` (`Fnn → Inn`). Unlike 2.0's,
the first two and the float resizings name their number types as literals, so `EXTEND`/`WRAP`
are not generic over integer pairs. The `REINTERPRET` clauses check `$size(Inn) = $size(Fnn)`.
Every clause calls a `hint(builtin)` primitive, answered by `Floats.FloatB P B`.

`applies_cvtop10`: at every V1 conversion `op` (`V1.ConvertOp`, the 1.0 conversions only) and
operand `x`, `$cvtop__` returns a list `L` with the 3.0 float track's
`Floats.CvtOk P op.toCore x L`:
its members are exactly the encodings of the profile's results, and it is empty exactly when the
profile traps.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (defOf evalExp_list1Call)
open Silmaril.Wasm.SpecTec.Sim.Floats (FloatB floatCall convRes bitsWhere CvtOk)
open Silmaril.Wasm.SpecTec.Sim20 (numTypeV sxV)
open Silmaril.Wasm.SpecTec.Sim20.Pure (matchArg_subVar20)
open Silmaril.Wasm.SpecTec.Scripts.Wasm10 (Original.d144)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit
  V1.ConvertOp.toCore ConvertOp.source ConvertOp.target

variable {B : Builtins} {P : Profile}

set_option maxRecDepth 100000 in
theorem findDef_cvtop10 : (simEnv10 B).findDef? "cvtop__" = defOf Original.d144 := rfl

/-- Skip a `$cvtop__` clause: its first, second or third argument pattern definitely fails, after
the earlier ones match (a literal number type or a kind pattern). -/
macro "skipCvt10" : tactic => `(tactic| repeat (refine tryClauses_skip_match (by
    first
    | exact matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef (by decide)))
    | exact matchArgs_cons_undef (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub (by rfl))
    | exact matchArgs_cons_undef_tail (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef (by decide))))
    | exact matchArgs_cons_undef_tail (matchArg_subVar20 (by simp) (by rfl))
        (matchArgs_cons_undef (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub (by rfl)))
    | exact matchArgs_cons_undef_tail (matchArg_subVar20 (by simp) (by rfl))
        (matchArgs_cons_undef_tail (matchArg_subVar20 (by simp) (by rfl))
          (matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef (by decide)))))) ?_))

/-- The arguments of `$cvtop__` at a V1 conversion. -/
abbrev cvtArgs10 (op : V1.ConvertOp) (x : BitVec op.toCore.source.width) : List ArgV :=
  [.val (numTypeV op.toCore.source), .val (numTypeV op.toCore.target), .val (cvtOpV op),
    .val (numV ⟨op.toCore.source, x⟩)]

/-- The 1.0 encoding of a number is the 3.0 track's. -/
theorem numV_eq_sim (t : NumType) (z : BitVec t.width) : numV ⟨t, z⟩ = Sim.numV ⟨t, z⟩ := by
  cases t <;> rfl

/-- A literal number-type pattern matches its type. -/
theorem matchArg_lit10 {ρ : VarEnv} {o : MixopS} :
    MatchArg (simEnv10 B) ρ (.expA (.caseE o (.tupE []))) (.val (.case o (.tuple []))) ρ :=
  matchArg_expA (matchExp_caseE matchExp_tupE_nil)

/-- The operator pattern `o sx` and the operand. -/
theorem matchArgs_opSx10 {s : Signedness} {ρ : VarEnv} (hs : ρ.findVal? "sx" = none) {v : IL.Id}
    (hv : (ρ.bindVal "sx" (sxV s)).findVal? v = none) {o : MixopS} {a : Value} :
    MatchArgs (simEnv10 B) ρ [.expA (.caseE o (.varE "sx")), .expA (.varE v)]
      [.val (.case o (sxV s)), .val a] ((ρ.bindVal "sx" (sxV s)).bindVal v a) :=
  matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_varE hs)))
    (matchArgs_cons (matchArg_expA (matchExp_varE hv)) matchArgs_nil)

/-- The operator pattern `o` and the operand. -/
theorem matchArgs_opNil10 {ρ : VarEnv} {v : IL.Id} (hv : ρ.findVal? v = none) {o : MixopS}
    {a : Value} :
    MatchArgs (simEnv10 B) ρ [.expA (.caseE o (.tupE [])), .expA (.varE v)]
      [.val (.case o (.tuple [])), .val a] (ρ.bindVal v a) :=
  matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
    (matchArgs_cons (matchArg_expA (matchExp_varE hv)) matchArgs_nil)

/-- Variables and literals, as arguments. -/
theorem evalArgs_var10 {ρ : VarEnv} {x : IL.Id} {a : Value} {rest : List Arg} {ws : List ArgV}
    (hx : ρ.findVal? x = some a) (hr : EvalArgs (simEnv10 B) ρ rest ws) :
    EvalArgs (simEnv10 B) ρ (.expA (.varE x) :: rest) (.val a :: ws) :=
  Equiv.evalArgs_cons (evalExp_varE_iff.2 hx) hr

theorem evalArgs_lit10 {ρ : VarEnv} {n : Nat} {rest : List Arg} {ws : List ArgV}
    (hr : EvalArgs (simEnv10 B) ρ rest ws) :
    EvalArgs (simEnv10 B) ρ (.expA (.numE (.natN n)) :: rest) (.val (natV n) :: ws) :=
  Equiv.evalArgs_cons evalExp_num hr

theorem evalArgs_size10 {ρ : VarEnv} {X : IL.Id} {t : NumType} {u₁ u₂ : Typ} {rest : List Arg}
    {ws : List ArgV} (hd : ρ.findDef? "size" = none) (hX : ρ.findVal? X = some (numTypeV t))
    (hr : EvalArgs (simEnv10 B) ρ rest ws) :
    EvalArgs (simEnv10 B) ρ (.expA (.callE "size" [.expA (.subE (.varE X) u₁ u₂)]) :: rest)
      (.val (natV t.width) :: ws) :=
  Equiv.evalArgs_cons (evalExp_sizeK10 t hd hX) hr

theorem evalArgs_kind10 {ρ : VarEnv} {X : IL.Id} {t : NumType} {u₁ u₂ : Typ} {rest : List Arg}
    {ws : List ArgV} (hX : ρ.findVal? X = some (numTypeV t))
    (hr : EvalArgs (simEnv10 B) ρ rest ws) :
    EvalArgs (simEnv10 B) ρ (.expA (.subE (.varE X) u₁ u₂) :: rest) (.val (numTypeV t) :: ws) :=
  Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 hX)) hr

/-- `$size(Inn) = $size(Fnn)` holds at two number types of the same width. -/
theorem premsHold_sameSize10 {ρ : VarEnv} {X₁ X₂ : IL.Id} {t₁ t₂ : NumType}
    (h₁ : ρ.findVal? X₁ = some (numTypeV t₁)) (h₂ : ρ.findVal? X₂ = some (numTypeV t₂))
    (hd : ρ.findDef? "size" = none) (hw : t₁.width = t₂.width) {u₁ u₂ u₃ u₄ : Typ} :
    PremsHold (simEnv10 B) ρ [.ifPr (.cmpE .eqOp .boolT
      (.callE "size" [.expA (.subE (.varE X₁) u₁ u₂)])
      (.callE "size" [.expA (.subE (.varE X₂) u₃ u₄)]))] ρ := by
  have e₁ : EvalExp (simEnv10 B) ρ (.callE "size" [.expA (.subE (.varE X₁) u₁ u₂)])
      (natV t₁.width) := evalExp_sizeK10 t₁ hd h₁
  have e₂ : EvalExp (simEnv10 B) ρ (.callE "size" [.expA (.subE (.varE X₂) u₃ u₄)])
      (natV t₁.width) := hw ▸ evalExp_sizeK10 t₂ hd h₂
  have hc : EvalExp (simEnv10 B) ρ (.cmpE .eqOp .boolT
      (.callE "size" [.expA (.subE (.varE X₁) u₁ u₂)])
      (.callE "size" [.expA (.subE (.varE X₂) u₃ u₄)])) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, e₁, e₂, by simp [cmpValues]⟩
  exact Equiv.Validation.premsHold_cons_iff.2 ⟨_, Equiv.Validation.premHolds_if_iff.2 ⟨rfl, hc⟩,
    Equiv.Validation.premsHold_nil_iff.2 rfl⟩

/-- `$list_(X, $f(…))` of an option-valued call. -/
theorem evalExp_listOpt10 {ρ : VarEnv} {T : Typ} {f : IL.Id} {args : List Arg} {o : Option Value}
    (hρ : ρ.findDef? "list_" = none) (hc : CallDef (simEnv10 B) ρ f args (.opt o)) :
    EvalExp (simEnv10 B) ρ (.callE "list_" [.typA T, .expA (.callE f args)]) (.list o.toList) :=
  evalExp_callE_iff.2 (callDef_list10 hρ (Sim.Round5.FwdRef.evalArgs_typA
    (Equiv.evalArgs_cons (evalExp_callE_iff.2 hc) Equiv.evalArgs_nil)))

/-! ## The clauses -/

set_option maxRecDepth 100000 in
theorem applies_cvt_extend10 (hB : FloatB P B) (s : Signedness) (x : BitVec 32) :
    Applies (simEnv10 B) "cvtop__" (cvtArgs10 (.extend s) x)
      (.list [bvV (match s with | .signed => x.signExtend 64 | .unsigned => x.setWidth 64)]) := by
  have hc : floatCall P "extend__" [.val (natV 32), .val (natV 64), .val (sxV s),
      .val (Equiv.Execution.pctV x.toNat)] =
      some (bvV (match s with | .signed => x.signExtend 64 | .unsigned => x.setWidth 64)) := by
    cases s
    · exact Sim.Floats.floatCall_extend P 32 64 .signed x
    · exact Sim.Floats.floatCall_extend P 32 64 .unsigned x
  refine ⟨_, _, _, findDef_cvtop10, Or.inl ?_⟩
  exact tryClauses_hit (matchArgs_cons matchArg_lit10 (matchArgs_cons matchArg_lit10
    (matchArgs_opSx10 (by simp) (by simp)))) premsHold_nil
    (evalExp_list1Call (callDef_floatPrim10 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_lit10 (evalArgs_lit10 (evalArgs_var10 (by simp)
        (evalArgs_var10 (by simp; rfl) Equiv.evalArgs_nil)))) hc))

set_option maxRecDepth 100000 in
theorem applies_cvt_wrap10 (hB : FloatB P B) (x : BitVec 64) :
    Applies (simEnv10 B) "cvtop__" (cvtArgs10 .wrap x) (.list [bvV (x.setWidth 32)]) := by
  refine ⟨_, _, _, findDef_cvtop10, Or.inl ?_⟩
  skipCvt10
  exact tryClauses_hit (matchArgs_cons matchArg_lit10 (matchArgs_cons matchArg_lit10
    (matchArgs_opNil10 (by simp)))) premsHold_nil
    (evalExp_list1Call (callDef_floatPrim10 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_lit10 (evalArgs_lit10 (evalArgs_var10 (by simp; rfl) Equiv.evalArgs_nil)))
      (Sim.Floats.floatCall_wrap P 64 32 x)))

/-- The two kind patterns of a clause, matched. -/
theorem matchArgs_kinds10 {X₁ X₂ : IL.Id} {u₁ u₂ : Typ} {t₁ t₂ : NumType} {pats : List Arg}
    {ws : List ArgV} {ρ' : VarEnv} (hX₁ : X₁ ≠ "_") (hX : X₁ ≠ X₂)
    (h₁ : argSubOk (simEnv10 B) VarEnv.empty (.subE (.varE X₁) u₁ (.varT "valtype" []))
      (numTypeV t₁) = true)
    (h₂ : argSubOk (simEnv10 B) (VarEnv.empty.bindVal X₁ (numTypeV t₁))
      (.subE (.varE X₂) u₂ (.varT "valtype" [])) (numTypeV t₂) = true)
    (hr : MatchArgs (simEnv10 B) ((VarEnv.empty.bindVal X₁ (numTypeV t₁)).bindVal X₂
      (numTypeV t₂)) pats ws ρ') :
    MatchArgs (simEnv10 B) VarEnv.empty
      (.expA (.subE (.varE X₁) u₁ (.varT "valtype" [])) ::
        .expA (.subE (.varE X₂) u₂ (.varT "valtype" [])) :: pats)
      (.val (numTypeV t₁) :: .val (numTypeV t₂) :: ws) ρ' :=
  matchArgs_cons (matchArg_subVar20 (by simp) h₁)
    (matchArgs_cons (matchArg_subVar20 (by simp [Equiv.Execution.findVal?_bindVal_lit hX₁, hX])
      h₂) hr)

set_option maxRecDepth 100000 in
theorem argSubOk_inn_bind10 (i : IntType) (Y : IL.Id) (w : Value) :
    argSubOk (simEnv10 B) (VarEnv.empty.bindVal Y w) innPat10' (numTypeV (.int i)) = true := by
  cases i <;> rfl

set_option maxRecDepth 100000 in
theorem argSubOk_fnn_bind10 (f : FloatType) (Y : IL.Id) (w : Value) :
    argSubOk (simEnv10 B) (VarEnv.empty.bindVal Y w) fnnPat10 (numTypeV (.float f)) = true := by
  cases f <;> rfl

/-- The `TRUNC sx` clause fires. -/
theorem hitTrunc10 (hB : FloatB P B) (f : FloatType) (i : IntType) (s : Signedness)
    (x : BitVec f.width) {q : List Param} {cs : List Clause} {T : Typ} :
    TryClauses (simEnv10 B) (.defD q [.expA fnnPat10, .expA innPat10',
        .expA (.caseE "TRUNC" (.varE "sx")), .expA (.varE "fN")]
      (.callE "list_" [.typA T, .expA (.callE "trunc__" [.expA (.callE "size" [.expA fnnPat10]),
        .expA (.callE "size" [.expA innPat10']), .expA (.varE "sx"), .expA (.varE "fN")])]) [] ::
        cs)
      (cvtArgs10 (.trunc f i s) x)
      (.list (((convRes P (.trunc f i s) x).map fun z => Sim.numV ⟨.int i, z⟩).toList)) := by
  have hc : floatCall P "trunc__" [.val (natV f.width), .val (natV i.width), .val (sxV s),
      .val (numV ⟨.float f, x⟩)] =
      some (.opt ((convRes P (.trunc f i s) x).map fun z => Sim.numV ⟨.int i, z⟩)) := by
    have hs : sxV s = Sim.sxV s := by cases s <;> rfl
    rw [hs]; exact Sim.Floats.floatCall_trunc P f i s x
  exact tryClauses_hit (matchArgs_kinds10 (by decide) (by decide) (argSubOk_fnn_float10 f)
      (argSubOk_inn_bind10 i _ _) (matchArgs_opSx10 (by simp) (by simp))) premsHold_nil
    (evalExp_listOpt10 rfl (callDef_floatPrim10 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_size10 (t := .float f) rfl (by simp) (evalArgs_size10 (t := .int i) rfl (by simp)
        (evalArgs_var10 (by simp) (evalArgs_var10 (by simp) Equiv.evalArgs_nil)))) hc))

set_option maxRecDepth 100000 in
theorem applies_cvt_trunc10 (hB : FloatB P B) (f : FloatType) (i : IntType) (s : Signedness)
    (x : BitVec f.width) :
    Applies (simEnv10 B) "cvtop__" (cvtArgs10 (.trunc f i s) x)
      (.list (((convRes P (.trunc f i s) x).map fun z => Sim.numV ⟨.int i, z⟩).toList)) := by
  refine ⟨_, _, _, findDef_cvtop10, Or.inl ?_⟩
  cases f <;> cases i <;> (skipCvt10; exact hitTrunc10 hB _ _ s x)

/-- The `CONVERT sx` clause fires. -/
theorem hitConvert10 (hB : FloatB P B) (i : IntType) (f : FloatType) (s : Signedness)
    (x : BitVec i.width) {q : List Param} {cs : List Clause} :
    TryClauses (simEnv10 B) (.defD q [.expA innPat10', .expA fnnPat10,
        .expA (.caseE "CONVERT" (.varE "sx")), .expA (.varE "iN")]
      (.listE [.callE "convert__" [.expA (.callE "size" [.expA innPat10']),
        .expA (.callE "size" [.expA fnnPat10]), .expA (.varE "sx"), .expA (.varE "iN")]]) [] :: cs)
      (cvtArgs10 (.convert i f s) x) (.list [Sim.numV ⟨.float f, convertInt i f s x⟩]) := by
  have hr : convRes P (.convert i f s) x = some (convertInt i f s x) :=
    (Sim.Floats.convRes_det (op := .convert i f s) (Sim.Floats.det_of nofun nofun) x).trans rfl
  have hc : floatCall P "convert__" [.val (natV i.width), .val (natV f.width), .val (sxV s),
      .val (Equiv.Execution.pctV x.toNat)] = some (Sim.numV ⟨.float f, convertInt i f s x⟩) := by
    have hs : sxV s = Sim.sxV s := by cases s <;> rfl
    rw [hs, Sim.Floats.floatCall_convert, hr]
    rfl
  exact tryClauses_hit (matchArgs_kinds10 (by decide) (by decide) (argSubOk_inn_int10 i)
      (argSubOk_fnn_bind10 f _ _) (matchArgs_opSx10 (by simp) (by simp))) premsHold_nil
    (evalExp_list1Call (callDef_floatPrim10 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_size10 (t := .int i) rfl (by simp) (evalArgs_size10 (t := .float f) rfl (by simp)
        (evalArgs_var10 (by simp) (evalArgs_var10 (by simp; rfl) Equiv.evalArgs_nil)))) hc))

set_option maxRecDepth 100000 in
theorem applies_cvt_convert10 (hB : FloatB P B) (i : IntType) (f : FloatType) (s : Signedness)
    (x : BitVec i.width) :
    Applies (simEnv10 B) "cvtop__" (cvtArgs10 (.convert i f s) x)
      (.list [Sim.numV ⟨.float f, convertInt i f s x⟩]) := by
  refine ⟨_, _, _, findDef_cvtop10, Or.inl ?_⟩
  cases f <;> cases i <;> (skipCvt10; exact hitConvert10 hB _ _ s x)

set_option maxRecDepth 100000 in
theorem applies_cvt_promote10 (hB : FloatB P B) (x : BitVec 32) :
    Applies (simEnv10 B) "cvtop__" (cvtArgs10 .promote x)
      (.list ((bitsWhere 64 (fun z => convertP P .promote x (.ok z))).map
        fun z => Sim.numV ⟨.float .f64, z⟩)) := by
  refine ⟨_, _, _, findDef_cvtop10, Or.inl ?_⟩
  skipCvt10
  exact tryClauses_hit (matchArgs_cons matchArg_lit10 (matchArgs_cons matchArg_lit10
    (matchArgs_opNil10 (by simp)))) premsHold_nil
    (evalExp_callE_iff.2 (callDef_floatPrim10 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_lit10 (evalArgs_lit10 (evalArgs_var10 (by simp; rfl) Equiv.evalArgs_nil)))
      (Sim.Floats.floatCall_promote P x)))

set_option maxRecDepth 100000 in
theorem applies_cvt_demote10 (hB : FloatB P B) (x : BitVec 64) :
    Applies (simEnv10 B) "cvtop__" (cvtArgs10 .demote x)
      (.list ((bitsWhere 32 (fun z => convertP P .demote x (.ok z))).map
        fun z => Sim.numV ⟨.float .f32, z⟩)) := by
  refine ⟨_, _, _, findDef_cvtop10, Or.inl ?_⟩
  skipCvt10
  exact tryClauses_hit (matchArgs_cons matchArg_lit10 (matchArgs_cons matchArg_lit10
    (matchArgs_opNil10 (by simp)))) premsHold_nil
    (evalExp_callE_iff.2 (callDef_floatPrim10 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_lit10 (evalArgs_lit10 (evalArgs_var10 (by simp; rfl) Equiv.evalArgs_nil)))
      (Sim.Floats.floatCall_demote P x)))

/-- The `REINTERPRET` clause from `Inn` to `Fnn` fires. -/
theorem hitReinterpF10 (i : IntType) (f : FloatType)
    (hw : (NumType.int i).width = (NumType.float f).width) {a v : Value} {q : List Param}
    {cs : List Clause} (hc : floatCall P "reinterpret__"
      [.val (numTypeV (.int i)), .val (numTypeV (.float f)), .val a] = some v) (hB : FloatB P B) :
    TryClauses (simEnv10 B) (.defD q [.expA innPat10', .expA fnnPat10,
        .expA (.caseE "REINTERPRET" (.tupE [])), .expA (.varE "iN")]
      (.listE [.callE "reinterpret__" [.expA innPat10', .expA fnnPat10, .expA (.varE "iN")]])
      [.ifPr (.cmpE .eqOp .boolT (.callE "size" [.expA innPat10'])
        (.callE "size" [.expA fnnPat10]))] :: cs)
      [.val (numTypeV (.int i)), .val (numTypeV (.float f)),
        .val (Equiv.Execution.caseNilV "REINTERPRET"),
        .val a] (.list [v]) :=
  tryClauses_hit (matchArgs_kinds10 (by decide) (by decide) (argSubOk_inn_int10 i)
      (argSubOk_fnn_bind10 f _ _) (matchArgs_opNil10 (by simp)))
    (premsHold_sameSize10 (t₁ := .int i) (t₂ := .float f) (by simp) (by simp) rfl hw)
    (evalExp_list1Call (callDef_floatPrim10 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_kind10 (by simp) (evalArgs_kind10 (by simp)
        (evalArgs_var10 (by simp) Equiv.evalArgs_nil))) hc))

/-- The `REINTERPRET` clause from `Fnn` to `Inn` fires. -/
theorem hitReinterpI10 (f : FloatType) (i : IntType)
    (hw : (NumType.int i).width = (NumType.float f).width) {a v : Value} {q : List Param}
    {cs : List Clause} (hc : floatCall P "reinterpret__"
      [.val (numTypeV (.float f)), .val (numTypeV (.int i)), .val a] = some v) (hB : FloatB P B) :
    TryClauses (simEnv10 B) (.defD q [.expA fnnPat10, .expA innPat10',
        .expA (.caseE "REINTERPRET" (.tupE [])), .expA (.varE "fN")]
      (.listE [.callE "reinterpret__" [.expA fnnPat10, .expA innPat10', .expA (.varE "fN")]])
      [.ifPr (.cmpE .eqOp .boolT (.callE "size" [.expA innPat10'])
        (.callE "size" [.expA fnnPat10]))] :: cs)
      [.val (numTypeV (.float f)), .val (numTypeV (.int i)),
        .val (Equiv.Execution.caseNilV "REINTERPRET"),
        .val a] (.list [v]) :=
  tryClauses_hit (matchArgs_kinds10 (by decide) (by decide) (argSubOk_fnn_float10 f)
      (argSubOk_inn_bind10 i _ _) (matchArgs_opNil10 (by simp)))
    (premsHold_sameSize10 (t₁ := .int i) (t₂ := .float f) (by simp) (by simp) rfl hw)
    (evalExp_list1Call (callDef_floatPrim10 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_kind10 (by simp) (evalArgs_kind10 (by simp)
        (evalArgs_var10 (by simp) Equiv.evalArgs_nil))) hc))

/-- `REINTERPRET`, at each of the four pairs. -/
theorem floatCall_reinterp10 (op : ConvertOp) (hop : Sim.Floats.reinterpOp? op.source op.target =
    some op) (hd : Sim.Floats.Det op) {x : BitVec op.source.width} {w : BitVec op.target.width}
    (hw : convert op x = .ok w) :
    floatCall P "reinterpret__" [.val (numTypeV op.source), .val (numTypeV op.target),
      .val (numV ⟨op.source, x⟩)] = some (Sim.numV ⟨op.target, w⟩) := by
  rw [numV_eq_sim]
  exact Sim.Floats.floatCall_reinterpret_eq hop hd hw

set_option maxRecDepth 100000 in
theorem applies_cvt_reinterpF10 (hB : FloatB P B) (i : IntType) (x : BitVec i.width) :
    ∃ L, Applies (simEnv10 B) "cvtop__" (cvtArgs10 (.reinterpretFloat i) x) (.list L) ∧
      CvtOk P (.reinterpretFloat i) x L := by
  cases i
  · refine ⟨_, ⟨_, _, _, findDef_cvtop10, Or.inl ?_⟩,
      Sim.Floats.cvtOk_single (op := .reinterpretFloat .i32) (Sim.Floats.det_of nofun nofun)
        (w := x) rfl⟩
    skipCvt10
    exact hitReinterpF10 .i32 .f32 rfl
      (floatCall_reinterp10 (.reinterpretFloat .i32) rfl (Sim.Floats.det_of nofun nofun) rfl) hB
  · refine ⟨_, ⟨_, _, _, findDef_cvtop10, Or.inl ?_⟩,
      Sim.Floats.cvtOk_single (op := .reinterpretFloat .i64) (Sim.Floats.det_of nofun nofun)
        (w := x) rfl⟩
    skipCvt10
    exact hitReinterpF10 .i64 .f64 rfl
      (floatCall_reinterp10 (.reinterpretFloat .i64) rfl (Sim.Floats.det_of nofun nofun) rfl) hB

set_option maxRecDepth 100000 in
theorem applies_cvt_reinterpI10 (hB : FloatB P B) (f : FloatType) (x : BitVec f.width) :
    ∃ L, Applies (simEnv10 B) "cvtop__" (cvtArgs10 (.reinterpretInt f) x) (.list L) ∧
      CvtOk P (.reinterpretInt f) x L := by
  cases f
  · refine ⟨_, ⟨_, _, _, findDef_cvtop10, Or.inl ?_⟩,
      Sim.Floats.cvtOk_single (op := .reinterpretInt .f32) (Sim.Floats.det_of nofun nofun)
        (w := x) rfl⟩
    skipCvt10
    exact hitReinterpI10 .f32 .i32 rfl
      (floatCall_reinterp10 (.reinterpretInt .f32) rfl (Sim.Floats.det_of nofun nofun) rfl) hB
  · refine ⟨_, ⟨_, _, _, findDef_cvtop10, Or.inl ?_⟩,
      Sim.Floats.cvtOk_single (op := .reinterpretInt .f64) (Sim.Floats.det_of nofun nofun)
        (w := x) rfl⟩
    skipCvt10
    exact hitReinterpI10 .f64 .i64 rfl
      (floatCall_reinterp10 (.reinterpretInt .f64) rfl (Sim.Floats.det_of nofun nofun) rfl) hB

/-! ## Agreement -/

/-- **`$cvtop__` at every V1 conversion** returns the list of the profile's results, empty exactly
when the profile traps. -/
theorem applies_cvtop10 (hB : FloatB P B) (op : V1.ConvertOp)
    (x : BitVec op.toCore.source.width) :
    ∃ L, Applies (simEnv10 B) "cvtop__" (cvtArgs10 op x) (.list L) ∧ CvtOk P op.toCore x L := by
  cases op with
  | wrap => exact ⟨_, applies_cvt_wrap10 hB x,
      Sim.Floats.cvtOk_single (op := .wrap) (Sim.Floats.det_of nofun nofun) rfl⟩
  | extend s =>
      cases s
      · exact ⟨_, applies_cvt_extend10 hB .signed x,
          Sim.Floats.cvtOk_single (op := .extend .signed) (Sim.Floats.det_of nofun nofun) rfl⟩
      · exact ⟨_, applies_cvt_extend10 hB .unsigned x,
          Sim.Floats.cvtOk_single (op := .extend .unsigned) (Sim.Floats.det_of nofun nofun) rfl⟩
  | trunc f i s => exact ⟨_, applies_cvt_trunc10 hB f i s x,
      Sim.Floats.agree_opt (op := .trunc f i s) (Sim.Floats.det_of nofun nofun) x⟩
  | convert i f s => exact ⟨_, applies_cvt_convert10 hB i f s x,
      Sim.Floats.cvtOk_single (op := .convert i f s) (Sim.Floats.det_of nofun nofun) rfl⟩
  | demote => exact ⟨_, applies_cvt_demote10 hB x,
      Sim.Floats.agree_list (op := .demote) (.inr rfl) (w := (asF64 x).toF32.bits.toBitVec) rfl⟩
  | promote => exact ⟨_, applies_cvt_promote10 hB x,
      Sim.Floats.agree_list (op := .promote) (.inl rfl) (w := (asF32 x).toF64.bits.toBitVec) rfl⟩
  | reinterpretInt f => exact applies_cvt_reinterpI10 hB f x
  | reinterpretFloat i => exact applies_cvt_reinterpF10 hB i x

end Silmaril.Wasm.SpecTec.Sim10.Whole
