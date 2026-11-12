module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.Backward

/-!
# Family V: `Backward.pure i` for the vector rules

Each lemma has exactly the type of the `Backward.pure i` obligation at its rule index (without the
`Typed` hypothesis, which these rules do not need), under the rule provenance `HasVectorRules`, the
syntactic decoders `VecDecode` and the operator agreement `VecAgree`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Vec

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.ExecVector (HasVectorRules vconstV)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV trapV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core

/-- `c = $f(args)`, inverted to the call's denotation. -/
theorem inv_eq_call_app {env : Env} {ρ : VarEnv} {c : IL.Id} {cv : Value} {f : IL.Id}
    {args : List Arg} {ws : List ArgV} (hc : ρ.findVal? c = some cv)
    (hd : ρ.findDef? f = none) (hx : EvalArgs env ρ args ws)
    (h : EvalExp env ρ (.cmpE .eqOp .boolT (.varE c) (.callE f args)) (.bool true)) :
    Applies env f ws cv := by
  obtain ⟨v₁, v₂, h₁, h₂, hcmp⟩ := evalExp_cmpE_iff.1 h
  have e₁ : v₁ = cv := Option.some.inj ((evalExp_varE_iff.1 h₁).symm.trans hc)
  have e₃ : v₁ = v₂ := by simpa [cmpValues] using hcmp
  exact (e₁ ▸ e₃ ▸ inv_call hd hx h₂ : Applies env f ws cv)

/-- `$f(args) = c`, inverted to the call's denotation. -/
theorem inv_call_eq_app {env : Env} {ρ : VarEnv} {c : IL.Id} {cv : Value} {f : IL.Id}
    {args : List Arg} {ws : List ArgV} (hc : ρ.findVal? c = some cv)
    (hd : ρ.findDef? f = none) (hx : EvalArgs env ρ args ws)
    (h : EvalExp env ρ (.cmpE .eqOp .boolT (.callE f args) (.varE c)) (.bool true)) :
    Applies env f ws cv := by
  obtain ⟨v₁, v₂, h₁, h₂, hcmp⟩ := evalExp_cmpE_iff.1 h
  have e₁ : v₂ = cv := Option.some.inj ((evalExp_varE_iff.1 h₂).symm.trans hc)
  have e₃ : v₁ = v₂ := by simpa [cmpValues] using hcmp
  exact (e₁ ▸ e₃ ▸ inv_call hd hx h₁ : Applies env f ws cv)

section

variable {H : Type} {env : Env} {P : Profile} {host : HostSemantics H}
  (V : HasVectorRules env) (D : VecDecode) (A : VecAgree env P)
  {s : Store H} {f : Frame} {is : List Admin} {w : Value}

include V D A

/-- `Backward.pure 54` (`Step_pure/vvunop`). -/
theorem bwd_vvunop (hf : Fires env "Step_pure" 54 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vvunop hf
  obtain ⟨c₁, y, z, hcode, rfl, f₁, hy, hz⟩ := inst_c1 he
  obtain ⟨op, rfl, fop⟩ := inv_vvop hy
  obtain ⟨c, rfl, fc⟩ := inv_vconst hz
  obtain ⟨b, i, rfl, rfl, hi⟩ := decode_c1 D (by simp [vecTags]) hcode
  obtain ⟨o, rfl, hx⟩ := vecInstrV?_vvunop hi
  obtain ⟨-, rfl⟩ := tuple2_inj hx
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.caseE "V128" (.tupE [])),
      .expA (.varE "vvunop"), .expA (.varE "c_1")]
      [.val vecTypeV, .val (vvunopV o), .val (vecV b)] :=
    evalArgs_v128 (evalArgs_var fop (evalArgs_var f₁ Equiv.evalArgs_nil))
  obtain rfl := List.mem_singleton.1 (inv_mem_call fc rfl hargs (A.vvunop o b) hp)
  exact ⟨[vconst (vvunop o b)], rfl, .vector (.vecUnOp o b)⟩

/-- `Backward.pure 55` (`Step_pure/vvbinop`). -/
theorem bwd_vvbinop (hf : Fires env "Step_pure" 55 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vvbinop hf
  obtain ⟨c₁, c₂, y, z, hcode, rfl, f₁, f₂, hy, hz⟩ := inst_c2 he
  obtain ⟨op, rfl, fop⟩ := inv_vvop hy
  obtain ⟨c, rfl, fc⟩ := inv_vconst hz
  obtain ⟨b₁, b₂, i, rfl, rfl, rfl, hi⟩ := decode_c2 D (by simp [vecTags]) hcode
  obtain ⟨o, rfl, hx⟩ := vecInstrV?_vvbinop hi
  obtain ⟨-, rfl⟩ := tuple2_inj hx
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.caseE "V128" (.tupE [])),
      .expA (.varE "vvbinop"), .expA (.varE "c_1"), .expA (.varE "c_2")]
      [.val vecTypeV, .val (vvbinopV o), .val (vecV b₁), .val (vecV b₂)] :=
    evalArgs_v128 (evalArgs_var fop (evalArgs_var f₁ (evalArgs_var f₂ Equiv.evalArgs_nil)))
  obtain rfl := List.mem_singleton.1 (inv_mem_call fc rfl hargs (A.vvbinop o b₁ b₂) hp)
  exact ⟨[vconst (vvbinop o b₁ b₂)], rfl, .vector (.vecBinOp o b₁ b₂)⟩

/-- `Backward.pure 56` (`Step_pure/vvternop`). -/
theorem bwd_vvternop (hf : Fires env "Step_pure" 56 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vvternop hf
  obtain ⟨c₁, c₂, c₃, y, z, hcode, rfl, f₁, f₂, f₃, hy, hz⟩ := inst_c3 he
  obtain ⟨op, rfl, fop⟩ := inv_vvop hy
  obtain ⟨c, rfl, fc⟩ := inv_vconst hz
  obtain ⟨b₁, b₂, b₃, i, rfl, rfl, rfl, rfl, hi⟩ := decode_c3 D (by simp [vecTags]) hcode
  obtain ⟨o, rfl, hx⟩ := vecInstrV?_vvternop hi
  obtain ⟨-, rfl⟩ := tuple2_inj hx
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.caseE "V128" (.tupE [])),
      .expA (.varE "vvternop"), .expA (.varE "c_1"), .expA (.varE "c_2"), .expA (.varE "c_3")]
      [.val vecTypeV, .val (vvternopV o), .val (vecV b₁), .val (vecV b₂), .val (vecV b₃)] :=
    evalArgs_v128 (evalArgs_var fop (evalArgs_var f₁ (evalArgs_var f₂ (evalArgs_var f₃
      Equiv.evalArgs_nil))))
  obtain rfl := List.mem_singleton.1 (inv_mem_call fc rfl hargs (A.vvternop o b₁ b₂ b₃) hp)
  exact ⟨[vconst (vvternop o b₁ b₂ b₃)], rfl, .vector (.vecTernOp o b₁ b₂ b₃)⟩

/-- `Backward.pure 58` (`Step_pure/vunop-val`): an integer or a float `VUNOP`. -/
theorem bwd_vunopVal (hf : Fires env "Step_pure" 58 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vunopVal hf
  obtain ⟨c₁, y, z, hcode, rfl, f₁, hy, hz⟩ := inst_c1 he
  obtain ⟨sh, op, rfl, fsh, fop⟩ := inv_op2 hy
  obtain ⟨c, rfl, fc⟩ := inv_vconst hz
  obtain ⟨b, i, rfl, rfl, hi⟩ := decode_c1 D (by simp [vecTags]) hcode
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.varE "sh"),
      .expA (.varE "vunop"), .expA (.varE "c_1")] [.val sh, .val op, .val (vecV b)] :=
    evalArgs_var fsh (evalArgs_var fop (evalArgs_var f₁ Equiv.evalArgs_nil))
  rcases vecInstrV?_vunop hi with ⟨s', o, rfl, hx⟩ | ⟨s', o, rfl, hx⟩
  · obtain ⟨rfl, rfl⟩ := tuple2_inj hx
    obtain rfl := List.mem_singleton.1 (inv_mem_call fc rfl hargs (A.intUnOp s' o b) hp)
    exact ⟨[vconst (vecIntUnOp s' o b)], rfl, .vector (.vecIntUnOp s' o b)⟩
  · obtain ⟨rfl, rfl⟩ := tuple2_inj hx
    obtain ⟨L, ha, hL⟩ := A.floatUnOp s' o b
    obtain ⟨r, hrel, rfl⟩ := (hL c).1 (inv_mem_call fc rfl hargs ha hp)
    exact ⟨[vconst r], rfl, .vector (.vecFloatUnOp hrel)⟩

/-- `Backward.pure 60` (`Step_pure/vbinop-val`): an integer or a float `VBINOP`. -/
theorem bwd_vbinopVal (hf : Fires env "Step_pure" 60 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vbinopVal hf
  obtain ⟨c₁, c₂, y, z, hcode, rfl, f₁, f₂, hy, hz⟩ := inst_c2 he
  obtain ⟨sh, op, rfl, fsh, fop⟩ := inv_op2 hy
  obtain ⟨c, rfl, fc⟩ := inv_vconst hz
  obtain ⟨b₁, b₂, i, rfl, rfl, rfl, hi⟩ := decode_c2 D (by simp [vecTags]) hcode
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.varE "sh"),
      .expA (.varE "vbinop"), .expA (.varE "c_1"), .expA (.varE "c_2")]
      [.val sh, .val op, .val (vecV b₁), .val (vecV b₂)] :=
    evalArgs_var fsh (evalArgs_var fop (evalArgs_var f₁ (evalArgs_var f₂ Equiv.evalArgs_nil)))
  rcases vecInstrV?_vbinop hi with ⟨s', o, rfl, hx⟩ | ⟨s', o, rfl, hx⟩
  · obtain ⟨rfl, rfl⟩ := tuple2_inj hx
    obtain rfl := List.mem_singleton.1 (inv_mem_call fc rfl hargs (A.intBinOp s' o b₁ b₂) hp)
    exact ⟨[vconst (vecIntBinOp P s' o b₁ b₂)], rfl, .vector (.vecIntBinOp s' o b₁ b₂)⟩
  · obtain ⟨rfl, rfl⟩ := tuple2_inj hx
    obtain ⟨L, ha, hL⟩ := A.floatBinOp s' o b₁ b₂
    obtain ⟨r, hrel, rfl⟩ := (hL c).1 (inv_mem_call fc rfl hargs ha hp)
    exact ⟨[vconst r], rfl, .vector (.vecFloatBinOp hrel)⟩

/-- `Backward.pure 62` (`Step_pure/vternop-val`): an integer or a float `VTERNOP`. -/
theorem bwd_vternopVal (hf : Fires env "Step_pure" 62 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vternopVal hf
  obtain ⟨c₁, c₂, c₃, y, z, hcode, rfl, f₁, f₂, f₃, hy, hz⟩ := inst_c3 he
  obtain ⟨sh, op, rfl, fsh, fop⟩ := inv_op2 hy
  obtain ⟨c, rfl, fc⟩ := inv_vconst hz
  obtain ⟨b₁, b₂, b₃, i, rfl, rfl, rfl, rfl, hi⟩ := decode_c3 D (by simp [vecTags]) hcode
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.varE "sh"),
      .expA (.varE "vternop"), .expA (.varE "c_1"), .expA (.varE "c_2"), .expA (.varE "c_3")]
      [.val sh, .val op, .val (vecV b₁), .val (vecV b₂), .val (vecV b₃)] :=
    evalArgs_var fsh (evalArgs_var fop (evalArgs_var f₁ (evalArgs_var f₂ (evalArgs_var f₃
      Equiv.evalArgs_nil))))
  rcases vecInstrV?_vternop hi with ⟨s', o, rfl, hx⟩ | ⟨s', o, rfl, hx⟩
  · obtain ⟨rfl, rfl⟩ := tuple2_inj hx
    obtain rfl := List.mem_singleton.1 (inv_mem_call fc rfl hargs (A.intTernOp s' o b₁ b₂ b₃) hp)
    exact ⟨_, rfl, .vector (.vecIntTernOp s' o b₁ b₂ b₃)⟩
  · obtain ⟨rfl, rfl⟩ := tuple2_inj hx
    obtain ⟨L, ha, hL⟩ := A.floatTernOp s' o b₁ b₂ b₃
    obtain ⟨r, hrel, rfl⟩ := (hL c).1 (inv_mem_call fc rfl hargs ha hp)
    exact ⟨[vconst r], rfl, .vector (.vecFloatTernOp hrel)⟩

/-- `Backward.pure 65` (`Step_pure/vrelop`): an integer or a float `VRELOP`. -/
theorem bwd_vrelop (hf : Fires env "Step_pure" 65 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vrelop hf
  obtain ⟨c₁, c₂, y, z, hcode, rfl, f₁, f₂, hy, hz⟩ := inst_c2 he
  obtain ⟨sh, op, rfl, fsh, fop⟩ := inv_op2 hy
  obtain ⟨c, rfl, fc⟩ := inv_vconst hz
  obtain ⟨b₁, b₂, i, rfl, rfl, rfl, hi⟩ := decode_c2 D (by simp [vecTags]) hcode
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.varE "sh"),
      .expA (.varE "vrelop"), .expA (.varE "c_1"), .expA (.varE "c_2")]
      [.val sh, .val op, .val (vecV b₁), .val (vecV b₂)] :=
    evalArgs_var fsh (evalArgs_var fop (evalArgs_var f₁ (evalArgs_var f₂ Equiv.evalArgs_nil)))
  rcases vecInstrV?_vrelop hi with ⟨s', o, rfl, hx⟩ | ⟨s', o, rfl, hx⟩
  · obtain ⟨rfl, rfl⟩ := tuple2_inj hx
    obtain rfl := inv_eq_call fc rfl hargs (A.intRelOp s' o b₁ b₂) hp
    exact ⟨_, rfl, .vector (.vecIntRelOp s' o b₁ b₂)⟩
  · obtain ⟨rfl, rfl⟩ := tuple2_inj hx
    obtain rfl := inv_eq_call fc rfl hargs (A.floatRelOp s' o b₁ b₂) hp
    exact ⟨_, rfl, .vector (.vecFloatRelOp s' o b₁ b₂)⟩

/-- `Backward.pure 68` (`Step_pure/vswizzlop`): `swizzle` or `relaxed_swizzle`. -/
theorem bwd_vswizzlop (hf : Fires env "Step_pure" 68 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vswizzlop hf
  obtain ⟨c₁, c₂, y, z, hcode, rfl, f₁, f₂, hy, hz⟩ := inst_c2 he
  obtain ⟨sh, op, rfl, fsh, fop⟩ := inv_op2 hy
  obtain ⟨c, rfl, fc⟩ := inv_vconst hz
  obtain ⟨b₁, b₂, i, rfl, rfl, rfl, hi⟩ := decode_c2 D (by simp [vecTags]) hcode
  obtain ⟨o, rfl, hx⟩ := vecInstrV?_vswizzlop hi
  obtain ⟨rfl, rfl⟩ := tuple2_inj hx
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.varE "sh"),
      .expA (.varE "swizzlop"), .expA (.varE "c_1"), .expA (.varE "c_2")]
      [.val bshapeV, .val (vSwizzleOpV o), .val (vecV b₁), .val (vecV b₂)] :=
    evalArgs_var fsh (evalArgs_var fop (evalArgs_var f₁ (evalArgs_var f₂ Equiv.evalArgs_nil)))
  cases o with
  | swizzle =>
      obtain rfl := inv_eq_call fc rfl hargs (A.swizzle b₁ b₂) hp
      exact ⟨_, rfl, .vector (.vecSwizzle b₁ b₂)⟩
  | relaxedSwizzle =>
      obtain rfl := inv_eq_call fc rfl hargs (A.relaxedSwizzle b₁ b₂) hp
      exact ⟨_, rfl, .vector (.vecRelaxedSwizzle b₁ b₂)⟩

/-- `Backward.pure 74` (`Step_pure/vextunop`). -/
theorem bwd_vextunop (hf : Fires env "Step_pure" 74 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vextunop hf
  obtain ⟨c₁, y, z, hcode, rfl, f₁, hy, hz⟩ := inst_c1 he
  obtain ⟨sh₂, sh₁, op, rfl, fsh₂, fsh₁, fop⟩ := inv_op3 hy
  obtain ⟨c, rfl, fc⟩ := inv_vconst hz
  obtain ⟨b, i, rfl, rfl, hi⟩ := decode_c1 D (by simp [vecTags]) hcode
  obtain ⟨s', t', o, rfl, hx⟩ := vecInstrV?_vextunop hi
  obtain ⟨rfl, rfl, rfl⟩ := tuple3_inj hx
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.varE "sh_1"),
      .expA (.varE "sh_2"), .expA (.varE "vextunop"), .expA (.varE "c_1")]
      [.val (ishapeV s'), .val (ishapeV t'), .val (vExtUnOpV o), .val (vecV b)] :=
    evalArgs_var fsh₁ (evalArgs_var fsh₂ (evalArgs_var fop (evalArgs_var f₁ Equiv.evalArgs_nil)))
  obtain ⟨r, hrel, rfl⟩ := (A.extUnOp s' t' o b c).1 (inv_call_eq_app fc rfl hargs hp)
  exact ⟨[vconst r], rfl, .vector (.vecExtUnOp hrel)⟩

/-- `Backward.pure 75` (`Step_pure/vextbinop`). -/
theorem bwd_vextbinop (hf : Fires env "Step_pure" 75 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vextbinop hf
  obtain ⟨c₁, c₂, y, z, hcode, rfl, f₁, f₂, hy, hz⟩ := inst_c2 he
  obtain ⟨sh₂, sh₁, op, rfl, fsh₂, fsh₁, fop⟩ := inv_op3 hy
  obtain ⟨c, rfl, fc⟩ := inv_vconst hz
  obtain ⟨b₁, b₂, i, rfl, rfl, rfl, hi⟩ := decode_c2 D (by simp [vecTags]) hcode
  obtain ⟨s', t', o, rfl, hx⟩ := vecInstrV?_vextbinop hi
  obtain ⟨rfl, rfl, rfl⟩ := tuple3_inj hx
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.varE "sh_1"),
      .expA (.varE "sh_2"), .expA (.varE "vextbinop"), .expA (.varE "c_1"), .expA (.varE "c_2")]
      [.val (ishapeV s'), .val (ishapeV t'), .val (vExtBinOpV o), .val (vecV b₁),
        .val (vecV b₂)] :=
    evalArgs_var fsh₁ (evalArgs_var fsh₂ (evalArgs_var fop (evalArgs_var f₁ (evalArgs_var f₂
      Equiv.evalArgs_nil))))
  obtain ⟨r, hrel, rfl⟩ := (A.extBinOp s' t' o b₁ b₂ c).1 (inv_call_eq_app fc rfl hargs hp)
  exact ⟨[vconst r], rfl, .vector (.vecExtBinOp hrel)⟩

/-- `Backward.pure 76` (`Step_pure/vextternop`). -/
theorem bwd_vextternop (hf : Fires env "Step_pure" 76 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vextternop hf
  obtain ⟨c₁, c₂, c₃, y, z, hcode, rfl, f₁, f₂, f₃, hy, hz⟩ := inst_c3 he
  obtain ⟨sh₂, sh₁, op, rfl, fsh₂, fsh₁, fop⟩ := inv_op3 hy
  obtain ⟨c, rfl, fc⟩ := inv_vconst hz
  obtain ⟨b₁, b₂, b₃, i, rfl, rfl, rfl, rfl, hi⟩ := decode_c3 D (by simp [vecTags]) hcode
  obtain ⟨s', t', o, rfl, hx⟩ := vecInstrV?_vextternop hi
  obtain ⟨rfl, rfl, rfl⟩ := tuple3_inj hx
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.varE "sh_1"),
      .expA (.varE "sh_2"), .expA (.varE "vextternop"), .expA (.varE "c_1"), .expA (.varE "c_2"),
      .expA (.varE "c_3")] [.val (ishapeV s'), .val (ishapeV t'), .val (vExtTernOpV o),
        .val (vecV b₁), .val (vecV b₂), .val (vecV b₃)] :=
    evalArgs_var fsh₁ (evalArgs_var fsh₂ (evalArgs_var fop (evalArgs_var f₁ (evalArgs_var f₂
      (evalArgs_var f₃ Equiv.evalArgs_nil)))))
  obtain ⟨r, hrel, rfl⟩ := (A.extTernOp s' t' o b₁ b₂ b₃ c).1 (inv_call_eq_app fc rfl hargs hp)
  exact ⟨[vconst r], rfl, .vector (.vecExtTernOp hrel)⟩

/-- `Backward.pure 78` (`Step_pure/vcvtop`). -/
theorem bwd_vcvtop (hf : Fires env "Step_pure" 78 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vcvtop hf
  obtain ⟨c₁, y, z, hcode, rfl, f₁, hy, hz⟩ := inst_c1 he
  obtain ⟨sh₂, sh₁, op, rfl, fsh₂, fsh₁, fop⟩ := inv_op3 hy
  obtain ⟨c, rfl, fc⟩ := inv_vconst hz
  obtain ⟨b, i, rfl, rfl, hi⟩ := decode_c1 D (by simp [vecTags]) hcode
  obtain ⟨s', t', o, rfl, hx⟩ := vecInstrV?_vcvtop hi
  obtain ⟨rfl, rfl, rfl⟩ := tuple3_inj hx
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.varE "sh_1"),
      .expA (.varE "sh_2"), .expA (.varE "vcvtop"), .expA (.varE "c_1")]
      [.val (shapeV s'), .val (shapeV t'), .val (vConvertOpV o), .val (vecV b)] :=
    evalArgs_var fsh₁ (evalArgs_var fsh₂ (evalArgs_var fop (evalArgs_var f₁ Equiv.evalArgs_nil)))
  obtain ⟨r, hrel, rfl⟩ := (A.convert s' t' o b c).1 (inv_eq_call_app fc rfl hargs hp)
  exact ⟨[vconst r], rfl, .vector (.vecConvert hrel)⟩

/-- `Backward.pure 59` (`Step_pure/vunop-trap`): only a float `VUNOP` with no result reaches it;
an integer `$vunop_` has one result. -/
theorem bwd_vunopTrap (hf : Fires env "Step_pure" 59 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vunopTrap hf
  obtain ⟨c₁, y, z, hcode, rfl, f₁, hy, hz⟩ := inst_c1 he
  obtain ⟨sh, op, rfl, fsh, fop⟩ := inv_op2 hy
  obtain rfl := inv_nil hz
  obtain ⟨b, i, rfl, rfl, hi⟩ := decode_c1 D (by simp [vecTags]) hcode
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.varE "sh"),
      .expA (.varE "vunop"), .expA (.varE "c_1")] [.val sh, .val op, .val (vecV b)] :=
    evalArgs_var fsh (evalArgs_var fop (evalArgs_var f₁ Equiv.evalArgs_nil))
  have hnil := inv_call_nil rfl hargs hp
  rcases vecInstrV?_vunop hi with ⟨s', o, rfl, hx⟩ | ⟨s', o, rfl, hx⟩
  · obtain ⟨rfl, rfl⟩ := tuple2_inj hx
    exact absurd (Equiv.ExecNumeric.Applies.unique hnil (A.intUnOp s' o b)) (by simp)
  · obtain ⟨rfl, rfl⟩ := tuple2_inj hx
    obtain ⟨L, ha, hL⟩ := A.floatUnOp s' o b
    have hL0 : Value.list L = .list [] := Equiv.ExecNumeric.Applies.unique ha hnil
    exact ⟨[.trap], rfl, .vector (.vecFloatUnOpTrap fun r hr' =>
      List.not_mem_nil (Value.list.inj hL0 ▸ (hL (vecV r)).2 ⟨r, hr', rfl⟩))⟩

/-- `Backward.pure 61` (`Step_pure/vbinop-trap`): only a float `VBINOP` with no result. -/
theorem bwd_vbinopTrap (hf : Fires env "Step_pure" 61 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vbinopTrap hf
  obtain ⟨c₁, c₂, y, z, hcode, rfl, f₁, f₂, hy, hz⟩ := inst_c2 he
  obtain ⟨sh, op, rfl, fsh, fop⟩ := inv_op2 hy
  obtain rfl := inv_nil hz
  obtain ⟨b₁, b₂, i, rfl, rfl, rfl, hi⟩ := decode_c2 D (by simp [vecTags]) hcode
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.varE "sh"),
      .expA (.varE "vbinop"), .expA (.varE "c_1"), .expA (.varE "c_2")]
      [.val sh, .val op, .val (vecV b₁), .val (vecV b₂)] :=
    evalArgs_var fsh (evalArgs_var fop (evalArgs_var f₁ (evalArgs_var f₂ Equiv.evalArgs_nil)))
  have hnil := inv_call_nil rfl hargs hp
  rcases vecInstrV?_vbinop hi with ⟨s', o, rfl, hx⟩ | ⟨s', o, rfl, hx⟩
  · obtain ⟨rfl, rfl⟩ := tuple2_inj hx
    exact absurd (Equiv.ExecNumeric.Applies.unique hnil (A.intBinOp s' o b₁ b₂)) (by simp)
  · obtain ⟨rfl, rfl⟩ := tuple2_inj hx
    obtain ⟨L, ha, hL⟩ := A.floatBinOp s' o b₁ b₂
    have hL0 : Value.list L = .list [] := Equiv.ExecNumeric.Applies.unique ha hnil
    exact ⟨[.trap], rfl, .vector (.vecFloatBinOpTrap fun r hr' =>
      List.not_mem_nil (Value.list.inj hL0 ▸ (hL (vecV r)).2 ⟨r, hr', rfl⟩))⟩

/-- `Backward.pure 63` (`Step_pure/vternop-trap`): only a float `VTERNOP` with no result. -/
theorem bwd_vternopTrap (hf : Fires env "Step_pure" 63 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vternopTrap hf
  obtain ⟨c₁, c₂, c₃, y, z, hcode, rfl, f₁, f₂, f₃, hy, hz⟩ := inst_c3 he
  obtain ⟨sh, op, rfl, fsh, fop⟩ := inv_op2 hy
  obtain rfl := inv_nil hz
  obtain ⟨b₁, b₂, b₃, i, rfl, rfl, rfl, rfl, hi⟩ := decode_c3 D (by simp [vecTags]) hcode
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.varE "sh"),
      .expA (.varE "vternop"), .expA (.varE "c_1"), .expA (.varE "c_2"), .expA (.varE "c_3")]
      [.val sh, .val op, .val (vecV b₁), .val (vecV b₂), .val (vecV b₃)] :=
    evalArgs_var fsh (evalArgs_var fop (evalArgs_var f₁ (evalArgs_var f₂ (evalArgs_var f₃
      Equiv.evalArgs_nil))))
  have hnil := inv_call_nil rfl hargs hp
  rcases vecInstrV?_vternop hi with ⟨s', o, rfl, hx⟩ | ⟨s', o, rfl, hx⟩
  · obtain ⟨rfl, rfl⟩ := tuple2_inj hx
    exact absurd (Equiv.ExecNumeric.Applies.unique hnil (A.intTernOp s' o b₁ b₂ b₃)) (by simp)
  · obtain ⟨rfl, rfl⟩ := tuple2_inj hx
    obtain ⟨L, ha, hL⟩ := A.floatTernOp s' o b₁ b₂ b₃
    have hL0 : Value.list L = .list [] := Equiv.ExecNumeric.Applies.unique ha hnil
    exact ⟨[.trap], rfl, .vector (.vecFloatTernOpTrap fun r hr' =>
      List.not_mem_nil (Value.list.inj hL0 ▸ (hL (vecV r)).2 ⟨r, hr', rfl⟩))⟩

/-- `Backward.pure 57` (`Step_pure/vvtestop`). -/
theorem bwd_vvtestop (hf : Fires env "Step_pure" 57 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vvtestop hf
  obtain ⟨c₁, y, z, hcode, rfl, f₁, hy, hz⟩ := inst_c1 he
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 hy
  obtain ⟨t, any, rfl, ht, hany⟩ := inv_tup2 hu
  obtain ⟨rfl, rfl⟩ : t = vecTypeV ∧ any = caseNilV "ANY_TRUE" := ⟨inv_nil ht, inv_nil hany⟩
  obtain ⟨c, rfl, fc⟩ := inv_constI32 hz
  obtain ⟨b, i, rfl, rfl, hi⟩ := decode_c1 D (by simp [vecTags]) hcode
  obtain ⟨o, rfl, -⟩ := vecInstrV?_vvtestop hi
  obtain ⟨n, hsz, hnz⟩ := A.vvtestop o b
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ)
      [.expA (.callE "vsize" [.expA (.caseE "V128" (.tupE []))]), .expA (.varE "c_1")]
      [.val n, .val (vecV b)] :=
    Equiv.evalArgs_cons (evalExp_call rfl (evalArgs_v128 Equiv.evalArgs_nil) hsz)
      (evalArgs_var f₁ Equiv.evalArgs_nil)
  obtain rfl := inv_eq_call fc rfl hargs hnz hp
  exact ⟨[constI32 (vvtestop o b)], rfl, .vector (.vecTestOp o b)⟩

/-- `Backward.pure 66` (`Step_pure/vshiftop`). -/
theorem bwd_vshiftop (hf : Fires env "Step_pure" 66 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vshiftop hf
  obtain ⟨l, r, hv, hl, hr⟩ := inv_tup2 he
  obtain ⟨x₁, x₂, y, rfl, h₁, h₂, hy⟩ := inv_list3 hl
  obtain ⟨c₁, rfl, f₁⟩ := inv_vconst h₁
  obtain ⟨n, rfl, fn⟩ := inv_constI32 h₂
  obtain ⟨sh, op, rfl, fsh, fop⟩ := inv_op2 hy
  obtain ⟨z, rfl, hz⟩ := inv_list1 hr
  obtain ⟨c, rfl, fc⟩ := inv_vconst hz
  obtain ⟨hcode, rfl⟩ := tuple2_inj hv
  obtain ⟨b, k, i, rfl, rfl, rfl, hi⟩ := decode_c1i D (by simp [vecTags]) (Value.list.inj hcode)
  obtain ⟨s', o, rfl, hx⟩ := vecInstrV?_vshiftop hi
  obtain ⟨rfl, rfl⟩ := tuple2_inj hx
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.varE "sh"),
      .expA (.varE "vshiftop"), .expA (.varE "c_1"), .expA (.varE "i")]
      [.val (ishapeV s'), .val (vShiftOpV o), .val (vecV b), .val (i32NV k)] :=
    evalArgs_var fsh (evalArgs_var fop (evalArgs_var f₁ (evalArgs_var fn Equiv.evalArgs_nil)))
  obtain rfl := inv_eq_call fc rfl hargs (A.shiftOp s' o b k) hp
  exact ⟨_, rfl, .vector (.vecShiftOp s' o b k)⟩

/-- `Backward.pure 67` (`Step_pure/vbitmask`). -/
theorem bwd_vbitmask (hf : Fires env "Step_pure" 67 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vbitmask hf
  obtain ⟨c₁, y, z, hcode, rfl, f₁, hy, hz⟩ := inst_c1 he
  obtain ⟨sh, rfl, fsh⟩ := inv_op1 hy
  obtain ⟨c, rfl, fc⟩ := inv_constI32 hz
  obtain ⟨b, i, rfl, rfl, hi⟩ := decode_c1 D (by simp [vecTags]) hcode
  obtain ⟨s', rfl, rfl⟩ := vecInstrV?_vbitmask hi
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.varE "sh"), .expA (.varE "c_1")]
      [.val (ishapeV s'), .val (vecV b)] :=
    evalArgs_var fsh (evalArgs_var f₁ Equiv.evalArgs_nil)
  obtain rfl := inv_eq_call fc rfl hargs (A.bitmask s' b) hp
  exact ⟨[constI32 (vecBitmask s' b)], rfl, .vector (.vecBitmask s' b)⟩

/-- `Backward.pure 69` (`Step_pure/vshuffle`): the agreement makes `$vshufflop_` defined exactly
on in-range lane indices, which is `VectorStep.vecShuffle`'s side condition. -/
theorem bwd_vshuffle (hf : Fires env "Step_pure" 69 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vshuffle hf
  obtain ⟨c₁, c₂, y, z, hcode, rfl, f₁, f₂, hy, hz⟩ := inst_c2 he
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 hy
  obtain ⟨sh, lv, rfl, hsh, hlv⟩ := inv_tup2 hu
  obtain ⟨c, rfl, fc⟩ := inv_vconst hz
  obtain ⟨b₁, b₂, i, rfl, rfl, rfl, hi⟩ := decode_c2 D (by simp [vecTags]) hcode
  obtain ⟨ls, rfl, hx⟩ := vecInstrV?_vshuffle hi
  obtain ⟨rfl, rfl⟩ := tuple2_inj hx
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ) [.expA (.varE "sh"),
      .expA (Equiv.Execution.iterPat "i" "i*"), .expA (.varE "c_1"), .expA (.varE "c_2")]
      [.val bshapeV, .val (.list (ls.map laneIdxV)), .val (vecV b₁), .val (vecV b₂)] :=
    evalArgs_var (evalExp_varE_iff.1 hsh) (Equiv.evalArgs_cons hlv (evalArgs_var f₁
      (evalArgs_var f₂ Equiv.evalArgs_nil)))
  obtain ⟨hidx, rfl⟩ := (A.shuffle ls b₁ b₂ c).1 (inv_eq_call_app fc rfl hargs hp)
  exact ⟨_, rfl, .vector (.vecShuffle ls b₁ b₂ hidx)⟩

/-- `Backward.pure 77` (`Step_pure/vnarrow`): the premise reads the shapes under `ishape`. -/
theorem bwd_vnarrow (hf : Fires env "Step_pure" 77 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, he, hp⟩ := fires_if1 V.vnarrow hf
  obtain ⟨c₁, c₂, y, z, hcode, rfl, f₁, f₂, hy, hz⟩ := inst_c2 he
  obtain ⟨sh₂, sh₁, sx, rfl, fsh₂, fsh₁, fsx⟩ := inv_op3 hy
  obtain ⟨c, rfl, fc⟩ := inv_vconst hz
  obtain ⟨b₁, b₂, i, rfl, rfl, rfl, hi⟩ := decode_c2 D (by simp [vecTags]) hcode
  obtain ⟨s', t', x, rfl, hx⟩ := vecInstrV?_vnarrow hi
  obtain ⟨rfl, rfl, rfl⟩ := tuple3_inj hx
  have hargs : EvalArgs env (VarEnv.empty.bindVals σ)
      [.expA (.projE (.uncaseE (.varE "sh_1") "%") 0),
        .expA (.projE (.uncaseE (.varE "sh_2") "%") 0),
        .expA (.varE "sx"), .expA (.varE "c_1"), .expA (.varE "c_2")]
      [.val (ishV s'), .val (ishV t'), .val (sxV x), .val (vecV b₁), .val (vecV b₂)] :=
    Equiv.evalArgs_cons (Equiv.ExecVector.evalExp_pctFst_iff.2 ⟨[], fsh₁⟩)
      (Equiv.evalArgs_cons (Equiv.ExecVector.evalExp_pctFst_iff.2 ⟨[], fsh₂⟩)
      (evalArgs_var fsx (evalArgs_var f₁ (evalArgs_var f₂ Equiv.evalArgs_nil))))
  obtain ⟨r, hrel, rfl⟩ := (A.narrow s' t' x b₁ b₂ c).1 (inv_eq_call_app fc rfl hargs hp)
  exact ⟨[vconst r], rfl, .vector (.vecNarrow hrel)⟩

/-- **`Backward.pure i` for the 20 vector rules handled here** (all of 54–78 except `vtestop`
(64), `vsplat` (70), `vextract_lane-num`/`-pack` (71, 72) and `vreplace_lane` (73)). -/
theorem bwd_vectorRules (i : Nat)
    (hi : i ∈ [54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 65, 66, 67, 68, 69, 74, 75, 76, 77, 78])
    (hf : Fires env "Step_pure" i (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bwd_vvunop V D A hf, bwd_vvbinop V D A hf, bwd_vvternop V D A hf,
    bwd_vvtestop V D A hf, bwd_vunopVal V D A hf, bwd_vunopTrap V D A hf,
    bwd_vbinopVal V D A hf, bwd_vbinopTrap V D A hf, bwd_vternopVal V D A hf,
    bwd_vternopTrap V D A hf, bwd_vrelop V D A hf, bwd_vshiftop V D A hf,
    bwd_vbitmask V D A hf, bwd_vswizzlop V D A hf, bwd_vshuffle V D A hf,
    bwd_vextunop V D A hf, bwd_vextbinop V D A hf, bwd_vextternop V D A hf,
    bwd_vnarrow V D A hf, bwd_vcvtop V D A hf]

end

end Silmaril.Wasm.SpecTec.Sim.Vec
