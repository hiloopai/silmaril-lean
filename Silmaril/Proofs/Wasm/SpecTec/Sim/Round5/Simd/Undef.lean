module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Decode
public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Thms

/-!
# Round 5, track simd (pass 3): the lane-wise operators' clauses definitely fail

Every lane-wise operator binds the lanes of its operands in an `if` premise
(`c_1* = $lanes_(…)`), directly (`$vnarrowop__`) or in the helper its clause calls (`$ivunop_`,
`$fvbinop_`, …). The IL evaluator's `if` only tests, so the premise mentions an unbound variable
and definitely fails; the dispatcher clauses do not check the subtype of the lane-type
pattern (`Jnn`, `Fnn`), so the first clause whose operator matches is taken, and its body (a
helper call nobody answers) definitely fails as well. Hence `callDef` takes `B`'s answer
(`applies_iff_of_undef`). Each `TryClausesUndef` here is computed by unfolding the evaluator at a
fixed fuel (`undef_simp`), with the definitions read off the fixed script by `rfl`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30
open Round4Int (BI)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {H : Type}

/-- The clauses of a definition. -/
def clausesOf : Def → List Clause
  | .decD _ _ _ cs => cs
  | _ => []

/-- A term binding does not change the definition scope. -/
@[simp] theorem findDef?_bindVal (ρ : VarEnv) (x y : IL.Id) (v : Value) :
    (ρ.bindVal x v).findDef? y = ρ.findDef? y := rfl

/-- A definition binding does not change the term scope. -/
@[simp] theorem findVal?_bindDef (ρ : VarEnv) (x y z : IL.Id) :
    (ρ.bindDef x y).findVal? z = ρ.findVal? z := rfl

/-- The empty scope binds no definition. -/
@[simp] theorem findDef?_empty (y : IL.Id) : VarEnv.empty.findDef? y = none := rfl

/-- Where every clause definitely fails, a call denotes exactly what `B` answers. -/
theorem applies_iff_of_undef {env : Env} {x : IL.Id} {ws : List ArgV} {v : Value}
    {ps : List Param} {t : Typ} {cs : List Clause} (hd : env.findDef? x = some (ps, t, cs))
    (hu : TryClausesUndef env cs ws) :
    Applies env x ws v ↔ env.builtins.call x ws = some v := by
  constructor
  · rintro ⟨ps', t', cs', hd', hc⟩
    rw [hd] at hd'
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hd'
    rcases hc with hc | ⟨-, hb⟩
    · exact absurd hu (fun h => Equiv.ExecNumeric.not_tryClauses_and_undef hc h)
    · exact hb
  · intro hb
    exact ⟨ps, t, cs, hd, Or.inr ⟨hu, hb⟩⟩

/-- `applies_iff_of_undef` for a definition read off the script. -/
theorem applies_iff_of_undef' {env : Env} {x : IL.Id} {ws : List ArgV} {v : Value} {d : Def}
    (hd : env.findDef? x = IntNumeric.defOf d) (hdec : ∃ y ps t cs, d = .decD y ps t cs)
    (hu : TryClausesUndef env (clausesOf d) ws) :
    Applies env x ws v ↔ env.builtins.call x ws = some v := by
  obtain ⟨y, ps, t, cs, rfl⟩ := hdec
  exact applies_iff_of_undef hd hu

/-! ## The definitions, read off the script -/

set_option maxRecDepth 100000 in
/-- `$R_idot` has no clause (`Original.d393`). -/
theorem findDef_RIdot (B : Builtins) :
    (simEnv B).findDef? "R_idot" = IntNumeric.defOf Original.d393 := rfl

/-- `Prims.builtins` does not answer `$R_idot`. -/
@[simp] theorem call_RIdot (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "R_idot" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

set_option maxRecDepth 100000 in
/-- `$zeroop`, as the script defines it (`Original.d510`). -/
theorem findDef_Zeroop (B : Builtins) :
    (simEnv B).findDef? "zeroop" = IntNumeric.defOf Original.d510 := rfl

set_option maxRecDepth 100000 in
/-- `$halfop`, as the script defines it (`Original.d511`). -/
theorem findDef_Halfop (B : Builtins) :
    (simEnv B).findDef? "halfop" = IntNumeric.defOf Original.d511 := rfl

set_option maxRecDepth 100000 in
/-- `$half`, as the script defines it (`Original.d512`). -/
theorem findDef_Half (B : Builtins) :
    (simEnv B).findDef? "half" = IntNumeric.defOf Original.d512 := rfl

set_option maxRecDepth 100000 in
/-- `$ivunop_`, as the script defines it (`Original.d515`). -/
theorem findDef_Ivunop (B : Builtins) :
    (simEnv B).findDef? "ivunop_" = IntNumeric.defOf Original.d515 := rfl

set_option maxRecDepth 100000 in
/-- `$fvunop_`, as the script defines it (`Original.d516`). -/
theorem findDef_Fvunop (B : Builtins) :
    (simEnv B).findDef? "fvunop_" = IntNumeric.defOf Original.d516 := rfl

set_option maxRecDepth 100000 in
/-- `$ivbinop_`, as the script defines it (`Original.d517`). -/
theorem findDef_Ivbinop (B : Builtins) :
    (simEnv B).findDef? "ivbinop_" = IntNumeric.defOf Original.d517 := rfl

set_option maxRecDepth 100000 in
/-- `$ivbinopsx_`, as the script defines it (`Original.d518`). -/
theorem findDef_Ivbinopsx (B : Builtins) :
    (simEnv B).findDef? "ivbinopsx_" = IntNumeric.defOf Original.d518 := rfl

set_option maxRecDepth 100000 in
/-- `$ivbinopsxnd_`, as the script defines it (`Original.d519`). -/
theorem findDef_Ivbinopsxnd (B : Builtins) :
    (simEnv B).findDef? "ivbinopsxnd_" = IntNumeric.defOf Original.d519 := rfl

set_option maxRecDepth 100000 in
/-- `$fvbinop_`, as the script defines it (`Original.d520`). -/
theorem findDef_Fvbinop (B : Builtins) :
    (simEnv B).findDef? "fvbinop_" = IntNumeric.defOf Original.d520 := rfl

set_option maxRecDepth 100000 in
/-- `$ivternopnd_`, as the script defines it (`Original.d521`). -/
theorem findDef_Ivternopnd (B : Builtins) :
    (simEnv B).findDef? "ivternopnd_" = IntNumeric.defOf Original.d521 := rfl

set_option maxRecDepth 100000 in
/-- `$fvternop_`, as the script defines it (`Original.d522`). -/
theorem findDef_Fvternop (B : Builtins) :
    (simEnv B).findDef? "fvternop_" = IntNumeric.defOf Original.d522 := rfl

set_option maxRecDepth 100000 in
/-- `$ivrelop_`, as the script defines it (`Original.d523`). -/
theorem findDef_Ivrelop (B : Builtins) :
    (simEnv B).findDef? "ivrelop_" = IntNumeric.defOf Original.d523 := rfl

set_option maxRecDepth 100000 in
/-- `$ivrelopsx_`, as the script defines it (`Original.d524`). -/
theorem findDef_Ivrelopsx (B : Builtins) :
    (simEnv B).findDef? "ivrelopsx_" = IntNumeric.defOf Original.d524 := rfl

set_option maxRecDepth 100000 in
/-- `$fvrelop_`, as the script defines it (`Original.d525`). -/
theorem findDef_Fvrelop (B : Builtins) :
    (simEnv B).findDef? "fvrelop_" = IntNumeric.defOf Original.d525 := rfl

set_option maxRecDepth 100000 in
/-- `$ivshiftop_`, as the script defines it (`Original.d526`). -/
theorem findDef_Ivshiftop (B : Builtins) :
    (simEnv B).findDef? "ivshiftop_" = IntNumeric.defOf Original.d526 := rfl

set_option maxRecDepth 100000 in
/-- `$ivshiftopsx_`, as the script defines it (`Original.d527`). -/
theorem findDef_Ivshiftopsx (B : Builtins) :
    (simEnv B).findDef? "ivshiftopsx_" = IntNumeric.defOf Original.d527 := rfl

set_option maxRecDepth 100000 in
/-- `$ivbitmaskop_`, as the script defines it (`Original.d528`). -/
theorem findDef_Ivbitmaskop (B : Builtins) :
    (simEnv B).findDef? "ivbitmaskop_" = IntNumeric.defOf Original.d528 := rfl

set_option maxRecDepth 100000 in
/-- `$ivswizzlop_`, as the script defines it (`Original.d529`). -/
theorem findDef_Ivswizzlop (B : Builtins) :
    (simEnv B).findDef? "ivswizzlop_" = IntNumeric.defOf Original.d529 := rfl

set_option maxRecDepth 100000 in
/-- `$ivshufflop_`, as the script defines it (`Original.d530`). -/
theorem findDef_Ivshufflop (B : Builtins) :
    (simEnv B).findDef? "ivshufflop_" = IntNumeric.defOf Original.d530 := rfl

set_option maxRecDepth 100000 in
/-- `$ivextunop__`, as the script defines it (`Original.d546`). -/
theorem findDef_Ivextunop (B : Builtins) :
    (simEnv B).findDef? "ivextunop__" = IntNumeric.defOf Original.d546 := rfl

set_option maxRecDepth 100000 in
/-- `$ivextbinop__`, as the script defines it (`Original.d550`). -/
theorem findDef_Ivextbinop (B : Builtins) :
    (simEnv B).findDef? "ivextbinop__" = IntNumeric.defOf Original.d550 := rfl

set_option maxRecDepth 100000 in
/-- `$vunop_`, as the script defines it (`Original.d534`). -/
theorem findDef_Vunop (B : Builtins) :
    (simEnv B).findDef? "vunop_" = IntNumeric.defOf Original.d534 := rfl

set_option maxRecDepth 100000 in
/-- `$vbinop_`, as the script defines it (`Original.d535`). -/
theorem findDef_Vbinop (B : Builtins) :
    (simEnv B).findDef? "vbinop_" = IntNumeric.defOf Original.d535 := rfl

set_option maxRecDepth 100000 in
/-- `$vternop_`, as the script defines it (`Original.d536`). -/
theorem findDef_Vternop (B : Builtins) :
    (simEnv B).findDef? "vternop_" = IntNumeric.defOf Original.d536 := rfl

set_option maxRecDepth 100000 in
/-- `$vrelop_`, as the script defines it (`Original.d537`). -/
theorem findDef_Vrelop (B : Builtins) :
    (simEnv B).findDef? "vrelop_" = IntNumeric.defOf Original.d537 := rfl

set_option maxRecDepth 100000 in
/-- `$vcvtop__`, as the script defines it (`Original.d539`). -/
theorem findDef_Vcvtop (B : Builtins) :
    (simEnv B).findDef? "vcvtop__" = IntNumeric.defOf Original.d539 := rfl

set_option maxRecDepth 100000 in
/-- `$vshiftop_`, as the script defines it (`Original.d540`). -/
theorem findDef_Vshiftop (B : Builtins) :
    (simEnv B).findDef? "vshiftop_" = IntNumeric.defOf Original.d540 := rfl

set_option maxRecDepth 100000 in
/-- `$vbitmaskop_`, as the script defines it (`Original.d541`). -/
theorem findDef_Vbitmaskop (B : Builtins) :
    (simEnv B).findDef? "vbitmaskop_" = IntNumeric.defOf Original.d541 := rfl

set_option maxRecDepth 100000 in
/-- `$vswizzlop_`, as the script defines it (`Original.d542`). -/
theorem findDef_Vswizzlop (B : Builtins) :
    (simEnv B).findDef? "vswizzlop_" = IntNumeric.defOf Original.d542 := rfl

set_option maxRecDepth 100000 in
/-- `$vshufflop_`, as the script defines it (`Original.d543`). -/
theorem findDef_Vshufflop (B : Builtins) :
    (simEnv B).findDef? "vshufflop_" = IntNumeric.defOf Original.d543 := rfl

set_option maxRecDepth 100000 in
/-- `$vnarrowop__`, as the script defines it (`Original.d544`). -/
theorem findDef_Vnarrowop (B : Builtins) :
    (simEnv B).findDef? "vnarrowop__" = IntNumeric.defOf Original.d544 := rfl

set_option maxRecDepth 100000 in
/-- `$vextunop__`, as the script defines it (`Original.d547`). -/
theorem findDef_Vextunop (B : Builtins) :
    (simEnv B).findDef? "vextunop__" = IntNumeric.defOf Original.d547 := rfl

set_option maxRecDepth 100000 in
/-- `$vextbinop__`, as the script defines it (`Original.d552`). -/
theorem findDef_Vextbinop (B : Builtins) :
    (simEnv B).findDef? "vextbinop__" = IntNumeric.defOf Original.d552 := rfl

set_option maxRecDepth 100000 in
/-- `$vextternop__`, as the script defines it (`Original.d553`). -/
theorem findDef_Vextternop (B : Builtins) :
    (simEnv B).findDef? "vextternop__" = IntNumeric.defOf Original.d553 := rfl

/-! ## The helpers are not primitives -/

/-- `Prims.builtins` does not answer `$ivunop_`. -/
@[simp] theorem call_Ivunop (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "ivunop_" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- `Prims.builtins` does not answer `$fvunop_`. -/
@[simp] theorem call_Fvunop (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "fvunop_" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- `Prims.builtins` does not answer `$ivbinop_`. -/
@[simp] theorem call_Ivbinop (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "ivbinop_" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- `Prims.builtins` does not answer `$ivbinopsx_`. -/
@[simp] theorem call_Ivbinopsx (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "ivbinopsx_" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- `Prims.builtins` does not answer `$ivbinopsxnd_`. -/
@[simp] theorem call_Ivbinopsxnd (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "ivbinopsxnd_" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- `Prims.builtins` does not answer `$fvbinop_`. -/
@[simp] theorem call_Fvbinop (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "fvbinop_" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- `Prims.builtins` does not answer `$ivternopnd_`. -/
@[simp] theorem call_Ivternopnd (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "ivternopnd_" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- `Prims.builtins` does not answer `$fvternop_`. -/
@[simp] theorem call_Fvternop (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "fvternop_" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- `Prims.builtins` does not answer `$ivrelop_`. -/
@[simp] theorem call_Ivrelop (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "ivrelop_" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- `Prims.builtins` does not answer `$ivrelopsx_`. -/
@[simp] theorem call_Ivrelopsx (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "ivrelopsx_" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- `Prims.builtins` does not answer `$fvrelop_`. -/
@[simp] theorem call_Fvrelop (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "fvrelop_" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- `Prims.builtins` does not answer `$ivshiftop_`. -/
@[simp] theorem call_Ivshiftop (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "ivshiftop_" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- `Prims.builtins` does not answer `$ivshiftopsx_`. -/
@[simp] theorem call_Ivshiftopsx (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "ivshiftopsx_" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- `Prims.builtins` does not answer `$ivbitmaskop_`. -/
@[simp] theorem call_Ivbitmaskop (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "ivbitmaskop_" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- `Prims.builtins` does not answer `$ivswizzlop_`. -/
@[simp] theorem call_Ivswizzlop (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "ivswizzlop_" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- `Prims.builtins` does not answer `$ivshufflop_`. -/
@[simp] theorem call_Ivshufflop (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "ivshufflop_" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- `Prims.builtins` does not answer `$ivextunop__`. -/
@[simp] theorem call_Ivextunop (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "ivextunop__" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- `Prims.builtins` does not answer `$ivextbinop__`. -/
@[simp] theorem call_Ivextbinop (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (simEnv (BI P hn host)).builtins.call "ivextbinop__" ws = none := by
  simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- Unfold the evaluator on a clause list, at a fixed fuel. -/
macro "undef_simp" "[" extra:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  set_option linter.unusedSimpArgs false in
  simp [clausesOf, tryClauses, matchArgs, matchArg, matchExp, matchExps, argSubOk, premsHold,
    premHolds, evalExp, evalIterE, evalDoms, domVar, domSrc, evalArgs, evalArg, evalExps, callDef,
    Res.assert, Res.ofOption, Res.elimUndef, Bind.bind, Except.bind, pure, Except.pure,
    Functor.map, Except.map, Value.asTuple?, Value.asCase?, IntNumeric.defOf, Vec.ishapeV, Vec.ishV, Vec.fshV, Vec.bshapeV, Vec.vIntUnOpV, Vec.vFloatUnOpV,
    Vec.vIntBinOpV, Vec.vFloatBinOpV, Vec.vIntTernOpV, Vec.vFloatTernOpV, Vec.vIntRelOpV,
    Vec.vFloatRelOpV, Vec.vShiftOpV, Vec.vSwizzleOpV, Vec.vExtUnOpV, Vec.vExtBinOpV, Vec.vExtTernOpV,
    Vec.sxV, Vec.halfV, caseNilV, Vec.intLaneV, Vec.floatLaneV, pctV,
    Original.d512, findDef_Half, Original.d393, findDef_RIdot,
    Original.d515, findDef_Ivunop, Original.d516, findDef_Fvunop, Original.d517, findDef_Ivbinop, Original.d518, findDef_Ivbinopsx, Original.d519, findDef_Ivbinopsxnd, Original.d520, findDef_Fvbinop, Original.d521, findDef_Ivternopnd, Original.d522, findDef_Fvternop, Original.d523, findDef_Ivrelop, Original.d524, findDef_Ivrelopsx, Original.d525, findDef_Fvrelop, Original.d526, findDef_Ivshiftop, Original.d527, findDef_Ivshiftopsx, Original.d528, findDef_Ivbitmaskop, Original.d529, findDef_Ivswizzlop, Original.d530, findDef_Ivshufflop, Original.d546, findDef_Ivextunop, Original.d550, findDef_Ivextbinop, $extra,*])

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
