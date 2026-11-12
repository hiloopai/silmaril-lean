module

public import Silmaril.Wasm.SpecTec.Sim.State.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Basic
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Provenance

/-!
# Family M: evaluating the state accessors

The state rules read and write the configuration through defined functions of the script
(`$local`, `$global`, `$table`, …, `$with_local`, `$with_global`). This file evaluates them,
first generically (any single-clause definition, `evalExp_call1`; reading and writing through a
path, `pathGet_*`/`pathSet_*`), then on arbitrary state values (`evalExp_sof`, `evalExp_local`,
`evalExp_storeAcc`, `evalExp_withLocal`, `evalExp_withGlobal`), and proves the environment facts
`StateDefs` for every `simEnv B` (`stateDefs_simEnv`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.State

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)

/-! ## Calls and paths -/

/-- A call of a single-clause definition: match the arguments, evaluate the body. -/
theorem evalExp_call1 {env : Env} {ρ ρ₀ : VarEnv} {x : IL.Id} {pats args : List Arg}
    {ws : List ArgV} {body : Exp} {v : Value} (hd : HasClause1 env x pats body)
    (hρ : ρ.findDef? x = none) (ha : EvalArgs env ρ args ws)
    (hm : MatchArgs env VarEnv.empty pats ws ρ₀) (he : EvalExp env ρ₀ body v) :
    EvalExp env ρ (.callE x args) v := by
  obtain ⟨ps, t, q, hf⟩ := hd
  exact evalExp_callE_iff.2 (callDef_of_tryClauses hρ hf ha (tryClauses_hit hm premsHold_nil he))

/-- The root of a path is the value itself. -/
theorem pathGet_root {env : Env} {ρ : VarEnv} {v : Value} : PathGet env ρ v .rootP v :=
  ⟨1, by simp only [pathGet]⟩

/-- Reading a field through a path. -/
theorem pathGet_dot {env : Env} {ρ : VarEnv} {v u w : Value} {p : Path} {a : AtomS}
    (h : PathGet env ρ v p u) (hf : u.field? a = some w) : PathGet env ρ v (.dotP p a) w := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 1, by simp only [pathGet, h, Bind.bind, Except.bind, hf, Res.ofOption]⟩

/-- Reading an element through a path. -/
theorem pathGet_idx {env : Env} {ρ : VarEnv} {v u w : Value} {p : Path} {e : Exp} {i : Nat}
    (h : PathGet env ρ v p u) (he : EvalExp env ρ e (.num (.natN i))) (hi : u.idx? i = some w) :
    PathGet env ρ v (.idxP p e) w := by
  obtain ⟨n₁, h⟩ := h
  obtain ⟨n₂, he⟩ := he
  refine ⟨max n₁ n₂ + 1, ?_⟩
  simp only [pathGet, pathGet_ok_of_le (le_max_left n₁ n₂) h, Bind.bind, Except.bind,
    evalExp_ok_of_le (le_max_right n₁ n₂) he, Value.asNat?, Res.ofOption, hi]

/-- Writing at the root replaces the value. -/
theorem pathSet_root {env : Env} {ρ : VarEnv} {v w : Value} : PathSet env ρ v .rootP w w :=
  ⟨1, by simp only [pathSet]⟩

/-- Writing a field through a path. -/
theorem pathSet_dot {env : Env} {ρ : VarEnv} {v u u' w r : Value} {p : Path} {a : AtomS}
    (hg : PathGet env ρ v p u) (hs : u.setField a w = some u') (hr : PathSet env ρ v p u' r) :
    PathSet env ρ v (.dotP p a) w r := by
  obtain ⟨n₁, hg⟩ := hg
  obtain ⟨n₂, hr⟩ := hr
  refine ⟨max n₁ n₂ + 1, ?_⟩
  simp only [pathSet, pathGet_ok_of_le (le_max_left n₁ n₂) hg, Bind.bind, Except.bind, hs,
    Res.ofOption, pathSet_ok_of_le (le_max_right n₁ n₂) hr]

/-- Writing an element through a path. -/
theorem pathSet_idx {env : Env} {ρ : VarEnv} {v u u' w r : Value} {p : Path} {e : Exp} {i : Nat}
    (hg : PathGet env ρ v p u) (he : EvalExp env ρ e (.num (.natN i)))
    (hs : u.setIdx i w = some u') (hr : PathSet env ρ v p u' r) :
    PathSet env ρ v (.idxP p e) w r := by
  obtain ⟨n₁, hg⟩ := hg
  obtain ⟨n₂, he⟩ := he
  obtain ⟨n₃, hr⟩ := hr
  refine ⟨max (max n₁ n₂) n₃ + 1, ?_⟩
  simp only [pathSet, pathGet_ok_of_le (show n₁ ≤ max (max n₁ n₂) n₃ by omega) hg, Bind.bind,
    Except.bind, evalExp_ok_of_le (show n₂ ≤ max (max n₁ n₂) n₃ by omega) he, Value.asNat?,
    Res.ofOption, hs, pathSet_ok_of_le (show n₃ ≤ max (max n₁ n₂) n₃ by omega) hr]

/-! ## Argument patterns -/

/-- `(s; f)` matches a state. -/
theorem matchArgs_statePat {env : Env} {S F : Value} :
    MatchArgs env VarEnv.empty statePat [.val (stV S F)]
      ((VarEnv.empty.bindVal "s" S).bindVal "f" F) :=
  matchArgs_cons (matchArg_expA (matchExp_caseE (Equiv.Validation.matchExp_tup_iff.2 ⟨[S, F], rfl,
    Equiv.Execution.matchExps_two_iff.2 ⟨S, F, _, rfl, matchExp_varE rfl, matchExp_varE rfl⟩⟩)))
    matchArgs_nil

/-- `z` matches anything. -/
theorem matchArgs_zPat {env : Env} {Z : Value} :
    MatchArgs env VarEnv.empty zPat [.val Z] (VarEnv.empty.bindVal "z" Z) :=
  matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil

/-- `z, x` matches anything. -/
theorem matchArgs_zxPat {env : Env} {Z X : Value} :
    MatchArgs env VarEnv.empty zxPat [.val Z, .val X]
      ((VarEnv.empty.bindVal "z" Z).bindVal "x" X) :=
  matchArgs_cons (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)

/-- `z, x, v` matches anything. -/
theorem matchArgs_zxvPat {env : Env} {Z X V : Value} :
    MatchArgs env VarEnv.empty zxvPat [.val Z, .val X, .val V]
      (((VarEnv.empty.bindVal "z" Z).bindVal "x" X).bindVal "v" V) :=
  matchArgs_cons (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))

/-! ## The projections of a state -/

section Projections

variable {env : Env} (D : StateDefs env) {ρ : VarEnv} {e : Exp} {S F : Value}
include D

/-- `$store((s; f)) = s`. -/
theorem evalExp_store (hρ : ρ.findDef? "store" = none) (he : EvalExp env ρ e (stV S F)) :
    EvalExp env ρ (.callE "store" [.expA e]) S :=
  evalExp_call1 D.store hρ (evalArgs_cons he evalArgs_nil) matchArgs_statePat
    (evalExp_var rfl)

/-- `$frame((s; f)) = f`. -/
theorem evalExp_frame (hρ : ρ.findDef? "frame" = none) (he : EvalExp env ρ e (stV S F)) :
    EvalExp env ρ (.callE "frame" [.expA e]) F :=
  evalExp_call1 D.frame hρ (evalArgs_cons he evalArgs_nil) matchArgs_statePat
    (evalExp_var rfl)

/-- `$sof(z)`, the store of a state. -/
theorem evalExp_sof (hρ : ρ.findDef? "sof" = none) (he : EvalExp env ρ e (stV S F)) :
    EvalExp env ρ (.callE "sof" [.expA e]) S :=
  evalExp_call1 D.sof hρ (evalArgs_cons he evalArgs_nil) matchArgs_zPat
    (evalExp_store D rfl (evalExp_var rfl))

/-- `$fof(z)`, the frame of a state. -/
theorem evalExp_fof (hρ : ρ.findDef? "fof" = none) (he : EvalExp env ρ e (stV S F)) :
    EvalExp env ρ (.callE "fof" [.expA e]) F :=
  evalExp_call1 D.fof hρ (evalArgs_cons he evalArgs_nil) matchArgs_zPat
    (evalExp_frame D rfl (evalExp_var rfl))

end Projections

/-- `x!%.0` on a `%`-wrapped numeral. -/
theorem evalExp_idxPayload {env : Env} {ρ : VarEnv} {n : Nat}
    (h : ρ.findVal? "x" = some (.case "%" (.tuple [.num (.natN n)]))) :
    EvalExp env ρ idxPayload (.num (.natN n)) :=
  evalExp_projE_iff.2 ⟨[.num (.natN n)], evalExp_uncaseE_iff.2 (evalExp_var h), Int.le_refl 0, rfl⟩

/-- `y*` matches any list, binding `y*`. -/
theorem matchExp_iterVar {env : Env} {ρ₀ : VarEnv} {y ys : IL.Id} {l : List Value}
    (hy : ρ₀.findVal? y = none) (hy' : y ≠ "_") (hys : ρ₀.findVal? ys = none) :
    MatchExp env ρ₀ (iterVar y ys) (.list l) (ρ₀.bindVal ys (.list l)) :=
  (Equiv.Execution.matchExp_iterE_list_iff (Equiv.Execution.bindsVar_varE y) hy hy').2
    ⟨l, rfl, matchExp_varE hys⟩

/-! ## The accessors -/

section Accessors

variable {env : Env} (D : StateDefs env) {ρ : VarEnv} {ez ex : Exp} {S F : Value} {n : Nat}
include D

/-- The scope of an accessor's clause. -/
abbrev accScope (Z X : Value) : VarEnv := (VarEnv.empty.bindVal "z" Z).bindVal "x" X

/-- The store accessor for field `Fl` evaluates to the store's `Fl` entry at the address the
frame's module lists at index `n`. -/
theorem evalExp_storeAccBody {Fl : AtomS} {Ls As : List Value} {M r : Value} {a : Nat}
    (hS : S.field? Fl = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? Fl = some (.list As)) (ha : As[n]? = some (.num (.natN a)))
    (hr : Ls[a]? = some r) :
    EvalExp env (accScope (stV S F) (.case "%" (.tuple [.num (.natN n)]))) (storeAccBody Fl) r :=
  evalExp_idxE_iff.2 ⟨.list Ls, a,
    evalExp_dotE_iff.2 ⟨S, evalExp_sof D rfl (evalExp_var rfl), hS⟩,
    evalExp_idxE_iff.2 ⟨.list As, n,
      evalExp_dotE_iff.2 ⟨M, evalExp_dotE_iff.2 ⟨F, evalExp_fof D rfl (evalExp_var rfl), hM⟩, hA⟩,
      evalExp_idxPayload rfl, ha⟩, hr⟩

/-- `$local(z, x) = $fof(z).LOCALS[x!%.0]`. -/
theorem evalExp_local {L r : Value} (hρ : ρ.findDef? "local" = none)
    (hz : EvalExp env ρ ez (stV S F)) (hx : EvalExp env ρ ex (.case "%" (.tuple [.num (.natN n)])))
    (hL : F.field? "LOCALS" = some L) (hr : L.idx? n = some r) :
    EvalExp env ρ (.callE "local" [.expA ez, .expA ex]) r :=
  evalExp_call1 D.local_ hρ (evalArgs_cons hz (evalArgs_cons hx evalArgs_nil)) matchArgs_zxPat
    (evalExp_idxE_iff.2 ⟨L, n, evalExp_dotE_iff.2 ⟨F, evalExp_fof D rfl (evalExp_var rfl), hL⟩,
      evalExp_idxPayload rfl, hr⟩)

/-- `$global(z, x)`. -/
theorem evalExp_global {Ls As : List Value} {M r : Value} {a : Nat}
    (hρ : ρ.findDef? "global" = none)
    (hz : EvalExp env ρ ez (stV S F)) (hx : EvalExp env ρ ex (.case "%" (.tuple [.num (.natN n)])))
    (hS : S.field? "GLOBALS" = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? "GLOBALS" = some (.list As)) (ha : As[n]? = some (.num (.natN a)))
    (hr : Ls[a]? = some r) :
    EvalExp env ρ (.callE "global" [.expA ez, .expA ex]) r :=
  evalExp_call1 D.global hρ (evalArgs_cons hz (evalArgs_cons hx evalArgs_nil)) matchArgs_zxPat
    (evalExp_storeAccBody D hS hM hA ha hr)

/-- `$table(z, x)`. -/
theorem evalExp_table {Ls As : List Value} {M r : Value} {a : Nat}
    (hρ : ρ.findDef? "table" = none)
    (hz : EvalExp env ρ ez (stV S F)) (hx : EvalExp env ρ ex (.case "%" (.tuple [.num (.natN n)])))
    (hS : S.field? "TABLES" = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? "TABLES" = some (.list As)) (ha : As[n]? = some (.num (.natN a)))
    (hr : Ls[a]? = some r) :
    EvalExp env ρ (.callE "table" [.expA ez, .expA ex]) r :=
  evalExp_call1 D.table hρ (evalArgs_cons hz (evalArgs_cons hx evalArgs_nil)) matchArgs_zxPat
    (evalExp_storeAccBody D hS hM hA ha hr)

/-- `$mem(z, x)`. -/
theorem evalExp_mem {Ls As : List Value} {M r : Value} {a : Nat}
    (hρ : ρ.findDef? "mem" = none)
    (hz : EvalExp env ρ ez (stV S F)) (hx : EvalExp env ρ ex (.case "%" (.tuple [.num (.natN n)])))
    (hS : S.field? "MEMS" = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? "MEMS" = some (.list As)) (ha : As[n]? = some (.num (.natN a)))
    (hr : Ls[a]? = some r) :
    EvalExp env ρ (.callE "mem" [.expA ez, .expA ex]) r :=
  evalExp_call1 D.mem hρ (evalArgs_cons hz (evalArgs_cons hx evalArgs_nil)) matchArgs_zxPat
    (evalExp_storeAccBody D hS hM hA ha hr)

/-- `$elem(z, x)`. -/
theorem evalExp_elem {Ls As : List Value} {M r : Value} {a : Nat}
    (hρ : ρ.findDef? "elem" = none)
    (hz : EvalExp env ρ ez (stV S F)) (hx : EvalExp env ρ ex (.case "%" (.tuple [.num (.natN n)])))
    (hS : S.field? "ELEMS" = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? "ELEMS" = some (.list As)) (ha : As[n]? = some (.num (.natN a)))
    (hr : Ls[a]? = some r) :
    EvalExp env ρ (.callE "elem" [.expA ez, .expA ex]) r :=
  evalExp_call1 D.elem hρ (evalArgs_cons hz (evalArgs_cons hx evalArgs_nil)) matchArgs_zxPat
    (evalExp_storeAccBody D hS hM hA ha hr)

/-- `$data(z, x)`. -/
theorem evalExp_data {Ls As : List Value} {M r : Value} {a : Nat}
    (hρ : ρ.findDef? "data" = none)
    (hz : EvalExp env ρ ez (stV S F)) (hx : EvalExp env ρ ex (.case "%" (.tuple [.num (.natN n)])))
    (hS : S.field? "DATAS" = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? "DATAS" = some (.list As)) (ha : As[n]? = some (.num (.natN a)))
    (hr : Ls[a]? = some r) :
    EvalExp env ρ (.callE "data" [.expA ez, .expA ex]) r :=
  evalExp_call1 D.data hρ (evalArgs_cons hz (evalArgs_cons hx evalArgs_nil)) matchArgs_zxPat
    (evalExp_storeAccBody D hS hM hA ha hr)

/-- `$with_local(z, x, v)`: the frame's `LOCALS` entry `n` becomes `?(v)`. -/
theorem evalExp_withLocal {ev : Exp} {V F' : Value} {L : List Value}
    (hρ : ρ.findDef? "with_local" = none) (hz : EvalExp env ρ ez (stV S F))
    (hx : EvalExp env ρ ex (.case "%" (.tuple [.num (.natN n)]))) (hv : EvalExp env ρ ev V)
    (hL : F.field? "LOCALS" = some (.list L)) (hn : n < L.length)
    (hF : F.setField "LOCALS" (.list (L.set n (.opt (some V)))) = some F') :
    EvalExp env ρ (.callE "with_local" [.expA ez, .expA ex, .expA ev]) (stV S F') := by
  refine evalExp_call1 D.withLocal hρ
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons hv evalArgs_nil))) matchArgs_zxvPat ?_
  refine evalExp_case (evalExp_tup2 (evalExp_sof D rfl (evalExp_var rfl)) ?_)
  refine evalExp_updE_iff.2 ⟨F, .opt (some V), evalExp_fof D rfl (evalExp_var rfl),
    evalExp_optE_some_iff.2 ⟨V, evalExp_var rfl, rfl⟩, ?_⟩
  refine pathSet_idx (pathGet_dot pathGet_root hL) (evalExp_idxPayload rfl)
    (by simp [Value.setIdx, hn]) (pathSet_dot pathGet_root hF pathSet_root)

/-- `$with_global(z, x, v)`: the `VALUE` of the global the frame's module lists at `n` becomes
`v`. -/
theorem evalExp_withGlobal {ev : Exp} {V M g g' S' : Value} {Ls As : List Value} {a : Nat}
    (hρ : ρ.findDef? "with_global" = none) (hz : EvalExp env ρ ez (stV S F))
    (hx : EvalExp env ρ ex (.case "%" (.tuple [.num (.natN n)]))) (hv : EvalExp env ρ ev V)
    (hS : S.field? "GLOBALS" = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? "GLOBALS" = some (.list As)) (ha : As[n]? = some (.num (.natN a)))
    (hg : Ls[a]? = some g) (hg' : g.setField "VALUE" V = some g')
    (hS' : S.setField "GLOBALS" (.list (Ls.set a g')) = some S') :
    EvalExp env ρ (.callE "with_global" [.expA ez, .expA ex, .expA ev]) (stV S' F) := by
  refine evalExp_call1 D.withGlobal hρ
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons hv evalArgs_nil))) matchArgs_zxvPat ?_
  refine evalExp_case (evalExp_tup2 ?_ (evalExp_fof D rfl (evalExp_var rfl)))
  have hidx : EvalExp env (((VarEnv.empty.bindVal "z" (stV S F)).bindVal "x"
      (.case "%" (.tuple [.num (.natN n)]))).bindVal "v" V)
      (.idxE (.dotE (.dotE (.callE "fof" [.expA (.varE "z")]) "MODULE") "GLOBALS") idxPayload)
      (.num (.natN a)) :=
    evalExp_idxE_iff.2 ⟨.list As, n,
      evalExp_dotE_iff.2 ⟨M, evalExp_dotE_iff.2 ⟨F, evalExp_fof D rfl (evalExp_var rfl), hM⟩, hA⟩,
      evalExp_idxPayload rfl, ha⟩
  have ha' : a < Ls.length := (List.getElem?_eq_some_iff.1 hg).1
  refine evalExp_updE_iff.2 ⟨S, V, evalExp_sof D rfl (evalExp_var rfl), evalExp_var rfl, ?_⟩
  exact pathSet_dot (pathGet_idx (pathGet_dot pathGet_root hS) hidx hg) hg'
    (pathSet_idx (pathGet_dot pathGet_root hS) hidx (by simp [Value.setIdx, ha'])
      (pathSet_dot pathGet_root hS' pathSet_root))

/-- `$fof(z).MODULE.F[x!%.0]` in an updater's scope. -/
theorem evalExp_modAddr {ρ₀ : VarEnv} {Fl : AtomS} {M : Value} {As : List Value} {a : Nat}
    (hd : ρ₀.findDef? "fof" = none) (hz : ρ₀.findVal? "z" = some (stV S F)) (hx : ρ₀.findVal? "x" = some (idxV n))
    (hM : F.field? "MODULE" = some M) (hA : M.field? Fl = some (.list As))
    (ha : As[n]? = some (.num (.natN a))) : EvalExp env ρ₀ (modAddr Fl) (.num (.natN a)) :=
  evalExp_idxE_iff.2 ⟨.list As, n,
    evalExp_dotE_iff.2 ⟨M, evalExp_dotE_iff.2 ⟨F, evalExp_fof D hd (evalExp_var hz), hM⟩, hA⟩,
    evalExp_idxPayload hx, ha⟩

/-- `$with_table(z, x, i, r)`: entry `i` of the `REFS` of the table the module lists at `n`
becomes `r`. -/
theorem evalExp_withTable {ei er : Exp} {R M t t' S' : Value} {Ls As rs : List Value} {a i : Nat}
    (hρ : ρ.findDef? "with_table" = none) (hz : EvalExp env ρ ez (stV S F))
    (hx : EvalExp env ρ ex (idxV n)) (hi : EvalExp env ρ ei (.num (.natN i)))
    (hr : EvalExp env ρ er R)
    (hS : S.field? "TABLES" = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? "TABLES" = some (.list As)) (ha : As[n]? = some (.num (.natN a)))
    (ht : Ls[a]? = some t) (hR : t.field? "REFS" = some (.list rs)) (hi' : i < rs.length)
    (ht' : t.setField "REFS" (.list (rs.set i R)) = some t')
    (hS' : S.setField "TABLES" (.list (Ls.set a t')) = some S') :
    EvalExp env ρ (.callE "with_table" [.expA ez, .expA ex, .expA ei, .expA er]) (stV S' F) := by
  refine evalExp_call1 D.withTable hρ
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons hi (evalArgs_cons hr evalArgs_nil))))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))) ?_
  refine evalExp_case (evalExp_tup2 ?_ (evalExp_fof D rfl (evalExp_var rfl)))
  let ρ₁ := (((VarEnv.empty.bindVal "z" (stV S F)).bindVal "x" (idxV n)).bindVal "i"
    (.num (.natN i))).bindVal "r" R
  have hidx : EvalExp env ρ₁ (modAddr "TABLES") (.num (.natN a)) :=
    evalExp_modAddr D rfl rfl rfl hM hA ha
  have ha' : a < Ls.length := (List.getElem?_eq_some_iff.1 ht).1
  have hg : PathGet env ρ₁ S (.idxP (.dotP .rootP "TABLES") (modAddr "TABLES")) t :=
    pathGet_idx (pathGet_dot pathGet_root hS) hidx ht
  refine evalExp_updE_iff.2 ⟨S, R, evalExp_sof D rfl (evalExp_var rfl), evalExp_var rfl, ?_⟩
  exact pathSet_idx (pathGet_dot hg hR) (evalExp_var rfl) (by simp [Value.setIdx, hi'])
    (pathSet_dot hg ht' (pathSet_idx (pathGet_dot pathGet_root hS) hidx
      (by simp [Value.setIdx, ha']) (pathSet_dot pathGet_root hS' pathSet_root)))

/-- `$with_elem(z, x, r*)`: the `REFS` of the segment the module lists at `n` become `r*`. -/
theorem evalExp_withElem {er : Exp} {M t t' S' : Value} {Ls As rs : List Value} {a : Nat}
    (hρ : ρ.findDef? "with_elem" = none) (hz : EvalExp env ρ ez (stV S F))
    (hx : EvalExp env ρ ex (idxV n)) (hr : EvalExp env ρ er (.list rs))
    (hS : S.field? "ELEMS" = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? "ELEMS" = some (.list As)) (ha : As[n]? = some (.num (.natN a)))
    (ht : Ls[a]? = some t) (ht' : t.setField "REFS" (.list rs) = some t')
    (hS' : S.setField "ELEMS" (.list (Ls.set a t')) = some S') :
    EvalExp env ρ (.callE "with_elem" [.expA ez, .expA ex, .expA er]) (stV S' F) := by
  refine evalExp_call1 D.withElem hρ
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons hr evalArgs_nil)))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA
        (matchExp_iterVar rfl (by decide) rfl)) matchArgs_nil))) ?_
  refine evalExp_case (evalExp_tup2 ?_ (evalExp_fof D rfl (evalExp_var rfl)))
  let ρ₁ := ((VarEnv.empty.bindVal "z" (stV S F)).bindVal "x" (idxV n)).bindVal "r*" (.list rs)
  have hidx : EvalExp env ρ₁ (modAddr "ELEMS") (.num (.natN a)) :=
    evalExp_modAddr D rfl rfl rfl hM hA ha
  have ha' : a < Ls.length := (List.getElem?_eq_some_iff.1 ht).1
  refine evalExp_updE_iff.2 ⟨S, .list rs, evalExp_sof D rfl (evalExp_var rfl),
    Equiv.Execution.evalExp_iterPat (by decide) rfl, ?_⟩
  exact pathSet_dot (pathGet_idx (pathGet_dot pathGet_root hS) hidx ht) ht'
    (pathSet_idx (pathGet_dot pathGet_root hS) hidx (by simp [Value.setIdx, ha'])
      (pathSet_dot pathGet_root hS' pathSet_root))

/-- `$with_data(z, x, b*)`: the `BYTES` of the segment the module lists at `n` become `b*`. -/
theorem evalExp_withData {eb : Exp} {M t t' S' : Value} {Ls As bs : List Value} {a : Nat}
    (hρ : ρ.findDef? "with_data" = none) (hz : EvalExp env ρ ez (stV S F))
    (hx : EvalExp env ρ ex (idxV n)) (hb : EvalExp env ρ eb (.list bs))
    (hS : S.field? "DATAS" = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? "DATAS" = some (.list As)) (ha : As[n]? = some (.num (.natN a)))
    (ht : Ls[a]? = some t) (ht' : t.setField "BYTES" (.list bs) = some t')
    (hS' : S.setField "DATAS" (.list (Ls.set a t')) = some S') :
    EvalExp env ρ (.callE "with_data" [.expA ez, .expA ex, .expA eb]) (stV S' F) := by
  refine evalExp_call1 D.withData hρ
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons hb evalArgs_nil)))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA
        (matchExp_iterVar rfl (by decide) rfl)) matchArgs_nil))) ?_
  refine evalExp_case (evalExp_tup2 ?_ (evalExp_fof D rfl (evalExp_var rfl)))
  let ρ₁ := ((VarEnv.empty.bindVal "z" (stV S F)).bindVal "x" (idxV n)).bindVal "b*" (.list bs)
  have hidx : EvalExp env ρ₁ (modAddr "DATAS") (.num (.natN a)) :=
    evalExp_modAddr D rfl rfl rfl hM hA ha
  have ha' : a < Ls.length := (List.getElem?_eq_some_iff.1 ht).1
  refine evalExp_updE_iff.2 ⟨S, .list bs, evalExp_sof D rfl (evalExp_var rfl),
    Equiv.Execution.evalExp_iterPat (by decide) rfl, ?_⟩
  exact pathSet_dot (pathGet_idx (pathGet_dot pathGet_root hS) hidx ht) ht'
    (pathSet_idx (pathGet_dot pathGet_root hS) hidx (by simp [Value.setIdx, ha'])
      (pathSet_dot pathGet_root hS' pathSet_root))

end Accessors

/-! ## The environment facts, for every `simEnv B` -/

set_option maxRecDepth 100000 in
/-- `baseEnv` has the accessor definitions `StateDefs` names. -/
theorem stateDefs_baseEnv : StateDefs baseEnv :=
  ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩,
    ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩,
    ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩

/-- Installing builtins keeps a definition. -/
theorem HasClause1.withBuiltins {env : Env} {x : IL.Id} {pats : List Arg} {body : Exp}
    (h : HasClause1 env x pats body) (B : Builtins) : HasClause1 (env.withBuiltins B) x pats body := by
  obtain ⟨ps, t, q, h⟩ := h
  exact ⟨ps, t, q, by rw [Env.findDef?_withBuiltins, h]⟩

/-- So has every `simEnv B`: builtins do not change the definitions. -/
theorem stateDefs_simEnv (B : Builtins) : StateDefs (simEnv B) :=
  let D := stateDefs_baseEnv
  ⟨D.store.withBuiltins B, D.frame.withBuiltins B, D.sof.withBuiltins B, D.fof.withBuiltins B,
    D.local_.withBuiltins B, D.global.withBuiltins B, D.mem.withBuiltins B,
    D.table.withBuiltins B, D.data.withBuiltins B, D.elem.withBuiltins B,
    D.withLocal.withBuiltins B, D.withTable.withBuiltins B, D.withElem.withBuiltins B,
    D.withData.withBuiltins B, D.withGlobal.withBuiltins B⟩

end Silmaril.Wasm.SpecTec.Sim.State
