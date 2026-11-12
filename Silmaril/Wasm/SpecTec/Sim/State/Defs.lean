module

public import Silmaril.Wasm.SpecTec.Sim.Defs

/-!
# SpecTec ↔ Core 3.0, family M (state): definitions

Family M of `docs/projects/spectec/README.md` covers the Core constructors `Step.variable` (`local.*`,
`global.*`), `Step.table` and `Step.memory`, and the SpecTec rules `Step_pure` 30, `Step_read`
23–62 and `Step` 11–28.

Every one of these rules reads or writes the state through the spec's accessor functions
(`$local`, `$global`, `$table`, `$mem`, `$elem`, `$data`, their `$with_*` updaters, and the
projections `$sof`/`$fof`/`$store`/`$frame`). They are *defined* functions of the script, so the
proofs evaluate them clause by clause; `HasClause1` names the one fact about the environment that
evaluation needs (the definition has a single premise-free clause with the given patterns and
body), and `StateDefs` collects those facts. `stateDefs_simEnv` proves them for every `simEnv B` by
computation.

`StateTyping` collects the typing facts about encoded immediates that the rules' quantifiers need
(`QuantsOk`). They are statements about the encoding alone, of the kind family E (encoding/typing)
owns, and the per-rule theorems take them as hypotheses.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.State

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- The IL type `idx`. -/
abbrev idxT : Typ := .varT "idx" []
/-- The IL type `val`. -/
abbrev valT : Typ := .varT "val" []

/-- The IL type `addrtype`. -/
abbrev addrtypeT : Typ := .varT "addrtype" []
/-- The IL type `ref`. -/
abbrev refT : Typ := .varT "ref" []
/-- The IL type `num_(y)`, for an address-type variable `y` (`num_(at)` in the rules). -/
abbrev numAtT (y : IL.Id) : Typ :=
  .varT "num_" [.expA (.subE (.varE y) (.varT "addrtype" []) (.varT "numtype" []))]
/-- The IL type `num_(I32)`. -/
abbrev num32T : Typ := .varT "num_" [.expA (.caseE "I32" (.tupE []))]

/-- A `%`-wrapped numeral: the encoding of an index (`Encode.toValue` on `Idx`). -/
abbrev idxV (n : Nat) : Value := .case "%" (.tuple [.num (.natN n)])

/-- The definition `x` of `env` has exactly one clause, with no premises, argument patterns `pats`
and body `body`. -/
def HasClause1 (env : Env) (x : IL.Id) (pats : List Arg) (body : Exp) : Prop :=
  ∃ ps t q, env.findDef? x = some (ps, t, [.defD q pats body []])

/-- `(s; f)`, the argument pattern of `$store` and `$frame`. -/
abbrev statePat : List Arg := [.expA (.caseE "%;%" (.tupE [.varE "s", .varE "f"]))]

/-- `z`, the argument pattern of `$sof` and `$fof`. -/
abbrev zPat : List Arg := [.expA (.varE "z")]

/-- `z, x`, the argument pattern of the accessors. -/
abbrev zxPat : List Arg := [.expA (.varE "z"), .expA (.varE "x")]

/-- `z, x, v`, the argument pattern of `$with_local` and `$with_global`. -/
abbrev zxvPat : List Arg := [.expA (.varE "z"), .expA (.varE "x"), .expA (.varE "v")]

/-- `x!%.0`: the payload of a `%`-wrapped index. -/
abbrev idxPayload : Exp := .projE (.uncaseE (.varE "x") "%") 0

/-- `$fof(z).MODULE.F[x!%.0]`: the address the current module lists at index `x` of field `F`. -/
def modAddr (F : AtomS) : Exp :=
  .idxE (.dotE (.dotE (.callE "fof" [.expA (.varE "z")]) "MODULE") F) idxPayload

/-- `z, x, i, r`, the argument pattern of `$with_table`. -/
abbrev zxirPat : List Arg := [.expA (.varE "z"), .expA (.varE "x"), .expA (.varE "i"), .expA (.varE "r")]

/-- `y*` as a pattern or expression: the list variable `ys` iterated element-wise as `y`. -/
abbrev iterVar (y ys : IL.Id) : Exp := .iterE (.varE y) (.mk .list [.mk y (.varE ys)])

/-- The body of the store accessor for the field `F` (`GLOBALS`, `MEMS`, …):
`$sof(z).F[$fof(z).MODULE.F[x!%.0]]`. -/
def storeAccBody (F : AtomS) : Exp :=
  .idxE (.dotE (.callE "sof" [.expA (.varE "z")]) F)
    (.idxE (.dotE (.dotE (.callE "fof" [.expA (.varE "z")]) "MODULE") F) idxPayload)

/-- The environment facts the state rules evaluate through. -/
structure StateDefs (env : Env) : Prop where
  /-- `$store((s; f)) = s`. -/
  store : HasClause1 env "store" statePat (.varE "s")
  /-- `$frame((s; f)) = f`. -/
  frame : HasClause1 env "frame" statePat (.varE "f")
  /-- `$sof(z) = $store(z)`. -/
  sof : HasClause1 env "sof" zPat (.callE "store" [.expA (.varE "z")])
  /-- `$fof(z) = $frame(z)`. -/
  fof : HasClause1 env "fof" zPat (.callE "frame" [.expA (.varE "z")])
  /-- `$local(z, x) = $fof(z).LOCALS[x!%.0]`. -/
  local_ : HasClause1 env "local" zxPat
    (.idxE (.dotE (.callE "fof" [.expA (.varE "z")]) "LOCALS") idxPayload)
  /-- `$global(z, x)`. -/
  global : HasClause1 env "global" zxPat (storeAccBody "GLOBALS")
  /-- `$mem(z, x)`. -/
  mem : HasClause1 env "mem" zxPat (storeAccBody "MEMS")
  /-- `$table(z, x)`. -/
  table : HasClause1 env "table" zxPat (storeAccBody "TABLES")
  /-- `$data(z, x)`. -/
  data : HasClause1 env "data" zxPat (storeAccBody "DATAS")
  /-- `$elem(z, x)`. -/
  elem : HasClause1 env "elem" zxPat (storeAccBody "ELEMS")
  /-- `$with_local(z, x, v) = $sof(z); $fof(z)[.LOCALS[x!%.0] = ?(v)]`. -/
  withLocal : HasClause1 env "with_local" zxvPat
    (.caseE "%;%" (.tupE [.callE "sof" [.expA (.varE "z")],
      .updE (.callE "fof" [.expA (.varE "z")]) (.idxP (.dotP .rootP "LOCALS") idxPayload)
        (.optE (some (.varE "v")))]))
  /-- `$with_table(z, x, i, r) = $sof(z)[.TABLES[…].REFS[i] = r]; $fof(z)`. -/
  withTable : HasClause1 env "with_table" zxirPat
    (.caseE "%;%" (.tupE [.updE (.callE "sof" [.expA (.varE "z")])
        (.idxP (.dotP (.idxP (.dotP .rootP "TABLES") (modAddr "TABLES")) "REFS") (.varE "i"))
        (.varE "r"),
      .callE "fof" [.expA (.varE "z")]]))
  /-- `$with_elem(z, x, r*) = $sof(z)[.ELEMS[…].REFS = r*]; $fof(z)`. -/
  withElem : HasClause1 env "with_elem" [.expA (.varE "z"), .expA (.varE "x"), .expA (iterVar "r" "r*")]
    (.caseE "%;%" (.tupE [.updE (.callE "sof" [.expA (.varE "z")])
        (.dotP (.idxP (.dotP .rootP "ELEMS") (modAddr "ELEMS")) "REFS") (iterVar "r" "r*"),
      .callE "fof" [.expA (.varE "z")]]))
  /-- `$with_data(z, x, b*) = $sof(z)[.DATAS[…].BYTES = b*]; $fof(z)`. -/
  withData : HasClause1 env "with_data" [.expA (.varE "z"), .expA (.varE "x"), .expA (iterVar "b" "b*")]
    (.caseE "%;%" (.tupE [.updE (.callE "sof" [.expA (.varE "z")])
        (.dotP (.idxP (.dotP .rootP "DATAS") (modAddr "DATAS")) "BYTES") (iterVar "b" "b*"),
      .callE "fof" [.expA (.varE "z")]]))
  /-- `$with_global(z, x, v) = $sof(z)[.GLOBALS[$fof(z).MODULE.GLOBALS[x!%.0]].VALUE = v]; $fof(z)`. -/
  withGlobal : HasClause1 env "with_global" zxvPat
    (.caseE "%;%" (.tupE [.updE (.callE "sof" [.expA (.varE "z")])
        (.dotP (.idxP (.dotP .rootP "GLOBALS")
          (.idxE (.dotE (.dotE (.callE "fof" [.expA (.varE "z")]) "MODULE") "GLOBALS")
            idxPayload)) "VALUE") (.varE "v"),
      .callE "fof" [.expA (.varE "z")]]))

/-- The numeric definitions the `grow-fail` rules evaluate: `$size` (its `I32` and `I64`
clauses first) and the numerics of `Equiv.NumEnv` (for `$inv_signed_`). -/
structure GrowDefs (env : Env) : Prop where
  /-- `$size(I32) = 32`, `$size(I64) = 64`, then the float clauses. -/
  size : ∃ ps t rest, env.findDef? "size" = some (ps, t,
    .defD [] [.expA (.caseE "I32" (.tupE []))] (.numE (.natN 32)) [] ::
    .defD [] [.expA (.caseE "I64" (.tupE []))] (.numE (.natN 64)) [] :: rest)
  /-- `$bool`, `$signed_`, `$inv_signed_`, … -/
  num : Equiv.NumEnv env

/-- Typing facts about encoded immediates that the state rules' quantifiers need. Statements
about the encoding alone (family E's subject); the per-rule theorems take them as hypotheses. -/
structure StateTyping (env : Env) : Prop where
  /-- Every `u32` index, `%`-wrapped, is an `idx`. -/
  idx : ∀ n : Nat, n < 2 ^ 32 → TypedV env idxT (idxV n)
  /-- Every address type is an `addrtype`. -/
  addr : ∀ a : Silmaril.Wasm.AddrType, TypedV env addrtypeT (Encode.toValue a)
  /-- An address-typed operand `i`, in a scope binding its address type `y` to `a`, has type
  `num_(y)`. -/
  num : ∀ (y : IL.Id) (a : Silmaril.Wasm.AddrType) (b : BitVec a.intType.width) (ρ : VarEnv),
    ValsOnly ρ → ρ.findVal? y = some (Encode.toValue a) → HasTyp env ρ (numAtT y) (idxV b.toNat)
  /-- An `i32` operand has type `num_(I32)`. -/
  num32 : ∀ b : BitVec 32, TypedV env num32T (idxV b.toNat)
  /-- A natural number is an `n`. -/
  nat : ∀ k : Nat, TypedV env nT (.num (.natN k))
  /-- A reference typed as a `val` is typed as a `ref`. -/
  ref : ∀ r : Silmaril.Wasm.Execution.Core.Ref,
    TypedV env valT (Equiv.RuntimeBridge.refToValue r) →
      TypedV env refT (Equiv.RuntimeBridge.refToValue r)

/-- Decoders the backward direction of the state rules needs: which Core instruction a SpecTec
instruction value is the image of. Facts about the encoding alone (family E's subject); the
backward theorems take them as hypotheses. -/
structure StateDecode (env : Env) : Prop where
  /-- An administrative instruction whose image is a typed `val` is a value. -/
  val : ∀ (a : Silmaril.Wasm.Execution.Core.Admin) (ρ : VarEnv), ValsOnly ρ →
    HasTyp env ρ valT (adminToV a) → ∃ v : Silmaril.Wasm.Execution.Core.Val, a = v.toAdmin
  /-- The only image tagged `LOCAL.TEE` is `local.tee`'s. -/
  localTee : ∀ (a : Silmaril.Wasm.Execution.Core.Admin) (X : Value),
    adminToV a = .case "LOCAL.TEE" X → ∃ x : Silmaril.Wasm.LocalIdx,
      a = .plain (.localTee x) ∧ X = idxV x.toNat

end Silmaril.Wasm.SpecTec.Sim.State
