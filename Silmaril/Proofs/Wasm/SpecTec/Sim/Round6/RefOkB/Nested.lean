module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkB.Derive

/-!
# Round 6: `RefOkBB` is false, at round 5's nested type

Round 5 (`Round5.RefOk.refOkAt_nested_null`) found the nested type
`REF NULL D_out` no counterexample to `RefOkB` only because `Ref_ok/sub` never fired under
`DDerives`. Under `DDerivesB` it fires, and the two type systems disagree on the type itself:

* `D_in := _DEF (REC (SUB FINAL (STRUCT (CONST (REF NULL (REC 1)))))) 0` refers past its own
  one-member group;
* `D_out := _DEF (REC (SUB FINAL (STRUCT (CONST (REF NULL D_in))))) 0` contains it.

Core's `Deftype_ok` checks a group under `TypeCtx.withRecs`, which **replaces** `RECS`, so inside
`D_in` the `REC 1` is unbound and `TyOk {} (REF NULL D_out)` fails
(`Round5.RefOk.not_tyOk_nested`). SpecTec's `Deftype_ok` checks it under `{RECS st} ⊕ C`, which
**appends** (`Value.comp?`): inside `D_in`, nested in `D_out`, `RECS = [st_in, st_out]` and
`REC 1` is `st_out`. So:

* `dderivesB_reftypeOk_nested`: `Reftype_ok {} (REF NULL D_out)` under `DDerivesB`;
* `dderivesB_refOk_nested`: `Ref_ok s (REF.NULL_ADDR) (REF NULL D_out)` on every typed store,
  under every reading of `otherwise` (through `Ref_ok/sub`, from `Ref_ok/null`);
* `not_refOkAtB_nested`, `not_refOkBB`: Core does not type `null` there, so `RefOkAtB` fails at
  `REF NULL D_out` on every typed store, and **`RefOkBB (simEnv B)` is false for every `B`**.

The type is bounded (`Round4.tyBnd`) but not Core-valid: the disagreement is SpecTec accepting
a type Core rejects.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV natV nullV mutV)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Round5.RefOk (stIn stOut dIn dOut nestedRT)

variable {B : Builtins}

/-! ## The shape of both members -/

/-- `SUB FINAL (STRUCT (CONST (REF NULL u)))`: the shape of both members. -/
def stOf (u : CTypeUse) : CSubType :=
  .sub true .nil (.struct (.cons (.field .const (.val (.refv (.ref true (.use u))))) .nil))

/-- The one-member group of `stOf u`, as a defined type. -/
def defOf (u : CTypeUse) : DefType := .defn (.group (.cons (stOf u) .nil)) 0

theorem stIn_eq : stIn = stOf (.recv 1) := rfl

theorem stOut_eq : stOut = stOf (.dt dIn) := rfl

theorem dIn_eq : dIn = defOf (.recv 1) := rfl

theorem dOut_eq : dOut = defOf (.dt dIn) := rfl

/-- `stOf u` is as bounded as `u`. -/
theorem tyBnd_stOf {u : CTypeUse} (hu : Round4.tyBnd u = true) : Round4.tyBnd (stOf u) = true := by
  simp [stOf, Round4.tyBnd, hu]

/-- **`Subtype_ok2 C (stOf u) OK(0)`**, from `Heaptype_ok C u`: through `Comptype_ok/struct`,
`Fieldtype_ok`, `Storagetype_ok/val`, `Valtype_ok/ref` and `Reftype_ok`. -/
theorem dderivesB_stOf (O : ElseI) {c : Value} (hc : TypedV (simEnv B) (.varT "context" []) c)
    {u : CTypeUse} (hu : Round4.tyBnd u = true)
    (hh : DDerivesB (simEnv B) O "Heaptype_ok" "%|-%:OK" [] (.tuple [c, tyV u])) :
    DDerivesB (simEnv B) O "Subtype_ok2" "%|-%:%" [] (.tuple [c, tyV (stOf u), .case "OK" (natV 0)]) :=
  have hb : Round4.tyBnd (stOf u) = true := tyBnd_stOf hu
  have hR : Round5.Pos.TyT B .ref (tyV (Ty.ref true (.use u) : CRefType)) :=
    Round5.Pos.tyT_tyV _ (by simpa [stOf, Round4.tyBnd] using hb)
  have hF : TypedV (simEnv B) (.varT "fieldtype" [])
      (tyV (Ty.field .const (.val (.refv (.ref true (.use u)))) : CFieldType)) :=
    Round5.Pos.tyT_tyV (B := B) (Ty.field .const (.val (.refv (.ref true (.use u)))) : CFieldType)
      (by simpa [stOf, Round4.tyBnd] using hb)
  have hS : TypedV (simEnv B) (.varT "comptype" [])
      (tyV (Ty.struct (.cons (.field .const (.val (.refv (.ref true (.use u))))) .nil) : CCompType)) :=
    Round5.Pos.tyT_tyV (B := B)
      (Ty.struct (.cons (.field .const (.val (.refv (.ref true (.use u))))) .nil) : CCompType)
      (by simpa [stOf, Round4.tyBnd] using hb)
  have r₁ := dderivesB_reftypeOk O hc (Round5.Pos.tyT_tyV (Ty.use u) hu) true hh
  have r₂ := dderivesB_storagetypeOkVal O hc hR.2.1 (dderivesB_valtypeOkRef O hc hR.1 r₁)
  dderivesB_subtypeOk2 O true 0 hc hS
    (dderivesB_comptypeOkStruct1 O hc hF (dderivesB_fieldtypeOk O hc hR.2.2 .const r₂))

/-- **`Deftype_ok (ctxR l) (defOf u)`**, from `Heaptype_ok` of `u` in the context the group is
checked in, `ctxR (stOf u :: l)` (SpecTec's appended `RECS`). -/
theorem dderivesB_defOf (O : ElseI) {l : List Value}
    (hl : ∀ v ∈ l, TypedV (simEnv B) (.varT "subtype" []) v) {u : CTypeUse}
    (hu : Round4.tyBnd u = true)
    (hh : DDerivesB (simEnv B) O "Heaptype_ok" "%|-%:OK" [] (.tuple [ctxR (tyV (stOf u) :: l), tyV u])) :
    DDerivesB (simEnv B) O "Deftype_ok" "%|-%:OK" [] (.tuple [ctxR l, tyV (defOf u)]) :=
  have hst : TypedV (simEnv B) (.varT "subtype" []) (tyV (stOf u)) :=
    Round5.Pos.tyT_tyV (B := B) (stOf u) (tyBnd_stOf hu)
  have hg : TypedV (simEnv B) (.varT "rectype" []) (tyV (Ty.group (.cons (stOf u) .nil))) :=
    Round5.Pos.tyT_tyV (B := B) (Ty.group (.cons (stOf u) .nil) : CRecType)
      (by simpa [Round4.tyBnd] using tyBnd_stOf hu)
  have hc' : TypedV (simEnv B) (.varT "context" []) (ctxR (tyV (stOf u) :: l)) :=
    typedV_ctxR fun v hv => (List.mem_cons.1 hv).elim (fun e => e ▸ hst) (hl v)
  dderivesB_deftypeOk1 O (typedV_ctxR hl) hg hst
    (dderivesB_rectypeOk2Cons O 0 hc' hst (fun _ h => absurd h List.not_mem_nil)
      (dderivesB_stOf O hc' hu hh) (dderivesB_rectypeOk2Empty O 1 hc'))

/-- `Heaptype_ok` of a defined type, from `Deftype_ok`. -/
theorem dderivesB_heaptypeOk_def (O : ElseI) {c : Value}
    (hc : TypedV (simEnv B) (.varT "context" []) c) {d : DefType} (hb : Round4.tyBnd d = true)
    (hd : DDerivesB (simEnv B) O "Deftype_ok" "%|-%:OK" [] (.tuple [c, tyV d])) :
    DDerivesB (simEnv B) O "Heaptype_ok" "%|-%:OK" [] (.tuple [c, tyV d]) :=
  have hT : Round5.Pos.TyT B .def (tyV d) := Round5.Pos.tyT_tyV d hb
  dderivesB_heaptypeOkUse O hc hT.2.1 (dderivesB_typeuseOkDef O hc hT.1 hd)

/-! ## The nested type -/

/-- **SpecTec (under `DDerivesB`) accepts `REF NULL D_out` in `{}`**; Core does not
(`Round5.RefOk.not_tyOk_nested`). -/
theorem dderivesB_reftypeOk_nested (O : ElseI) :
    DDerivesB (simEnv B) O "Reftype_ok" "%|-%:OK" [] (.tuple [ctx0V, tyV nestedRT]) :=
  have hOut : TypedV (simEnv B) (.varT "subtype" []) (tyV stOut) :=
    Round5.Pos.tyT_tyV (B := B) stOut rfl
  have hIn : TypedV (simEnv B) (.varT "subtype" []) (tyV stIn) :=
    Round5.Pos.tyT_tyV (B := B) stIn rfl
  have hl₂ : ∀ v ∈ [tyV stIn, tyV stOut], TypedV (simEnv B) (.varT "subtype" []) v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl)
    · exact hIn
    · exact hOut
  have hl₁ : ∀ v ∈ [tyV stOut], TypedV (simEnv B) (.varT "subtype" []) v := by
    simp only [List.mem_singleton]
    rintro v rfl
    exact hOut
  -- inside `D_in`, nested in `D_out`: `RECS = [st_in, st_out]`, and `REC 1` is `st_out`
  have hRec : DDerivesB (simEnv B) O "Heaptype_ok" "%|-%:OK" []
      (.tuple [ctxR [tyV stIn, tyV stOut], tyV (Ty.recv 1 : CTypeUse)]) :=
    dderivesB_heaptypeOkUse O (typedV_ctxR hl₂) (Round5.Pos.tyT_tyV (Ty.recv 1 : CTypeUse) rfl).1
      (dderivesB_typeuseOkRec O (typedV_ctxR hl₂) hOut rfl)
  have hDIn : DDerivesB (simEnv B) O "Deftype_ok" "%|-%:OK" [] (.tuple [ctxR [tyV stOut], tyV dIn]) :=
    dderivesB_defOf O hl₁ rfl hRec
  have hDOut : DDerivesB (simEnv B) O "Deftype_ok" "%|-%:OK" [] (.tuple [ctxR [], tyV dOut]) :=
    dderivesB_defOf O (fun _ h => absurd h List.not_mem_nil) (u := .dt dIn) rfl
      (dderivesB_heaptypeOk_def O (typedV_ctxR hl₁) rfl hDIn)
  dderivesB_reftypeOk O typedV_ctx0 (typedV_heaptype rfl) true
    (dderivesB_heaptypeOk_def O typedV_ctx0 rfl hDOut)

/-- `Ref_ok/null` and `Ref_ok/sub`: SpecTec types `null` at `REF NULL ht` whenever
`Reftype_ok {} (REF NULL ht)` holds, on every typed store. -/
theorem dderivesB_refOk_null_of (O : ElseI) {sv : Value} (hs : TypedV (simEnv B) storeT sv)
    {h : CHeapType} (hb : Round4.tyBnd h = true)
    (hok : DDerivesB (simEnv B) O "Reftype_ok" "%|-%:OK" []
      (.tuple [ctx0V, tyV (Ty.ref true h : CRefType)])) :
    DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" [] (.tuple [sv, refToValue .null,
      tyV (Ty.ref true h : CRefType)]) := by
  have hbot : TypedV (simEnv B) (.varT "reftype" []) (tyV (Ty.ref true .bot : CRefType)) :=
    typedV_reftype rfl
  have hsub : DDerivesB (simEnv B) O "Reftype_sub" "%|-%<:%" []
      (.tuple [ctx0V, tyV (Ty.ref true .bot : CRefType), tyV (Ty.ref true h : CRefType)]) :=
    dderivesB_reftypeSub_null O typedV_ctx0 (typedV_heaptype rfl) (typedV_heaptype hb) true
      (dderivesB_heaptypeSub_bot O typedV_ctx0 (typedV_heaptype hb))
  exact dderivesB_of_ruleAt ruleAt_refOkSub (self_mem_conclAlts _)
    [("s", sv), ("ref", refToValue .null), ("rt", tyV (Ty.ref true h : CRefType)),
      ("rt'", tyV (Ty.ref true .bot : CRefType))]
    (QuantsOk.cons rfl (hs _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Typing.typedV_ref .null _ (valsOnly_bind _)) (QuantsOk.cons rfl
        (typedV_reftype hb _ (valsOnly_bind _)) (QuantsOk.cons rfl (hbot _ (valsOnly_bind _))
          QuantsOk.nil))))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl))
    (premsB_cons (.rulePr (evalArgs_nil _ _)
        (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl))
        (dderivesB_refOk_null O hs)) <|
      premsB_cons (.rulePr (evalArgs_nil _ _) (evalExp_tup2 evalExp_ctx0 (evalExp_var rfl)) hok) <|
      premsB_cons (.rulePr (evalArgs_nil _ _)
        (evalExp_tup3 evalExp_ctx0 (evalExp_var rfl) (evalExp_var rfl)) hsub) premsB_nil)

/-- **SpecTec types `null` at `REF NULL D_out`** under `DDerivesB`, on every typed store and
under every reading of `otherwise`. -/
theorem dderivesB_refOk_nested (O : ElseI) {sv : Value} (hs : TypedV (simEnv B) storeT sv) :
    DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" [] (.tuple [sv, refToValue .null, tyV nestedRT]) :=
  dderivesB_refOk_null_of O hs (h := .use (.dt dOut)) rfl (dderivesB_reftypeOk_nested O)

/-- `REF NULL D_out` is bounded. -/
theorem tyBnd_nested : Round4.tyBnd nestedRT = true := rfl

section Refute

variable {H : Type}

/-- **`RefOkAtB` fails at `REF NULL D_out`** on every store with a typed image: SpecTec types
`null` there, Core does not (`Round5.RefOk.not_refOk_null_nested`). -/
theorem not_refOkAtB_nested (hn : H → String) (s : Store H)
    (hs : TypedV (simEnv B) storeT (storeV hn s)) : ¬ RefOkAtB (simEnv B) hn s nestedRT :=
  fun K => Round5.RefOk.not_refOk_null_nested s ((K noElse .null).1 (dderivesB_refOk_nested _ hs))

end Refute

/-- **`RefOkBB (simEnv B)` is false, for every `B`**: at the empty store (whose image is typed)
and the bounded type `REF NULL D_out`. -/
theorem not_refOkBB (B : Builtins) : ¬ RefOkBB (simEnv B) := fun K =>
  not_refOkAtB_nested (B := B) (id : String → String) {} (Round5.RefOk.typedV_storeEmpty B id)
    (K.refOk id {} nestedRT (Round5.RefOk.typedV_storeEmpty B id) tyBnd_nested)

end Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB
