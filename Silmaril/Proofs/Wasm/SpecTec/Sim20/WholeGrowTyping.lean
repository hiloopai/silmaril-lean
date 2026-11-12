module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeGrowB
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.NumTyping

/-!
# Every V2 table and memory instance is an IL `tableinst`/`meminst` of the 2.0 script

The two `grow-succeed` rules of the wasm-2.0 script quantify the grown instance
(`ti : tableinst`, `mi : meminst`). To fire them forward, the image of V2's grown instance must be
IL-typed. It is, and without any hypothesis: V2's limits are `Fin (2 ^ 32)`, so they are `u32`
(`typedV_limits20`), every reference is a `ref` (`typedV_ref20`), and every byte is a `byte`
(`hasTyp_byte20`). So every table instance is a `tableinst` (`typedV_tableInst20`) and every
memory instance a `meminst` (`typedV_memInst20`), in particular the grown ones.

The quantifiers the two rules share with the `grow-fail` rules are typed the same way: `n` is a
natural (`typedV_n20`), `x` an index (`typedV_idx20`). The state `z` is read off the typing of the
configuration (`typedV_state_of_typed20`).

Each definition is found by kernel `rfl` against `Scripts.Wasm20.Original`. The lemmas port round
5's `Pos.typedV_tableinst`/`typedV_meminst` (3.0) to `simEnv20 B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly stateT)
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d16)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

set_option maxRecDepth 100000

variable {B : Builtins}

/-! ## Generic shapes, at any environment -/

/-- A closed alias, as `TypedV`. -/
theorem typedV_aliasG {env : Env} {x : IL.Id} {t : Typ}
    (htd : env.findTyp? x = some ([], [.instD [] [] (.aliasT t)]))
    {v : Value} (h : HasTyp env VarEnv.empty t v) : TypedV env (.varT x []) v :=
  fun ρ hρ =>
    hasTyp_varT_of_insts (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) htd Equiv.evalArgs_nil
      (hasTypInsts_head matchArgs_nil (hasTypDef_aliasT_iff.2 h))

/-- A closed record, field by field. -/
theorem typedV_structG {env : Env} {x : IL.Id} {fs : List TypField} {gs : List (AtomS × Value)}
    (htd : env.findTyp? x = some ([], [.instD [] [] (.structT fs)]))
    (hf : HasTypFields env VarEnv.empty fs gs) : TypedV env (.varT x []) (.struct gs) :=
  fun _ hρ => hasTyp_varT_struct (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) htd
    Equiv.evalArgs_nil matchArgs_nil hf

/-- A field without premises, then the rest. -/
theorem hasTypFields_consG {env : Env} {a : AtomS} {t : Typ} {fs : List TypField} {v : Value}
    {gs : List (AtomS × Value)} (hv : TypedV env t v)
    (hr : HasTypFields env VarEnv.empty fs gs) :
    HasTypFields env VarEnv.empty (.mk a t [] [] :: fs) ((a, v) :: gs) :=
  hasTypFields_cons_iff.2 ⟨_, _, rfl, hv _ ⟨rfl, rfl, rfl⟩, premsOk_nil, hr⟩

/-- The last field. -/
theorem hasTypFields_oneG {env : Env} {a : AtomS} {t : Typ} {v : Value} (hv : TypedV env t v) :
    HasTypFields env VarEnv.empty [.mk a t [] []] [(a, v)] :=
  hasTypFields_consG hv (hasTypFields_nil_iff.2 rfl)

/-- A pair of typed components. -/
theorem hasTyp_tup2G {env : Env} {a b : IL.Id} {τ₁ τ₂ : Typ} {u v : Value}
    (h₁ : TypedV env τ₁ u) (h₂ : TypedV env τ₂ v) :
    HasTyp env VarEnv.empty (.tupT [.mk a τ₁, .mk b τ₂]) (.tuple [u, v]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, h₁ _ ⟨rfl, rfl, rfl⟩,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, h₂ _ ⟨rfl, rfl, rfl⟩, hasTypTup_nil_iff.2 rfl⟩⟩⟩

/-- A natural, at the IL type `nat`. -/
theorem hasTyp_nat (env : Env) (ρ : VarEnv) (k : Nat) :
    HasTyp env ρ (.numT .natT) (.num (.natN k)) :=
  hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩

/-! ## The 2.0 type definitions -/

theorem findTyp_n20 : (simEnv20 B).findTyp? "n" =
    some ([], [.instD [] [] (.aliasT (.numT .natT))]) := rfl
theorem findTyp_addr20 : (simEnv20 B).findTyp? "addr" =
    some ([], [.instD [] [] (.aliasT (.numT .natT))]) := rfl
theorem findTyp_funcaddr20 : (simEnv20 B).findTyp? "funcaddr" =
    some ([], [.instD [] [] (.aliasT (.varT "addr" []))]) := rfl
theorem findTyp_hostaddr20 : (simEnv20 B).findTyp? "hostaddr" =
    some ([], [.instD [] [] (.aliasT (.varT "addr" []))]) := rfl
theorem findTyp_limits20 : (simEnv20 B).findTyp? "limits" = some ([], [.instD [] []
    (.variantT [.mk "[%..%]" (.tupT [.mk "u32" (.varT "u32" []),
      .mk "u32?" (.iterT (.varT "u32" []) .opt)]) [] []])]) := rfl
theorem findTyp_tabletype20 : (simEnv20 B).findTyp? "tabletype" = some ([], [.instD [] []
    (.variantT [.mk "%%" (.tupT [.mk "limits" (.varT "limits" []),
      .mk "reftype" (.varT "reftype" [])]) [] []])]) := rfl
theorem findTyp_memtype20 : (simEnv20 B).findTyp? "memtype" = some ([], [.instD [] []
    (.variantT [.mk "%PAGE" (.varT "limits" []) [] []])]) := rfl
theorem findTyp_tableinst20 : (simEnv20 B).findTyp? "tableinst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" (.varT "tabletype" []) [] [],
      .mk "REFS" (.iterT (.varT "ref" []) .list) [] []])]) := rfl
theorem findTyp_meminst20 : (simEnv20 B).findTyp? "meminst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" (.varT "memtype" []) [] [],
      .mk "BYTES" (.iterT (.varT "byte" []) .list) [] []])]) := rfl
theorem findTyp_byte20 : (simEnv20 B).findTyp? "byte" =
    some ([], [.instD [] [] (.variantT (Sim.IntNumeric.instCases Original.d16 0))]) := rfl
theorem findTyp_state20 : (simEnv20 B).findTyp? "state" = some ([], [.instD [] []
    (.variantT [.mk "%;%" (.tupT [.mk "store" (.varT "store" []), .mk "frame" (.varT "frame" [])])
      [] []])]) := rfl
theorem findTyp_config20 : (simEnv20 B).findTyp? "config" = some ([], [.instD [] []
    (.variantT [.mk "%;%" (.tupT [.mk "state" (.varT "state" []),
      .mk "admininstr*" (.iterT (.varT "admininstr" []) .list)]) [] []])]) := rfl

/-! ## Scalars -/

/-- `n` holds every natural. -/
theorem typedV_n20 (k : Nat) : TypedV (simEnv20 B) (.varT "n" []) (.num (.natN k)) :=
  typedV_aliasG findTyp_n20 (hasTyp_nat _ _ k)

/-- `addr` holds every natural. -/
theorem typedV_addr20 (k : Nat) : TypedV (simEnv20 B) (.varT "addr" []) (.num (.natN k)) :=
  typedV_aliasG findTyp_addr20 (hasTyp_nat _ _ k)

/-- `u32` holds every natural below `2 ^ 32`. -/
theorem typedV_u32_20 {k : Nat} (hk : k < 2 ^ 32) :
    TypedV (simEnv20 B) (.varT "u32" []) (pctV k) :=
  typedV_aliasG Pure.findTyp_u32_20 (Pure.hasTyp_uN20 evalExp_num hk)

/-- Every index is an `idx`. -/
theorem typedV_idx20 {k : IndexKind} (x : Idx k) : TypedV (simEnv20 B) (.varT "idx" []) (idxV x) :=
  typedV_aliasG Pure.findTyp_idx20 (typedV_u32_20 x.value.isLt _ ⟨rfl, rfl, rfl⟩)

/-- **Every reference is a `ref`.** -/
theorem typedV_ref20 (r : Ref) : TypedV (simEnv20 B) State.refT (refV r) := by
  cases r with
  | null t => exact typedV_refNull20 t
  | funcAddr a =>
    exact Pure.typedV_closedCase20 findTyp_ref20 rfl
      (typedV_aliasG findTyp_funcaddr20 (typedV_addr20 a _ ⟨rfl, rfl, rfl⟩) _ ⟨rfl, rfl, rfl⟩)
  | hostAddr a =>
    exact Pure.typedV_closedCase20 findTyp_ref20 rfl
      (typedV_aliasG findTyp_hostaddr20 (typedV_addr20 a _ ⟨rfl, rfl, rfl⟩) _ ⟨rfl, rfl, rfl⟩)

/-- `byte` holds every natural below `256` (round 5's `FwdMem.hasTyp_byte`, ported). -/
theorem hasTyp_byte20 {ρ : VarEnv} (hρ : ValsOnly ρ) {n : Nat} (hn : n < 256) :
    HasTyp (simEnv20 B) ρ (.varT "byte" []) (pctV n) := by
  have hl : localTyp? ρ "byte" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  have htup : HasTyp (simEnv20 B) VarEnv.empty (.tupT [.mk "i" (.numT .natT)])
      (.tuple [.num (.natN n)]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_nat _ _ n,
      hasTypTup_nil_iff.2 rfl⟩⟩
  refine hasTyp_varT_case hl findTyp_byte20 Equiv.evalArgs_nil matchArgs_nil
    (Sim.IntNumeric.hasTypCase_of_findCase rfl htup
      (Sim.IntNumeric.premsOk_if (Sim.IntNumeric.evalExp_and ?_ ?_)))
  · exact evalExp_cmpNum (evalExp_var (v := .num (.natN n)) rfl) evalExp_num
      (by simp [Num.cmp])
  · refine evalExp_cmpNum (evalExp_var (v := .num (.natN n)) rfl) evalExp_num ?_
    simp only [Num.cmp, Option.some.injEq, decide_eq_true_eq]
    omega

/-- An encoded byte string is a `byte*`. -/
theorem typedV_bytes20 (b : ByteArray) :
    TypedV (simEnv20 B) (.iterT (.varT "byte" []) .list) (bytesV b) := fun _ hρ =>
  hasTyp_iterT_list_iff.2 ⟨_, rfl, hasTypList_iff.2 fun w hw => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hw
    exact hasTyp_byte20 hρ c.toNat_lt⟩

/-! ## Types and instances -/

/-- **Every V2 limits pair is a `limits`**: both bounds are `Fin (2 ^ 32)`. -/
theorem typedV_limits20 (l : V2.Limits) : TypedV (simEnv20 B) (.varT "limits" []) (limitsV l) := by
  have hmax : TypedV (simEnv20 B) (.iterT (.varT "u32" []) .opt)
      (.opt (l.max.map fun m => pctV m.val)) := by
    rcases l.max with _ | m
    · exact fun _ _ => hasTyp_iterT_opt_iff.2 (.inl rfl)
    · exact fun ρ hρ => hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl, typedV_u32_20 m.isLt ρ hρ⟩)
  exact Pure.typedV_closedCase20 findTyp_limits20 rfl
    (hasTyp_tup2G (typedV_u32_20 l.min.isLt) hmax)

/-- Every table type is a `tabletype`. -/
theorem typedV_tableType20 (t : V2.TableType) :
    TypedV (simEnv20 B) (.varT "tabletype" []) (tableTypeV t) :=
  Pure.typedV_closedCase20 findTyp_tabletype20 rfl
    (hasTyp_tup2G (typedV_limits20 t.limits) (typedV_refType20 t.element))

/-- Every memory type is a `memtype`. -/
theorem typedV_memType20 (m : V2.MemoryType) :
    TypedV (simEnv20 B) (.varT "memtype" []) (memTypeV m) :=
  Pure.typedV_closedCase20 findTyp_memtype20 rfl (typedV_limits20 m.limits _ ⟨rfl, rfl, rfl⟩)

/-- **Every V2 table instance is a `tableinst`**, in particular every grown one. -/
theorem typedV_tableInst20 (ti : TableInst) :
    TypedV (simEnv20 B) (.varT "tableinst" []) (tableInstV ti) :=
  typedV_structG findTyp_tableinst20 (hasTypFields_consG (typedV_tableType20 ti.type)
    (hasTypFields_oneG (Sim.typedV_list_iff.2 fun u hu => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 hu
      exact typedV_ref20 r)))

/-- **Every V2 memory instance is a `meminst`**, in particular every grown one. -/
theorem typedV_memInst20 (mi : MemInst) :
    TypedV (simEnv20 B) (.varT "meminst" []) (memInstV mi) :=
  typedV_structG findTyp_meminst20 (hasTypFields_consG (typedV_memType20 mi.type)
    (hasTypFields_oneG (typedV_bytes20 mi.bytes)))

/-! ## The state of a typed configuration -/

/-- **The state of a configuration whose image is typed is typed.** -/
theorem typedV_state_of_typed20 {H : Type} {hn : H → String} {c : Config H}
    (h : Typed20 (simEnv20 B) hn c) :
    TypedV (simEnv20 B) stateT (stateV hn c.store c.frame) := by
  have hl : localTyp? VarEnv.empty "config" [] = none := rfl
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [findTyp_config20] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hrest
  · obtain rfl := Sim.IntNumeric.matchArgs_nil_scope hm
    obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1 hd
    obtain ⟨rfl, rfl⟩ : op = "%;%" ∧
        w = .tuple [stateV hn c.store c.frame, .list (adminsToV c.code)] := by
      simpa [configV] using he.symm
    obtain ⟨ht, -⟩ := (hasTypCase_cons_hit_iff rfl).1 hc
    obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 ht
    obtain rfl := (Value.tuple.inj hvs).symm
    obtain ⟨y, ys, hys, hy, -⟩ := hasTypTup_cons_iff.1 htup
    obtain ⟨rfl, -⟩ := List.cons.inj hys
    exact fun ρ hρ => Sim.IntNumeric.hasTyp_varT_nil_congr ⟨rfl, rfl, rfl⟩ hρ hy
  · exact absurd hrest not_hasTypInsts_nil

end Silmaril.Wasm.SpecTec.Sim20.Whole
