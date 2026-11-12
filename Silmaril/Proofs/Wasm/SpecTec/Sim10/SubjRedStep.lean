module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.SubjRedPure

/-!
# Subject reduction for every V1 step

**`ts10_step`**: every V1 step from a configuration whose state and code images are typed, and
which satisfies `GSetOk`, leads to a configuration whose images are typed, given `ValTyped10`
(every V1 value is a typed `val`). With it, pass 3's forward theorem drops the successor's
typing (`wholeStepFwd10_of_restR'`).

The state-changing steps rebuild the store field by field (`StoreTy10`):

* `global.set` writes a global instance whose `TYPE` is the old one, by `GSetOk`
  (`typedV_globalInst_set10`);
* `memory.grow` that succeeds writes a memory instance with the old maximum and at most `65536`
  pages (`typedV_memInst_grow10`); one that fails writes the old instance back;
* the new frame of `call_addr` has typed locals (`ValTyped10`) and the module of the callee's
  `funcinst`, and its body is the callee's `expr` (`typed_invokeFrame10`).

Host calls and stores do not arise: a typed state has no host function, and no 1.0 `STORE` is
typed (pass 2).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  expression frameMemory setGlobal setMemory)
open Silmaril.Wasm.Execution.Runtime (Frame GlobalInst MemInst ModuleInst FuncInst)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly stateT storeT frameT instrsT typedV_list_iff)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk)
open Silmaril.Wasm.SpecTec.Sim20.Whole (typedV_struct2 hasTyp_struct2_fst hasTyp_struct2_snd
  typedV_list_set20 typedV_list_of_empty20 typedV_of_empty20 typedV_of_getElem?
  hasTypFields_cons_nil_iff hasTypFields_of_closed)

set_option maxRecDepth 100000

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## The store, field by field -/

set_option maxRecDepth 8000000 in
theorem findTyp_storeF10 : (simEnv10 B).findTyp? "store" = some ([], [.instD [] []
    (.structT [.mk "FUNCS" (.iterT (.varT "funcinst" []) .list) [] [],
      .mk "GLOBALS" (.iterT (.varT "globalinst" []) .list) [] [],
      .mk "TABLES" (.iterT (.varT "tableinst" []) .list) [] [],
      .mk "MEMS" (.iterT (.varT "meminst" []) .list) [] []])]) := rfl

/-- **A store image is typed field by field.** -/
structure StoreTy10 (B : Builtins) (hn : H → String) (s : Store H) : Prop where
  funcs : TypedV (simEnv10 B) (.iterT (.varT "funcinst" []) .list) (.list (s.funcs.map (funcInstV hn)))
  globals : TypedV (simEnv10 B) (.iterT (.varT "globalinst" []) .list) (.list (s.globals.map globalInstV))
  tables : TypedV (simEnv10 B) (.iterT (.varT "tableinst" []) .list) (.list (s.tables.map tableInstV))
  mems : TypedV (simEnv10 B) (.iterT (.varT "meminst" []) .list) (.list (s.memories.map memInstV))

theorem typedV_storeV_iff10 {s : Store H} :
    TypedV (simEnv10 B) storeT (storeV hn s) ↔ StoreTy10 B hn s := by
  constructor
  · intro h
    have h₀ := hasTypFields_of_closed findTyp_storeF10 h
    obtain ⟨h₁, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
    obtain ⟨h₂, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
    obtain ⟨h₃, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
    obtain ⟨h₄, -⟩ := hasTypFields_cons_nil_iff.1 h₀
    exact ⟨typedV_list_of_empty20 h₁, typedV_list_of_empty20 h₂, typedV_list_of_empty20 h₃,
      typedV_list_of_empty20 h₄⟩
  · intro h
    exact Sim20.Whole.typedV_structG findTyp_storeF10 (Sim20.Whole.hasTypFields_consG h.funcs
      (Sim20.Whole.hasTypFields_consG h.globals (Sim20.Whole.hasTypFields_consG h.tables
        (Sim20.Whole.hasTypFields_oneG h.mems))))

/-- A typed state with its store replaced by another typed store. -/
theorem typedV_state_store10 {s s' : Store H} {f : Frame}
    (hz : TypedV (simEnv10 B) stateT (stateV hn s f)) (hs : StoreTy10 B hn s') :
    TypedV (simEnv10 B) stateT (stateV hn s' f) :=
  typedV_stV_iff10.2 ⟨typedV_storeV_iff10.2 hs, (typedV_stV_iff10.1 hz).2⟩

/-- The store of a typed state, field by field. -/
theorem storeTy10_of_state {s : Store H} {f : Frame}
    (hz : TypedV (simEnv10 B) stateT (stateV hn s f)) : StoreTy10 B hn s :=
  typedV_storeV_iff10.1 (typedV_stV_iff10.1 hz).1

/-! ## `global.set` -/

/-- **A global instance with a value of its type is typed.** -/
theorem typedV_globalInst_set10 {g : GlobalInst} {v : Execution.Runtime.Value}
    (hg : TypedV (simEnv10 B) (.varT "globalinst" []) (globalInstV g))
    (hv : TypedV (simEnv10 B) (.varT "val" []) (valV v)) (ht : v.type = g.value.type) :
    TypedV (simEnv10 B) (.varT "globalinst" []) (globalInstV {g with value := v}) := by
  have hT := hasTyp_struct2_fst findTyp_globalinst10 hg
  have e : globalTypeV g.mutability v.type = globalTypeV g.mutability g.value.type := by rw [ht]
  exact typedV_struct2 findTyp_globalinst10 (by simpa [globalInstV, e] using hT)
    (hv _ valsOnly_empty)

/-! ## `memory.grow` -/

set_option maxRecDepth 8000000 in
theorem findTyp_meminst10 : (simEnv10 B).findTyp? "meminst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" (.varT "memtype" []) [] [],
      .mk "BYTES" (.iterT (.varT "byte" []) .list) [] []])]) := rfl

set_option maxRecDepth 8000000 in
theorem findTyp_memtype10 : (simEnv10 B).findTyp? "memtype" =
    some ([], [.instD [] [] (.aliasT (.varT "limits" []))]) := rfl

set_option maxRecDepth 8000000 in
theorem findTyp_limits10 : (simEnv10 B).findTyp? "limits" = some ([], [.instD [] []
    (.variantT [.mk "[%..%]" (.tupT [.mk "u32" (.varT "u32" []),
      .mk "u32?" (.iterT (.varT "u32" []) .opt)]) [] []])]) := rfl

set_option maxRecDepth 8000000 in
theorem findTyp_byte10 : (simEnv10 B).findTyp? "byte" = some ([], [.instD [] []
    (.variantT [.mk "%" (.tupT [.mk "i" (.numT .natT)]) []
      [.ifPr (.binE .andOp .boolT (.cmpE .geOp (.numT .natT) (.varE "i") (.numE (.natN 0)))
        (.cmpE .leOp (.numT .natT) (.varE "i") (.numE (.natN 255))))]])]) := rfl

/-- `byte` holds every natural below `256` (2.0's `hasTyp_byte20`, ported). -/
theorem typedV_byte10 {n : Nat} (hn : n < 256) : TypedV (simEnv10 B) (.varT "byte" []) (pctV n) := by
  have htup : HasTyp (simEnv10 B) VarEnv.empty (.tupT [.mk "i" (.numT .natT)])
      (.tuple [.num (.natN n)]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, Sim20.Whole.hasTyp_nat _ _ n,
      hasTypTup_nil_iff.2 rfl⟩⟩
  refine fun ρ hρ => hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1])
    findTyp_byte10 Equiv.evalArgs_nil matchArgs_nil (Sim.IntNumeric.hasTypCase_of_findCase rfl htup
      (Sim.IntNumeric.premsOk_if (Sim.IntNumeric.evalExp_and ?_ ?_)))
  · exact evalExp_cmpNum (evalExp_var (v := .num (.natN n)) rfl) evalExp_num (by simp [Num.cmp])
  · refine evalExp_cmpNum (evalExp_var (v := .num (.natN n)) rfl) evalExp_num ?_
    simp only [Num.cmp, Option.some.injEq, decide_eq_true_eq]
    omega

/-- An encoded byte string is a `byte*`. -/
theorem typedV_bytes10 (b : ByteArray) :
    TypedV (simEnv10 B) (.iterT (.varT "byte" []) .list) (bytesV b) :=
  typedV_list_iff.2 fun w hw => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hw
    exact typedV_byte10 c.toNat_lt

/-- The maximum of a typed memory instance is a typed `u32?`. -/
theorem typedV_memMax10 {m : MemInst}
    (h : TypedV (simEnv10 B) (.varT "meminst" []) (memInstV m)) :
    TypedV (simEnv10 B) (.iterT (.varT "u32" []) .opt) (.opt (m.max.map pctV)) := by
  have hT : HasTyp (simEnv10 B) VarEnv.empty (.varT "memtype" [])
      (limitsV (Execution.Memory.size m.data) m.max) := hasTyp_struct2_fst findTyp_meminst10 h
  have hL : HasTyp (simEnv10 B) VarEnv.empty (.varT "limits" [])
      (limitsV (Execution.Memory.size m.data) m.max) :=
    hasTypDef_aliasT_iff.1 (Sim20.Whole.hasTypDef_of_closed findTyp_memtype10 hT)
  have hP := hasTyp_closedVariant_inv valsOnly_empty findTyp_limits10 hL (op := "[%..%]") rfl
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 hP
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y, ys, hys, -, htup'⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨rfl, rfl⟩ := List.cons.inj hys
  obtain ⟨y', ys', hys', hmax, -⟩ := hasTypTup_cons_iff.1 htup'
  obtain ⟨rfl, -⟩ := List.cons.inj hys'
  intro ρ hρ
  rcases hasTyp_iterT_opt_iff.1 hmax with he | ⟨w, he, hw⟩
  · exact hasTyp_iterT_opt_iff.2 (.inl he)
  · exact hasTyp_iterT_opt_iff.2 (.inr ⟨w, he, Sim.IntNumeric.hasTyp_varT_nil_congr
      ⟨rfl, rfl, rfl⟩ hρ hw⟩)

/-- **A grown memory instance is typed**: the old maximum, and at most `65536` pages. -/
theorem typedV_memInst_grow10 {m : MemInst} {n : Nat} {d : Execution.Memory.Bytes}
    (h : TypedV (simEnv10 B) (.varT "meminst" []) (memInstV m))
    (hg : Execution.Memory.grow? m.data m.max n = some d) :
    TypedV (simEnv10 B) (.varT "meminst" []) (memInstV {m with data := d}) := by
  have hle : Execution.Memory.size d < 2 ^ 32 := by
    unfold Execution.Memory.grow? at hg
    split at hg
    · rename_i hc
      obtain rfl := (Option.some.inj hg).symm
      have hr : ({ data := Array.replicate (n * 65536) 0 } : ByteArray).size = n * 65536 := by
        simp [ByteArray.size]
      simp only [Execution.Memory.size, Execution.Memory.pageSize, Execution.Memory.maxPages,
        ByteArray.size_append, hr] at hc ⊢
      omega
    · cases hg
  have hL : TypedV (simEnv10 B) (.varT "limits" []) (limitsV (Execution.Memory.size d) m.max) :=
    Sim20.Pure.typedV_closedCase20 findTyp_limits10 rfl
      (Sim20.Whole.hasTyp_tup2G (typedV_u32_10 hle) (typedV_memMax10 h))
  exact typedV_struct2 findTyp_meminst10
    (typedV_aliasG10 findTyp_memtype10 (hL _ valsOnly_empty) _ valsOnly_empty)
    (typedV_bytes10 d _ valsOnly_empty)

/-! ## The frame of `call_addr` -/

set_option maxRecDepth 8000000 in
theorem findTyp_funcF10 : (simEnv10 B).findTyp? "func" = some ([], [.instD [] []
    (.variantT [.mk "FUNC" (.tupT [.mk "typeidx" (.varT "typeidx" []),
      .mk "local*" (.iterT (.varT "local" []) .list), .mk "expr" (.varT "expr" [])]) [] []])]) :=
  rfl

set_option maxRecDepth 8000000 in
theorem findTyp_expr10 : (simEnv10 B).findTyp? "expr" =
    some ([], [.instD [] [] (.aliasT (.iterT (.varT "instr" []) .list))]) := rfl

set_option maxRecDepth 8000000 in
theorem findTyp_funcinstF10 : (simEnv10 B).findTyp? "funcinst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" (.varT "functype" []) [] [], .mk "MODULE" (.varT "moduleinst" []) [] [],
      .mk "CODE" (.varT "func" []) [] []])]) := rfl

/-- **The module of a typed Wasm `funcinst` is a typed `moduleinst`.** -/
theorem typedV_moduleOfInst10 {ft : V1.FuncType} {m : ModuleInst} {fn : V1.Func}
    (hi : HasTyp (simEnv10 B) VarEnv.empty (.varT "funcinst" []) (funcInstV hn (.wasm ft m fn))) :
    TypedV (simEnv10 B) (.varT "moduleinst" []) (moduleInstV m) := by
  have h₀ : HasTypFields (simEnv10 B) VarEnv.empty _
      [("TYPE", funcTypeV ft), ("MODULE", moduleInstV m), ("CODE", funcV fn)] :=
    hasTypFields_of_closed findTyp_funcinstF10 (typedV_of_empty20 hi)
  exact typedV_of_empty20 (hasTypFields_cons_nil_iff.1 (hasTypFields_cons_nil_iff.1 h₀).2).1

/-- **The body of a typed `func` is a typed `instr*`.** -/
theorem typedV_bodyOfFunc10 {fn : V1.Func}
    (h : TypedV (simEnv10 B) (.varT "func" []) (funcV fn)) :
    TypedV (simEnv10 B) instrsT (.list (instrsToV fn.body)) := by
  have hp := hasTyp_closedVariant_inv valsOnly_empty findTyp_funcF10 (h _ valsOnly_empty)
    (op := "FUNC") rfl
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 hp
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y, ys, hys, -, htup₁⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨rfl, rfl⟩ := List.cons.inj hys
  obtain ⟨y', ys', hys', -, htup₂⟩ := hasTypTup_cons_iff.1 htup₁
  obtain ⟨rfl, rfl⟩ := List.cons.inj hys'
  obtain ⟨y'', ys'', hys'', he, -⟩ := hasTypTup_cons_iff.1 htup₂
  obtain ⟨rfl, -⟩ := List.cons.inj hys''
  have he' : HasTyp (simEnv10 B) VarEnv.empty (.varT "expr" []) (.list (instrsToV fn.body)) :=
    Sim.IntNumeric.hasTyp_varT_nil_congr ⟨rfl, rfl, rfl⟩ valsOnly_empty he
  exact typedV_list_of_scope valsOnly_empty
    (hasTypDef_aliasT_iff.1 (Sim20.Whole.hasTypDef_of_closed findTyp_expr10 he'))

/-- **The code `call_addr` opens is typed**: the new frame and its body's label. -/
theorem typed_invokeFrame10 (V : ValTyped10 B) {s : Store H} (hst : StoreTy10 B hn s)
    {a : Execution.Runtime.FuncAddr} {ft : V1.FuncType} {m : ModuleInst} {fn : V1.Func}
    (hfi : s.funcs[a.value]? = some (.wasm ft m fn)) (args : List Execution.Runtime.Value)
    (n : Nat) : CodeTy10 B [.frame n ⟨args ++ fn.locals.map Execution.Runtime.Value.zero, m⟩
      [.label n [] (expression fn.body)]] := by
  have hstore : TypedV (simEnv10 B) storeT (storeV hn s) := typedV_storeV_iff10.2 hst
  have hi := hasTyp_funcinst_of_store10 hstore hfi
  have hbody := typedV_bodyOfFunc10 (typedV_funcV_of_inst10 hi)
  have hlocals : TypedV (simEnv10 B) (.iterT (.varT "val" []) .list)
      (.list ((args ++ fn.locals.map Execution.Runtime.Value.zero).map valV)) :=
    typedV_list_iff.2 fun u hu => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
      exact V v
  have hF : TypedV (simEnv10 B) frameT
      (frameV ⟨args ++ fn.locals.map Execution.Runtime.Value.zero, m⟩) :=
    typedV_struct2 findTyp_frame10 (hlocals _ valsOnly_empty)
      (typedV_moduleOfInst10 hi _ valsOnly_empty)
  have hl : CodeTy10 B [.label n [] (expression fn.body)] :=
    codeTy10_single (typedV_label10 typedV_instrs_nil10 (codeTy10_expression hbody))
  exact codeTy10_single (typedV_frame10 hF hl)

/-! ## Every step -/

/-- Subject reduction at `global.set`. -/
theorem ts10_globalSet (s : Store H) (f : Frame) (x : GlobalIdx) (a : Execution.Runtime.GlobalAddr)
    (g : GlobalInst) (v : Execution.Runtime.Value) (ha : f.module.globals[x.toNat]? = some a)
    (hg : s.globals[a.value]? = some g) (hts : TS10 B hn ⟨s, f, [value v, .source (.globalSet x)]⟩)
    (hok : GSetOk s f [value v, .source (.globalSet x)]) :
    TS10 B hn ⟨setGlobal s a { g with value := v }, f, []⟩ := by
  have hst := storeTy10_of_state hts.1
  have hgi := typedV_globalInst_set10 (typedV_of_getElem? hst.globals hg)
    (typedV_val_of_head10 hts.2) (gsetOk_redex hok ha hg)
  have hgs : TypedV (simEnv10 B) (.iterT (.varT "globalinst" []) .list)
      (.list ((s.globals.set a.value { g with value := v }).map globalInstV)) :=
    typedV_list_set20 hst.globals hgi
  exact ⟨typedV_state_store10 (s' := setGlobal s a { g with value := v }) hts.1
    ⟨hst.funcs, hgs, hst.tables, hst.mems⟩, codeTy10_nil⟩

/-- Subject reduction at `memory.grow`. -/
theorem ts10_memoryGrow (V : ValTyped10 B) (s : Store H) (f : Frame)
    (a : Execution.Runtime.MemAddr) (m : MemInst) (c r : BitVec 32) (b : Execution.Memory.Bytes)
    (hm : frameMemory s f = some (a, m)) (hgr : Execution.Memory.Grow m.data m.max c.toNat b r)
    (hts : TS10 B hn ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩) :
    TS10 B hn ⟨setMemory s a {m with data := b}, f, [value (.int .i32 r)]⟩ := by
  refine ⟨?_, codeTy10_value V _⟩
  have hsm := (frameMemory_some hm).2
  cases hgr with
  | success _ hgrow =>
    have hst := storeTy10_of_state hts.1
    have hms : TypedV (simEnv10 B) (.iterT (.varT "meminst" []) .list)
        (.list ((s.memories.set a.value {m with data := b}).map memInstV)) :=
      typedV_list_set20 hst.mems (typedV_memInst_grow10 (typedV_of_getElem? hst.mems hsm) hgrow)
    exact typedV_state_store10 (s' := setMemory s a {m with data := b}) hts.1
      ⟨hst.funcs, hst.globals, hst.tables, hms⟩
  | failure =>
    rw [setMemory_self hsm]
    exact hts.1

/-- **Subject reduction for every V1 step**, given that V1 values are typed: from a configuration
whose images are typed and which satisfies `GSetOk`, every V1 step leads to typed images. -/
theorem ts10_step (V : ValTyped10 B) {host : HostSemantics H} {c c' : Config H}
    (h : Step host c c') (hts : TS10 B hn c) (hg : GSetOk c.store c.frame c.code) :
    TS10 B hn c' := by
  induction h with
  | pure s f hp => exact ⟨hts.1, codeTy10_pure V hp hts.2⟩
  | context hs vs tail ih => exact ts10_context vs tail hts fun h' => ih h' (gsetOk_mid hg)
  | label _ n cont ih => exact ts10_label n cont hts fun h' => ih h' (gsetOk_label hg)
  | frame _ n outer ih => exact ts10_frame n outer hts fun h' => ih h' (gsetOk_frame hg)
  | localGet s f i v hv => exact subjRed10_leaf (.localGet s f i v hv) hts
  | localSet s f i v old hv => exact subjRed10_leaf (.localSet s f i v old hv) hts
  | globalGet s f i a g h₁ h₂ => exact subjRed10_leaf (.globalGet s f i a g h₁ h₂) hts
  | globalSet s f i a g v h₁ h₂ _ => exact ts10_globalSet s f i a g v h₁ h₂ hts hg
  | call s f i a h₁ => exact subjRed10_leaf (.call s f i a h₁) hts
  | callIndirect s f i c t a fn ft _ _ _ _ _ => exact ⟨hts.1, codeTy10_single (typedV_invoke10 a)⟩
  | callIndirectBounds s f i c t _ _ => exact ⟨hts.1, codeTy10_trap⟩
  | callIndirectNull s f i c t _ _ => exact ⟨hts.1, codeTy10_trap⟩
  | callIndirectType s f i c t a fn ft _ _ _ _ _ => exact ⟨hts.1, codeTy10_trap⟩
  | invokeWasm s f a ft m fn args h₁ _ _ =>
    exact ⟨hts.1, typed_invokeFrame10 V (storeTy10_of_state hts.1) h₁ args _⟩
  | invokeHost s s' f a ft fn args r h₁ _ _ => exact (not_typed_host10 hts.1 h₁).elim
  | invokeHostDiverges s f a ft fn args h₁ _ _ => exact (not_typed_host10 hts.1 h₁).elim
  | intLoad s f t p arg c a m v _ _ => exact ⟨hts.1, codeTy10_value V v⟩
  | intLoadTrap s f t p arg c a m _ _ => exact ⟨hts.1, codeTy10_trap⟩
  | floatLoad s f t arg c a m v _ _ => exact ⟨hts.1, codeTy10_value V v⟩
  | floatLoadTrap s f t arg c a m _ _ => exact ⟨hts.1, codeTy10_trap⟩
  | intStore s f t p arg c x a m b _ _ => exact (not_typed_store3 ⟨_, rfl⟩ hts.2).elim
  | intStoreTrap s f t p arg c x a m _ _ => exact (not_typed_store3 ⟨_, rfl⟩ hts.2).elim
  | floatStore s f t arg c x a m b _ _ => exact (not_typed_store3 ⟨_, rfl⟩ hts.2).elim
  | floatStoreTrap s f t arg c x a m _ _ => exact (not_typed_store3 ⟨_, rfl⟩ hts.2).elim
  | memorySize s f a m _ => exact ⟨hts.1, codeTy10_value V _⟩
  | memoryGrow s f a m c r b h₁ h₂ => exact ts10_memoryGrow V s f a m c r b h₁ h₂ hts

/-- **Subject reduction on configuration images.** -/
theorem typed10_step (V : ValTyped10 B) {host : HostSemantics H} {c c' : Config H}
    (h : Step host c c') (hc : Typed10 (simEnv10 B) hn c) (hg : GSetOk c.store c.frame c.code) :
    Typed10 (simEnv10 B) hn c' :=
  typed10_iff.2 (ts10_step V h (typed10_iff.1 hc) hg)

/-! ## The forward half without the successor's typing -/

/-- **The forward 1.0 half, without the successor's typing**: given that V1 values are typed,
`NumAgree10` at the spec profile and `FwdRestR10`, every V1 step from a configuration whose
image is typed and which satisfies `Plain10`, `GSetOk` and `MemsAligned10` is a step of the 1.0
script between the images. -/
theorem wholeStepFwd10_of_restR' (V : ValTyped10 B) {host : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) (R : FwdRestR10 B hn)
    {c c' : Config H} (hc : Typed10 (simEnv10 B) hn c) (hpl : Plain10 c.code)
    (hg : GSetOk c.store c.frame c.code) (hal : MemsAligned10 c.store) (h : Step host c c') :
    SStepB (simEnv10 B) (configV hn c) (configV hn c') :=
  wholeStepFwd10_of_restR A R hc (typed10_step V h hc hg) hpl hg hal h

end Silmaril.Wasm.SpecTec.Sim10.Whole
