module

public import Silmaril.Wasm.Tools.Gen.Typed3.Defs
public import Silmaril.Wasm.Models.Syntax.Thms
public import Silmaril.Wasm.Models.Features.Thms

/-!
# The Core 3.0 typed generator: typing proofs

* the facts about the fixed type section (`types_ok`, `toC_ok`, `heapC_ok`, `sig_expand`,
  `expand_S`, `expand_A`, lookups), each by kernel evaluation of silmaril's sound checkers
  (`typesCheck?_sound`, `TyOk.check_sound`, `Expand.iff`) on constants;
* `module_valid`: the module of every skeleton and code is Core 3.0 `ModuleValid` (the
  fixed type section and tags, constant global initialisers, memory limits, functions typed by
  `te_typed`/`ts_typed`/`ta_typed`, exports with distinct names);
* `module_inFeat`: it is inside `v30` (each instruction's capabilities, one memory per
  address type at most three, multi-memory);
* `te_typed`, `ts_typed`, `ta_typed`: in a context with the fixed types and tags (`Wf`), the
  erasure of a typed term has its Core 3.0 instruction type (`InstrsOk`): one structural
  induction over the mutual family, each constructor one or two Core typing rules (with
  `Instrs_ok/sub` for the non-null results of `struct.new`, `array.new`, `ref.i31`, `ref.func`
  and `ref.as_non_null`, and for dropping the locals `local.set`/`local.tee` initialise).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Tools.Gen.Typed3

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.Tools.Gen.Typed3

/-! ## The type section -/

theorem types_some : typesCheck? RecTypeOkAt.check {} pre = some dts := by decide +kernel

/-- **The type section is valid.** -/
theorem types_ok : TypesOk {} pre dts :=
  typesCheck?_sound (fun _ _ _ h => RecTypeOkAt.check_sound h) types_some

theorem toC_ok : ∀ t, TyOk Δ0 (toC t)
  | .num t => .num t
  | .sref => TyOk.check_sound (by decide +kernel)
  | .aref => TyOk.check_sound (by decide +kernel)
  | .fref => TyOk.check_sound (by decide +kernel)
  | .i31 => TyOk.check_sound (by decide +kernel)
  | .exn => TyOk.check_sound (by decide +kernel)

theorem heapC_ok : ∀ t, TyOk Δ0 (heapC t)
  | .num _ => .abs _
  | .sref => TyOk.check_sound (by decide +kernel)
  | .aref => TyOk.check_sound (by decide +kernel)
  | .fref => TyOk.check_sound (by decide +kernel)
  | .i31 => .abs _
  | .exn => .abs _

theorem sig_expand_b : ∀ j : Fin sigs.length,
    (sigD j).expand? = some (.func (Silmaril.Wasm.Validation.Ty.ofList ((sigP j).map toC)) (Silmaril.Wasm.Validation.Ty.ofList ((sigR j).map toC))) := by
  decide +kernel

/-- Each signature's defined type expands to its function type. -/
theorem sig_expand (j : Fin sigs.length) :
    Expand (sigD j) (.func (Silmaril.Wasm.Validation.Ty.ofList ((sigP j).map toC)) (Silmaril.Wasm.Validation.Ty.ofList ((sigR j).map toC))) :=
  Expand.iff.mpr (sig_expand_b j)

theorem expand_S : Expand dS (.struct (Silmaril.Wasm.Validation.Ty.ofList [.field .var (.val (.num (.int .i32))),
    .field .var (.val (.num (.int .i64)))])) := Expand.iff.mpr (by decide +kernel)

theorem expand_A : Expand dA (.array (.field .var (.val (.num (.int .i32))))) :=
  Expand.iff.mpr (by decide +kernel)

theorem expand_tag0 : Expand (sigD j0) (.func .nil .nil) := sig_expand j0

theorem expand_tag1 : Expand (sigD j1) (.func (Silmaril.Wasm.Validation.Ty.ofList [toC I32]) .nil) := sig_expand j1

theorem expand_F : Expand dF (.func (Silmaril.Wasm.Validation.Ty.ofList [toC I32]) (Silmaril.Wasm.Validation.Ty.ofList [toC I32])) :=
  sig_expand j2

theorem dts_S : dts[0]? = some dS := by decide +kernel
theorem dts_A : dts[1]? = some dA := by decide +kernel
theorem dts_F : dts[fIdx]? = some dF := by decide +kernel

theorem dts_sig : ∀ j : Fin sigs.length, dts[2 + j.val]? = some (sigD j) := by decide +kernel

theorem toC_ref : ∀ {t : VT}, t.isNum = false → toC t = .refT true (heapC t)
  | .num _, h => nomatch h
  | .sref, _ => rfl
  | .aref, _ => rfl
  | .fref, _ => rfl
  | .i31, _ => rfl
  | .exn, _ => rfl

/-! ## Contexts -/

variable {C : Context}

theorem wfTypes (hW : Wf C) : C.types = dts := congrArg TypeCtx.types hW.tctx

theorem wfLabel (hW : Wf C) (ts : List CValType) : Wf (C.withLabel ts) := ⟨hW.tctx, hW.tags⟩

theorem tyOk (hW : Wf C) (t : VT) : TyOk C.toTypeCtx (toC t) := hW.tctx ▸ toC_ok t

theorem heapOk (hW : Wf C) (t : VT) : TyOk C.toTypeCtx (heapC t) := hW.tctx ▸ heapC_ok t

theorem rok (hW : Wf C) (ts : List VT) : ResultOk C.toTypeCtx (ts.map toC) := by
  intro u hu
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hu
  exact tyOk hW t

theorem subRefl (t : VT) {Δ : TypeCtx} : Sub Δ (toC t) (toC t) := by
  cases t with
  | num t => exact .num
  | _ => exact .refv (.refNull .heapRefl)

theorem subNull (h : CHeapType) {Δ : TypeCtx} : Sub Δ (.refT false h) (.refT true h) :=
  .refv (.refNull .heapRefl)

theorem closeVal_src (hW : Wf C) : ∀ t, C.closeVal (srcVT t) = toC t := by
  have hT := wfTypes hW
  intro t
  unfold Context.closeVal
  rw [hT]
  cases t <;> rfl

theorem closeHeap_src (hW : Wf C) : ∀ t, C.closeHeap (srcHeap t) = heapC t := by
  have hT := wfTypes hW
  intro t
  unfold Context.closeHeap
  rw [hT]
  cases t <;> rfl

theorem typeAt (hW : Wf C) {n : Nat} {d : DefType} (h : dts[n]? = some d) (hn : n < 2 ^ 32) :
    C.type? (idx n) = some d := by
  have e : (idx n : TypeIdx).toNat = n := Nat.mod_eq_of_lt hn
  unfold Context.type?
  rw [e, wfTypes hW]
  exact h

theorem bt (hW : Wf C) (t : VT) : BlockTypeOk C (.value (srcVT t)) [] [toC t] := by
  have h := BlockTypeOk.value (C := C) (t := srcVT t) ((closeVal_src hW t).symm ▸ tyOk hW t)
  rw [closeVal_src hW t] at h
  exact h

/-! ## Composition -/

theorem cat {e₁ e₂ : Expr} {a b : List CValType} (h₁ : InstrsOk C e₁ (.plain [] a))
    (h₂ : InstrsOk C e₂ (.plain [] b)) (ha : ResultOk C.toTypeCtx a) :
    InstrsOk C (e₁ ++ e₂) (.plain [] (a ++ b)) := by
  have h₂' : InstrsOk C e₂ ⟨a ++ [], [], a ++ b⟩ := .frame h₂ ha
  rw [List.append_nil] at h₂'
  exact .seq h₁ (fun _ hx => absurd hx List.not_mem_nil) h₂'

theorem push {e : Expr} {i : Instr} {a b : List CValType} {xs : List Nat}
    (h : InstrsOk C e (.plain [] a)) (hi : InstrOk C i ⟨a, xs, b⟩) :
    InstrsOk C (e ++ [i]) ⟨[], xs, b⟩ :=
  .seq h (fun _ hx => absurd hx List.not_mem_nil) (.instr hi)

theorem dropInits {e : Expr} {xs : List Nat} {b : List CValType} (h : InstrsOk C e ⟨[], xs, b⟩)
    (hs : ResultSub C.toTypeCtx b b) (hok : ResultOk C.toTypeCtx b) :
    InstrsOk C e (.plain [] b) :=
  .sub h ⟨.nil, hs, fun _ hx => absurd hx List.not_mem_nil⟩
    ⟨fun _ hx => absurd hx List.not_mem_nil, hok, fun _ hx => absurd hx List.not_mem_nil⟩

theorem up {e : Expr} {u v : CValType} (h : InstrsOk C e (.plain [] [u]))
    (hs : Sub C.toTypeCtx u v) (hv : TyOk C.toTypeCtx v) : InstrsOk C e (.plain [] [v]) :=
  .sub h ⟨.nil, .cons hs .nil, fun _ hx => absurd hx List.not_mem_nil⟩
    ⟨fun _ hx => absurd hx List.not_mem_nil, fun _ hx => (List.mem_singleton.mp hx) ▸ hv,
      fun _ hx => absurd hx List.not_mem_nil⟩

theorem un {e : Expr} {i : Instr} {u : VT} {b : List CValType}
    (h : InstrsOk C e (.plain [] [toC u])) (hi : InstrOk C i (.plain [toC u] b)) :
    InstrsOk C (e ++ [i]) (.plain [] b) := push h hi

theorem bin (hW : Wf C) {e₁ e₂ : Expr} {i : Instr} {u w : VT} {b : List CValType}
    (h₁ : InstrsOk C e₁ (.plain [] [toC u])) (h₂ : InstrsOk C e₂ (.plain [] [toC w]))
    (hi : InstrOk C i (.plain [toC u, toC w] b)) : InstrsOk C (e₁ ++ e₂ ++ [i]) (.plain [] b) :=
  push (cat h₁ h₂ (rok hW [u])) hi

theorem tern (hW : Wf C) {e₁ e₂ e₃ : Expr} {i : Instr} {u w z : VT} {b : List CValType}
    (h₁ : InstrsOk C e₁ (.plain [] [toC u])) (h₂ : InstrsOk C e₂ (.plain [] [toC w]))
    (h₃ : InstrsOk C e₃ (.plain [] [toC z])) (hi : InstrOk C i (.plain [toC u, toC w, toC z] b)) :
    InstrsOk C (e₁ ++ e₂ ++ e₃ ++ [i]) (.plain [] b) :=
  push (cat (cat h₁ h₂ (rok hW [u])) h₃ (rok hW [u, w])) hi

theorem okNil : InstrTypeOk C (.plain [] []) :=
  ⟨fun _ hx => absurd hx List.not_mem_nil, fun _ hx => absurd hx List.not_mem_nil,
    fun _ hx => absurd hx List.not_mem_nil⟩

theorem ok1 {v : CValType} (hv : TyOk C.toTypeCtx v) : InstrTypeOk C (.plain [] [v]) :=
  ⟨fun _ hx => absurd hx List.not_mem_nil, fun _ hx => (List.mem_singleton.mp hx) ▸ hv,
    fun _ hx => absurd hx List.not_mem_nil⟩

theorem callT {e : Expr} {x : FuncIdx} {j : Fin sigs.length} {rs : List VT}
    (ha : InstrsOk C e (.plain [] ((sigP j).map toC))) (hf : C.funcs[x.toNat]? = some (sigD j))
    (hr : sigR j = rs) : InstrsOk C (e ++ [.call x]) (.plain [] (rs.map toC)) := by
  have hi := InstrOk.call (C := C) hf (sig_expand j)
  rw [Silmaril.Wasm.Validation.Ty.toList_ofList, Silmaril.Wasm.Validation.Ty.toList_ofList, hr] at hi
  exact push ha hi

/-- The memory access of a load. -/
theorem loadT {t : IntType} {p : Option (PackSize × Signedness)} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {l : Limits} (hm : C.mems[x.toNat]? = some ⟨a, l⟩) (hok : LoadOk t p arg a) :
    InstrOk C (.intLoad t p x arg) (.plain [a.valType] [.num (.int t)]) :=
  match p, hok with
  | none, hok => .memory (.intLoad hm hok)
  | some (_, _), hok => .memory (.intLoadPack hm hok.1 hok.2)

theorem storeT {t : IntType} {p : Option PackSize} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {l : Limits} (hm : C.mems[x.toNat]? = some ⟨a, l⟩) (hok : StoreOk t p arg a) :
    InstrOk C (.intStore t p x arg) (.plain [a.valType, .num (.int t)] []) :=
  match p, hok with
  | none, hok => .memory (.intStore hm hok)
  | some _, hok => .memory (.intStorePack hm hok.1 hok.2)

theorem tagAt (hW : Wf C) {n : Nat} {d : DefType} (h : tagDts[n]? = some d) (hn : n < 2 ^ 32) :
    C.tags[(idx n : TagIdx).toNat]? = some d := by
  have e : (idx n : TagIdx).toNat = n := Nat.mod_eq_of_lt hn
  rw [e, hW.tags]
  exact h

/-- `try_table`'s catch of tag 1 to the enclosing block. -/
theorem catch1 (hW : Wf C) :
    ∀ c ∈ [Catch.catch_ (idx 1) (idx 0)], CatchOk (C.withLabel [toC I32]) c := by
  intro c hc
  rw [List.mem_singleton.mp hc]
  exact .catch_ (tagAt (n := 1) (wfLabel hW _) rfl (by decide)) expand_tag1 rfl
    (List.Forall₂.cons Sub.num List.Forall₂.nil)

/-- `try_table`'s `catch_all_ref` to the enclosing block. -/
theorem catchAllRef0 :
    ∀ c ∈ [Catch.catchAllRef (idx 0)], CatchOk (C.withLabel [toC .exn]) c := by
  intro c hc
  rw [List.mem_singleton.mp hc]
  exact .catchAllRef rfl (.cons (subNull _) .nil)

mutual

/-- **Typed expressions erase to well-typed Core 3.0 code.** -/
theorem te_typed : {C : Context} → {t : VT} → Wf C → (e : TE C t) →
    InstrsOk C e.erase (.plain [] [toC t])
  | _, _, _, .iconst t b => .instr (.numeric (.intConst t b))
  | _, _, _, .fconst t b => .instr (.numeric (.floatConst t b))
  | C, _, hW, .null t h => by
    have hi := RefInstrOk.refNull (C := C) (ht := srcHeap t) ((closeHeap_src hW t).symm ▸ heapOk hW t)
    rw [closeHeap_src hW t, ← toC_ref h] at hi
    exact .instr (.reference hi)
  | _, _, _, .get x h => .instr (.variable (.localGet h))
  | _, _, _, .gget x _ h => .instr (.variable (.globalGet h))
  | _, _, hW, .ibin t op a b => bin hW (te_typed hW a) (te_typed hW b) (.numeric (.intBinOp t op))
  | _, _, hW, .iun t op v a => un (te_typed hW a) (.numeric (.intUnOp v))
  | _, _, hW, .itest t op a => un (te_typed hW a) (.numeric (.intTestOp t op))
  | _, _, hW, .irel t op a b => bin hW (te_typed hW a) (te_typed hW b) (.numeric (.intRelOp t op))
  | _, _, hW, .fbin t op a b =>
    bin hW (te_typed hW a) (te_typed hW b) (.numeric (.floatBinOp t op))
  | _, _, hW, .fun_ t op a => un (te_typed hW a) (.numeric (.floatUnOp t op))
  | _, _, hW, .frel t op a b =>
    bin hW (te_typed hW a) (te_typed hW b) (.numeric (.floatRelOp t op))
  | _, _, hW, .cvt op a => un (te_typed hW a) (.numeric (.convert op))
  | _, _, hW, .load _ _ _ _ _ _ hm hok addr => un (te_typed hW addr) (loadT hm hok)
  | _, _, hW, .fload _ _ _ _ _ hm hok addr => un (te_typed hW addr) (.memory (.floatLoad hm hok))
  | _, _, _, .msize _ _ _ hm => .instr (.memory (.memorySize hm))
  | _, _, hW, .mgrow _ _ _ hm v => un (te_typed hW v) (.memory (.memoryGrow hm))
  | _, _, hW, .call _ j hf hr args => callT (ta_typed hW args) hf hr
  | C, t, hW, .select a b c => by
    have hi := ParametricInstrOk.selectExpl (C := C) (t := srcVT t)
      ((closeVal_src hW t).symm ▸ tyOk hW t)
    rw [closeVal_src hW t] at hi
    exact tern hW (te_typed hW a) (te_typed hW b) (te_typed hW c) (.parametric hi)
  | _, t, hW, .block s v =>
    .instr (.block (bt hW t) (cat (ts_typed (wfLabel hW _) s) (te_typed (wfLabel hW _) v) (rok hW [])))
  | _, t, hW, .ite c a b =>
    un (te_typed hW c) (.if_ (bt hW t) (te_typed (wfLabel hW _) a) (te_typed (wfLabel hW _) b))
  | _, t, hW, .tee x h a =>
    dropInits (push (te_typed hW a) (.variable (.localTee h))) (.cons (subRefl t) .nil) (rok hW [t])
  | _, _, hW, .snew a b =>
    up (bin hW (te_typed hW a) (te_typed hW b)
      (.reference (.structNew (typeAt hW dts_S (by decide)) expand_S)))
      (subNull _) (tyOk hW .sref)
  | _, _, hW, .sget0 a =>
    un (te_typed hW a) (.reference (.structGet (m := .var) (z := .val (.num (.int .i32)))
      (typeAt hW dts_S (by decide)) expand_S rfl rfl))
  | _, _, hW, .sget1 a =>
    un (te_typed hW a) (.reference (.structGet (m := .var) (z := .val (.num (.int .i64)))
      (typeAt hW dts_S (by decide)) expand_S rfl rfl))
  | _, _, hW, .anew v n =>
    up (bin hW (te_typed hW v) (te_typed hW n)
      (.reference (.arrayNew (m := .var) (z := .val (.num (.int .i32)))
        (typeAt hW dts_A (by decide)) expand_A)))
      (subNull _) (tyOk hW .aref)
  | _, _, hW, .aget a i =>
    bin hW (te_typed hW a) (te_typed hW i)
      (.reference (.arrayGet (m := .var) (z := .val (.num (.int .i32)))
        (typeAt hW dts_A (by decide)) expand_A rfl))
  | _, _, hW, .alen a =>
    push (up (te_typed hW a) (.refv (.refNull (.defArray expand_A))) (.refv (.ref (.abs _))))
      (.reference .arrayLen)
  | _, _, hW, .i31new a =>
    up (un (te_typed hW a) (.reference .refI31)) (subNull _) (tyOk hW .i31)
  | _, _, hW, .i31get sx a => un (te_typed hW a) (.reference (.i31Get sx))
  | _, _, hW, @TE.isnull _ t h a => by
    have ha := te_typed hW a
    rw [toC_ref h] at ha
    exact push ha (.reference (.refIsNull (heapOk hW t)))
  | _, _, hW, @TE.asnn _ t h a => by
    have ha := te_typed hW a
    rw [toC_ref h] at ha ⊢
    exact up (push ha (.reference (.refAsNonNull (heapOk hW t)))) (subNull _)
      (toC_ref h ▸ tyOk hW t)
  | _, _, hW, .rfunc _ hf hr => up (.instr (.reference (.refFunc hf hr))) (subNull _) (tyOk hW .fref)
  | _, _, hW, .callref arg f =>
    push (cat (te_typed hW arg) (te_typed hW f) (rok hW [I32]))
      (.callRef (typeAt hW dts_F (by decide)) expand_F)
  | _, _, hW, .tryc b =>
    .instr (.block (bt hW I32) (.instr (.tryTable (bt (wfLabel hW _) I32)
      (te_typed (wfLabel (wfLabel hW _) _) b) (catch1 hW))))
  | _, _, hW, .exnc s =>
    .instr (.block (bt hW .exn) (push (.instr (.tryTable .empty
      (ts_typed (wfLabel (wfLabel hW _) _) s) catchAllRef0))
      (.throw (tagAt (n := 0) (wfLabel hW _) rfl (by decide)) expand_tag0
        (ok1 (tyOk hW .exn)))))

/-- **Typed statements erase to well-typed code with no stack effect.** -/
theorem ts_typed : {C : Context} → Wf C → (s : TS C) → InstrsOk C s.erase (.plain [] [])
  | _, _, .nop => .instr (.parametric .nop)
  | _, hW, @TS.drop _ t a => un (te_typed hW a) (.parametric (.drop (tyOk hW t)))
  | _, hW, .set x h a =>
    dropInits (push (te_typed hW a) (.variable (.localSet h))) .nil (rok hW [])
  | _, hW, .gset x h a => un (te_typed hW a) (.variable (.globalSet h))
  | _, hW, .store _ _ _ _ _ _ hm hok addr v =>
    bin hW (te_typed hW addr) (te_typed hW v) (storeT hm hok)
  | _, hW, .fstore _ _ _ _ _ hm hok addr v =>
    bin hW (te_typed hW addr) (te_typed hW v) (.memory (.floatStore hm hok))
  | _, hW, .fill _ _ _ hm d v n =>
    tern hW (te_typed hW d) (te_typed hW v) (te_typed hW n) (.memory (.memoryFill hm))
  | _, hW, .copy _ _ _ _ _ _ h₁ h₂ d s n =>
    tern hW (te_typed hW d) (te_typed hW s) (te_typed hW n) (.memory (.memoryCopy h₁ h₂))
  | _, hW, .block s => .instr (.block .empty (ts_typed (wfLabel hW _) s))
  | _, hW, .loop s => .instr (.loop .empty (ts_typed (wfLabel hW _) s))
  | _, hW, .ite c a b =>
    un (te_typed hW c) (.if_ .empty (ts_typed (wfLabel hW _) a) (ts_typed (wfLabel hW _) b))
  | _, hW, .brIf l h c => un (te_typed hW c) (.brIf h)
  | _, hW, .call _ j hf hr args => callT (rs := []) (ta_typed hW args) hf hr
  | _, hW, .seq a b => cat (ts_typed hW a) (ts_typed hW b) (rok hW [])
  | _, hW, .sset r v =>
    bin hW (te_typed hW r) (te_typed hW v)
      (.reference (.structSet (z := .val (.num (.int .i32))) (typeAt hW dts_S (by decide))
        expand_S rfl))
  | _, hW, .aset r i v =>
    tern hW (te_typed hW r) (te_typed hW i) (te_typed hW v)
      (.reference (.arraySet (z := .val (.num (.int .i32))) (typeAt hW dts_A (by decide))
        expand_A))
  | _, hW, .throw a =>
    un (te_typed hW a) (.throw (tagAt (n := 1) hW rfl (by decide)) expand_tag1 okNil)
  | _, hW, .throwRef a => un (te_typed hW a) (.throwRef okNil)

/-- **Typed argument lists erase to code pushing their types.** -/
theorem ta_typed : {C : Context} → {ts : List VT} → Wf C → (a : TA C ts) →
    InstrsOk C a.erase (.plain [] (ts.map toC))
  | _, _, _, .nil => .nil
  | _, _, hW, @TA.cons _ t _ a r => cat (te_typed hW a) (ta_typed hW r) (rok hW [t])

end

/-! ## Modules -/

theorem closeVal_srcΔ {C : Context} (hΔ : C.toTypeCtx = Δ0) (t : VT) :
    C.closeVal (srcVT t) = toC t :=
  closeVal_src (C := { C with tags := tagDts }) ⟨hΔ, rfl⟩ t

theorem closeHeap_srcΔ {C : Context} (hΔ : C.toTypeCtx = Δ0) (t : VT) :
    C.closeHeap (srcHeap t) = heapC t :=
  closeHeap_src (C := { C with tags := tagDts }) ⟨hΔ, rfl⟩ t

theorem defaultable : ∀ t : VT, Defaultable (toC t)
  | .num _ => trivial
  | .sref => rfl
  | .aref => rfl
  | .fref => rfl
  | .i31 => rfl
  | .exn => rfl

/-- A global's initialiser is a constant of its type. -/
theorem ginit_ok {C : Context} (hΔ : C.toTypeCtx = Δ0) (t : VT) (b : Nat) :
    ExprOkConst C (ginit t b) (toC t) := by
  have hT : TyOk C.toTypeCtx (C.closeHeap (srcHeap t)) := (closeHeap_srcΔ hΔ t).symm ▸ hΔ ▸ heapC_ok t
  have hnull : ∀ u : VT, u.isNum = false → ExprOkConst C [.refNull (srcHeap u)] (toC u) := by
    intro u hu
    have hu' : TyOk C.toTypeCtx (C.closeHeap (srcHeap u)) :=
      (closeHeap_srcΔ hΔ u).symm ▸ hΔ ▸ heapC_ok u
    have hi : InstrOk C (.refNull (srcHeap u)) (.plain [] [toC u]) := by
      have h := InstrOk.reference (RefInstrOk.refNull (C := C) hu')
      rwa [closeHeap_srcΔ hΔ u, ← toC_ref hu] at h
    exact ⟨.instr hi, fun i hi' => (List.mem_singleton.mp hi') ▸ .refNull _⟩
  have _ := hT
  match t with
  | .num (.int it) =>
    exact ⟨.instr (.numeric (.intConst _ _)), fun i hi => (List.mem_singleton.mp hi) ▸ .intConst _ _⟩
  | .num (.float ft) =>
    exact ⟨.instr (.numeric (.floatConst _ _)),
      fun i hi => (List.mem_singleton.mp hi) ▸ .floatConst _ _⟩
  | .sref => exact hnull .sref rfl
  | .aref => exact hnull .aref rfl
  | .fref => exact hnull .fref rfl
  | .i31 => exact hnull .i31 rfl
  | .exn => exact hnull .exn rfl

/-- The globals of a skeleton are valid, in every context with the fixed types. -/
theorem globals_ok : ∀ (gs : List (VT × Bool × Nat)) {C : Context}, C.toTypeCtx = Δ0 →
    GlobalsOk C (gs.map fun (t, m, b) => (⟨⟨gmut m, srcVT t⟩, ginit t b⟩ : Global))
      (gs.map fun (t, m, _) => (⟨gmut m, toC t⟩ : CGlobalType))
  | [], _, _ => .nil
  | (t, m, b) :: gs, C, hΔ =>
    .cons ⟨by rw [Context.closeGlobalType, closeVal_srcΔ hΔ], hΔ ▸ toC_ok t, ginit_ok hΔ t b⟩
      (globals_ok gs (C := { C with globals := C.globals ++ [⟨gmut m, toC t⟩] }) hΔ)

theorem memLimits_ok (a : AddrType) : MemOk ⟨a, memLimits⟩ := by
  cases a
  · exact (by decide : MemoryType.Valid ⟨.i32, memLimits⟩)
  · exact (by decide : MemoryType.Valid ⟨.i64, memLimits⟩)

theorem locals_ok {C : Context} (hΔ : C.toTypeCtx = Δ0) :
    ∀ ls : List VT, List.Forall₂ (LocalOk C) (ls.map srcVT) (lts ls)
  | [] => .nil
  | t :: ls => by
    have h := LocalOk.set (C := C) (t := srcVT t) ((closeVal_srcΔ hΔ t).symm ▸ hΔ ▸ toC_ok t)
      ((closeVal_srcΔ hΔ t).symm ▸ defaultable t)
    rw [closeVal_srcΔ hΔ t] at h
    exact .cons h (locals_ok hΔ ls)

theorem ctx_wf (k : Skel) : Wf k.ctx := ⟨rfl, rfl⟩

theorem fctx_wf (C0 : Context) (h : Wf C0) (j : Fin sigs.length) (ls : List VT) :
    Wf (fctx C0 j ls) := ⟨h.tctx, h.tags⟩

/-- **Every function of a skeleton's code is valid.** -/
theorem funcs_ok (k : Skel) : ∀ {l : List (Fin sigs.length)} (bs : Bodies k.ctx l),
    List.Forall₂ (FuncOk k.ctx) bs.funcs (l.map sigD)
  | [], .nil => .nil
  | j :: _, .cons b r => by
    have hj : 2 + j.val < 2 ^ 32 := by have := j.isLt; simp [sigs] at this; omega
    have hb : InstrsOk (fctx k.ctx j b.locals) (b.stmts.erase ++ b.rets.erase)
        (.plain [] ((sigR j).map toC)) :=
      cat (ts_typed (fctx_wf _ (ctx_wf k) j _) b.stmts) (ta_typed (fctx_wf _ (ctx_wf k) j _) b.rets)
        (rok (fctx_wf _ (ctx_wf k) j _) [])
    have hb' : ExprOk (k.ctx.funcBody (Silmaril.Wasm.Validation.Ty.ofList ((sigP j).map toC)).toList
        (Silmaril.Wasm.Validation.Ty.ofList ((sigR j).map toC)).toList (lts b.locals)) (b.stmts.erase ++ b.rets.erase)
        (Silmaril.Wasm.Validation.Ty.ofList ((sigR j).map toC)).toList := by
      rw [Silmaril.Wasm.Validation.Ty.toList_ofList, Silmaril.Wasm.Validation.Ty.toList_ofList]
      exact hb
    exact .cons (.mk (typeAt (ctx_wf k) (dts_sig j) hj) (sig_expand j) (locals_ok rfl b.locals) hb')
      (funcs_ok k r)

theorem tags_ok (C : Context) (hΔ : C.toTypeCtx = Δ0) :
    List.Forall₂ (TagOk C) Skel.tagTypes tagDts := by
  have hT : C.types = dts := congrArg TypeCtx.types hΔ
  have h0 : TagTypeOk Δ0 (sigD j0) := TagTypeOk.check_sound (by decide +kernel)
  have h1 : TagTypeOk Δ0 (sigD j1) := TagTypeOk.check_sound (by decide +kernel)
  have e0 : C.type? (idx 2) = some (sigD j0) := by
    unfold Context.type?; rw [hT]; exact dts_sig j0
  have e1 : C.type? (idx 3) = some (sigD j1) := by
    unfold Context.type?; rw [hT]; exact dts_sig j1
  exact .cons ⟨e0, hΔ ▸ h0⟩ (.cons ⟨e1, hΔ ▸ h1⟩ .nil)

theorem forall₂_of_exists {α β : Type _} {R : α → β → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, R a b) → ∃ l', List.Forall₂ R l l'
  | [], _ => ⟨[], .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨l', hl⟩ := forall₂_of_exists (l := l) fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact ⟨b :: l', .cons hb hl⟩

theorem exportNames_nodup : Skel.exportNames.Nodup := by decide

theorem exports_ok (k : Skel) (C : Context) (hf : C.funcs = k.fsigs.map sigD) :
    ∀ e ∈ k.exports, ∃ xt, ExportOk C e xt := by
  intro e he
  obtain ⟨⟨n, i⟩, hi, rfl⟩ := List.mem_map.mp he
  have hlt : i < (Skel.exportNames.take k.fsigs.length).length := List.snd_lt_of_mem_zipIdx hi
  have hlen : (Skel.exportNames.take k.fsigs.length).length ≤ k.fsigs.length ∧
      (Skel.exportNames.take k.fsigs.length).length ≤ 10 := by
    simp [Skel.exportNames]
  have hi32 : i < 2 ^ 32 := by omega
  have hi' : (idx i : FuncIdx).toNat = i := Nat.mod_eq_of_lt hi32
  have hk : i < (k.fsigs.map sigD).length := by
    rw [List.length_map]; omega
  refine ⟨.func ((k.fsigs.map sigD)[i]'hk), .func ?_⟩
  rw [hi', hf]
  exact List.getElem?_eq_getElem hk

theorem exports_nodup (k : Skel) : (k.exports.map Export.name).Nodup := by
  have e : (k.exports.map Export.name) = Skel.exportNames.take k.fsigs.length := by
    unfold Skel.exports
    rw [List.map_map]
    exact List.zipIdx_map_fst 0 _
  rw [e]
  exact exportNames_nodup.sublist (List.take_sublist _ _)

/-- **The module of a skeleton and its code is valid** (Core 3.0 `ModuleValid`). -/
theorem module_valid (k : Skel) (bs : Bodies k.ctx k.fsigs) : ModuleValid (k.module bs) := by
  obtain ⟨xtE, hx⟩ := forall₂_of_exists (exports_ok k k.ctx rfl)
  exact ⟨_, ModuleOk.mk (C := k.ctx) (dts := dts) (xtI := []) (jts := tagDts) (gts := k.gts)
    (fdts := k.fsigs.map sigD) (rts := []) (xtE := xtE)
    types_ok .nil rfl rfl (tags_ok _ rfl) (globals_ok k.gspecs rfl)
    (fun mt hm => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hm
      exact memLimits_ok a)
    .nil (funcs_ok k bs) (fun _ hd => absurd hd List.not_mem_nil) .nil
    (fun _ hs => nomatch hs) hx (exports_nodup k)⟩

/-! ## Inside Wasm 3.0 -/

open Silmaril.Wasm.Models

theorem v_intNum : v30.has .intNum = true := by decide
theorem v_floatNum : v30.has .floatNum = true := by decide
theorem v_control : v30.has .control = true := by decide
theorem v_directCall : v30.has .directCall = true := by decide
theorem v_memory : v30.has .memory = true := by decide
theorem v_globals : v30.has .globals = true := by decide
theorem v_mutGlobal : v30.has .mutGlobal = true := by decide
theorem v_signExt : v30.has .signExt = true := by decide
theorem v_satConv : v30.has .satConv = true := by decide
theorem v_multiValue : v30.has .multiValue = true := by decide
theorem v_refTypes : v30.has .refTypes = true := by decide
theorem v_bulkMemoryOpt : v30.has .bulkMemoryOpt = true := by decide
theorem v_typedFuncRef : v30.has .typedFuncRef = true := by decide
theorem v_gcImm : v30.has .gcImm = true := by decide
theorem v_gcMut : v30.has .gcMut = true := by decide
theorem v_exn : v30.has .exn = true := by decide
theorem v_memory64 : v30.has .memory64 = true := by decide
theorem v_multiMemory : v30.has .multiMemory = true := by decide

attribute [local simp] v_intNum v_floatNum v_control v_directCall v_memory v_globals v_mutGlobal
  v_signExt v_satConv v_multiValue v_refTypes v_bulkMemoryOpt v_typedFuncRef v_gcImm v_gcMut v_exn
  v_memory64 v_multiMemory

/-- Every instruction of a sequence is in `v30`. -/
def Ok (e : Expr) : Prop := ∀ i ∈ e, Instr.inFeatB v30 i = true

theorem ok_app {a b : Expr} (ha : Ok a) (hb : Ok b) : Ok (a ++ b) := fun i hi =>
  (List.mem_append.mp hi).elim (ha i) (hb i)

theorem ok_one {i : Instr} (h : Instr.inFeatB v30 i = true) : Ok [i] :=
  fun _ hj => (List.mem_singleton.mp hj) ▸ h

theorem ok_nil : Ok [] := fun _ h => absurd h List.not_mem_nil

theorem ins_of_ok : (e : Expr) → Ok e → Instr.insInFeatB v30 e = true
  | [], _ => rfl
  | i :: e, h => by
    have h₁ : Instr.inFeatB v30 i = true := h i List.mem_cons_self
    have h₂ : Instr.insInFeatB v30 e = true := ins_of_ok e (fun j hj => h j (List.mem_cons_of_mem _ hj))
    simp only [Instr.insInFeatB, h₁, h₂, Bool.and_self]

theorem vt_in : ∀ t : VT, ValType.inFeatB v30 (srcVT t) = true
  | .num (.int _) => by simp [srcVT, ValType.inFeatB]
  | .num (.float _) => by simp [srcVT, ValType.inFeatB]
  | .sref => by decide
  | .aref => by decide
  | .fref => by decide
  | .i31 => by decide
  | .exn => by decide

theorem heap_in : ∀ t : VT, HeapType.inFeatB v30 (srcHeap t) = true
  | .num _ => rfl
  | .sref => by decide
  | .aref => by decide
  | .fref => by decide
  | .i31 => by decide
  | .exn => by decide

theorem okI {i : Instr} (h : Instr.headB v30 i = true) (hb : i.bodies = []) : Ok [i] :=
  ok_one (by cases i <;> simp_all [Instr.inFeatB, Instr.bodies])

theorem un_ok {a : Expr} {i : Instr} (ha : Ok a) (h : Instr.headB v30 i = true)
    (hb : i.bodies = []) : Ok (a ++ [i]) := ok_app ha (okI h hb)

theorem bin_ok {a b : Expr} {i : Instr} (ha : Ok a) (hb' : Ok b) (h : Instr.headB v30 i = true)
    (hb : i.bodies = []) : Ok (a ++ b ++ [i]) := ok_app (ok_app ha hb') (okI h hb)

theorem tern_ok {a b c : Expr} {i : Instr} (ha : Ok a) (hb' : Ok b) (hc : Ok c)
    (h : Instr.headB v30 i = true) (hb : i.bodies = []) : Ok (a ++ b ++ c ++ [i]) :=
  ok_app (ok_app (ok_app ha hb') hc) (okI h hb)

theorem block_ok (bt : BlockType) (hbt : BlockType.inFeatB v30 bt = true) {b : Expr} (hb : Ok b) :
    Ok [.block bt b] := ok_one (by simp [Instr.inFeatB, Instr.headB, hbt, ins_of_ok b hb])

theorem loop_ok {b : Expr} (hb : Ok b) : Ok [.loop .empty b] :=
  ok_one (by simp [Instr.inFeatB, Instr.headB, BlockType.inFeatB, ins_of_ok b hb])

theorem if_ok (bt : BlockType) (hbt : BlockType.inFeatB v30 bt = true) {a b : Expr} (ha : Ok a)
    (hb : Ok b) : Ok [.if_ bt a b] :=
  ok_one (by simp [Instr.inFeatB, Instr.headB, hbt, ins_of_ok a ha, ins_of_ok b hb])

theorem try_ok (bt : BlockType) (hbt : BlockType.inFeatB v30 bt = true) (cs : List Catch) {b : Expr}
    (hb : Ok b) : Ok [.tryTable bt cs b] :=
  ok_one (by simp [Instr.inFeatB, Instr.headB, hbt, ins_of_ok b hb])

theorem bt_in (t : VT) : BlockType.inFeatB v30 (.value (srcVT t)) = true := vt_in t

theorem memIdx_in (x : MemIdx) : memIdxB v30 x = true := by simp [memIdxB]

theorem unop_in (op : IntUnOp) : IntUnOp.inFeatB v30 op = true := by
  cases op <;> simp [IntUnOp.inFeatB]

theorem cvt_in (op : ConvertOp) : ConvertOp.inFeatB v30 op = true := by
  cases op <;> simp [ConvertOp.inFeatB]

mutual

/-- **The erasure of an expression is in `v30`.** -/
theorem te_in : {C : Context} → {t : VT} → (e : TE C t) → Ok e.erase
  | _, _, .iconst _ _ => okI (by simp [Instr.headB]) rfl
  | _, _, .fconst _ _ => okI (by simp [Instr.headB]) rfl
  | _, _, .null t _ => okI (by simp [Instr.headB, heap_in t]) rfl
  | _, _, .get _ _ => okI (by simp [Instr.headB]) rfl
  | _, _, .gget _ _ _ => okI (by simp [Instr.headB]) rfl
  | _, _, .ibin _ _ a b => bin_ok (te_in a) (te_in b) (by simp [Instr.headB]) rfl
  | _, _, .iun _ op _ a => un_ok (te_in a) (by simp [Instr.headB, unop_in op]) rfl
  | _, _, .itest _ _ a => un_ok (te_in a) (by simp [Instr.headB]) rfl
  | _, _, .irel _ _ a b => bin_ok (te_in a) (te_in b) (by simp [Instr.headB]) rfl
  | _, _, .fbin _ _ a b => bin_ok (te_in a) (te_in b) (by simp [Instr.headB]) rfl
  | _, _, .fun_ _ _ a => un_ok (te_in a) (by simp [Instr.headB]) rfl
  | _, _, .frel _ _ a b => bin_ok (te_in a) (te_in b) (by simp [Instr.headB]) rfl
  | _, _, .cvt op a => un_ok (te_in a) (by simp [Instr.headB, cvt_in op]) rfl
  | _, _, .load _ _ x _ _ _ _ _ addr => un_ok (te_in addr) (by simp [Instr.headB, memIdx_in x]) rfl
  | _, _, .fload _ x _ _ _ _ _ addr => un_ok (te_in addr) (by simp [Instr.headB, memIdx_in x]) rfl
  | _, _, .msize x _ _ _ => okI (by simp [Instr.headB, memIdx_in x]) rfl
  | _, _, .mgrow x _ _ _ v => un_ok (te_in v) (by simp [Instr.headB, memIdx_in x]) rfl
  | _, _, .call _ _ _ _ args => un_ok (ta_in args) (by simp [Instr.headB]) rfl
  | _, t, .select a b c => tern_ok (te_in a) (te_in b) (te_in c)
      (by simp [Instr.headB, vt_in t]) rfl
  | _, t, .block s v => block_ok _ (bt_in t) (ok_app (ts_in s) (te_in v))
  | _, t, .ite c a b => ok_app (te_in c) (if_ok _ (bt_in t) (te_in a) (te_in b))
  | _, _, .tee _ _ a => un_ok (te_in a) (by simp [Instr.headB]) rfl
  | _, _, .snew a b => bin_ok (te_in a) (te_in b) (by simp [Instr.headB]) rfl
  | _, _, .sget0 a => un_ok (te_in a) (by simp [Instr.headB]) rfl
  | _, _, .sget1 a => un_ok (te_in a) (by simp [Instr.headB]) rfl
  | _, _, .anew v n => bin_ok (te_in v) (te_in n) (by simp [Instr.headB]) rfl
  | _, _, .aget a i => bin_ok (te_in a) (te_in i) (by simp [Instr.headB]) rfl
  | _, _, .alen a => un_ok (te_in a) (by simp [Instr.headB]) rfl
  | _, _, .i31new a => un_ok (te_in a) (by simp [Instr.headB]) rfl
  | _, _, .i31get _ a => un_ok (te_in a) (by simp [Instr.headB]) rfl
  | _, _, .isnull _ a => un_ok (te_in a) (by simp [Instr.headB]) rfl
  | _, _, .asnn _ a => un_ok (te_in a) (by simp [Instr.headB]) rfl
  | _, _, .rfunc _ _ _ => okI (by simp [Instr.headB]) rfl
  | _, _, .callref arg f => bin_ok (te_in arg) (te_in f) (by simp [Instr.headB]) rfl
  | _, _, .tryc b => block_ok _ (bt_in I32) (try_ok _ (bt_in I32) _ (te_in b))
  | _, _, .exnc s => block_ok _ (bt_in .exn)
      (ok_app (try_ok _ rfl _ (ts_in s)) (okI (by simp [Instr.headB]) rfl))

/-- **The erasure of a statement is in `v30`.** -/
theorem ts_in : {C : Context} → (s : TS C) → Ok s.erase
  | _, .nop => okI (by simp [Instr.headB]) rfl
  | _, .drop a => un_ok (te_in a) (by simp [Instr.headB]) rfl
  | _, .set _ _ a => un_ok (te_in a) (by simp [Instr.headB]) rfl
  | _, .gset _ _ a => un_ok (te_in a) (by simp [Instr.headB]) rfl
  | _, .store _ _ x _ _ _ _ _ addr v =>
    bin_ok (te_in addr) (te_in v) (by simp [Instr.headB, memIdx_in x]) rfl
  | _, .fstore _ x _ _ _ _ _ addr v =>
    bin_ok (te_in addr) (te_in v) (by simp [Instr.headB, memIdx_in x]) rfl
  | _, .fill x _ _ _ d v n =>
    tern_ok (te_in d) (te_in v) (te_in n) (by simp [Instr.headB, memIdx_in x]) rfl
  | _, .copy x₁ x₂ _ _ _ _ _ _ d s n =>
    tern_ok (te_in d) (te_in s) (te_in n) (by simp [Instr.headB, memIdx_in x₁, memIdx_in x₂]) rfl
  | _, .block s => block_ok _ rfl (ts_in s)
  | _, .loop s => loop_ok (ts_in s)
  | _, .ite c a b => ok_app (te_in c) (if_ok _ rfl (ts_in a) (ts_in b))
  | _, .brIf _ _ c => un_ok (te_in c) (by simp [Instr.headB]) rfl
  | _, .call _ _ _ _ args => un_ok (ta_in args) (by simp [Instr.headB]) rfl
  | _, .seq a b => ok_app (ts_in a) (ts_in b)
  | _, .sset r v => bin_ok (te_in r) (te_in v) (by simp [Instr.headB]) rfl
  | _, .aset r i v => tern_ok (te_in r) (te_in i) (te_in v) (by simp [Instr.headB]) rfl
  | _, .throw a => un_ok (te_in a) (by simp [Instr.headB]) rfl
  | _, .throwRef a => un_ok (te_in a) (by simp [Instr.headB]) rfl

/-- **The erasure of an argument list is in `v30`.** -/
theorem ta_in : {C : Context} → {ts : List VT} → (a : TA C ts) → Ok a.erase
  | _, _, .nil => ok_nil
  | _, _, .cons a r => ok_app (te_in a) (ta_in r)

end

theorem ginit_in : ∀ (t : VT) (b : Nat), constExprB v30 (ginit t b) = true
  | .num (.int _), _ => rfl
  | .num (.float _), _ => rfl
  | .sref, _ => rfl
  | .aref, _ => rfl
  | .fref, _ => rfl
  | .i31, _ => rfl
  | .exn, _ => rfl

theorem global_in (t : VT) (m : Bool) (b : Nat) :
    Global.inFeatB v30 ⟨⟨gmut m, srcVT t⟩, ginit t b⟩ = true := by
  have h : constExprB v30 (ginit t b) = true := ginit_in t b
  simp only [Global.inFeatB, GlobalType.inFeatB, vt_in, v_globals, v_mutGlobal, Bool.or_true,
    Bool.and_true, Bool.true_and]
  exact h

theorem funcs_in {C0 : Context} : ∀ {l : List (Fin sigs.length)} (bs : Bodies C0 l),
    ∀ f ∈ bs.funcs, Func.inFeatB v30 f = true
  | [], .nil, _, h => absurd h List.not_mem_nil
  | _ :: _, .cons b r, f, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · have hl : (b.locals.map srcVT).all (ValType.inFeatB v30) = true :=
        List.all_eq_true.mpr fun v hv => by
          obtain ⟨t, -, rfl⟩ := List.mem_map.mp hv
          exact vt_in t
      have hb : Instr.insInFeatB v30 (b.stmts.erase ++ b.rets.erase) = true :=
        ins_of_ok _ (ok_app (ts_in b.stmts) (ta_in b.rets))
      simp only [Func.inFeatB, hl, hb, Bool.and_self]
    · exact funcs_in r f h'

theorem pre_in : pre.all (RecType.inFeatB v30) = true := by decide +kernel

/-- **The module of a skeleton and its code is inside Wasm 3.0.** -/
theorem module_inFeat (k : Skel) (bs : Bodies k.ctx k.fsigs) : Module.InFeat v30 (k.module bs) := by
  have hg : k.globals.all (Global.inFeatB v30) = true := List.all_eq_true.mpr fun g hg => by
    obtain ⟨⟨t, m, b⟩, -, rfl⟩ := List.mem_map.mp hg
    exact global_in t m b
  have hm : k.memTypes.all (MemoryType.inFeatB v30) = true := List.all_eq_true.mpr fun mt hm => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hm
    cases a <;> decide
  have hf : bs.funcs.all (Func.inFeatB v30) = true := List.all_eq_true.mpr (funcs_in bs)
  show Module.inFeatB v30 (k.module bs) = true
  simp only [Module.inFeatB, Skel.module, Skel.module0, pre_in, hg, hm, hf, v_exn, v_multiMemory,
    v_refTypes, Bool.or_true, Bool.and_true, List.all_nil]

end Silmaril.Proofs.Wasm.Tools.Gen.Typed3
