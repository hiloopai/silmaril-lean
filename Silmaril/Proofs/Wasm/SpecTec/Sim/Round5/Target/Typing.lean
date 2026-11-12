module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy.Thms

/-!
# Round 5: positive typing on `FloatMissel`-free code

Track pos's reduction of the positive typing to the SIMD instructions (`Pos.instrTyping_of_open`,
`Pos.openTyping_of_simd`, `Pos.typedV_store_ne`, `Pos.typed_of_configOk_ne`), re-run with the
`instrSel` restriction threaded through the recursion into block bodies, function bodies and the
code. Its SIMD leaf is then `SimdTy.SimdTypingSel`, which is proved
(`SimdTy.simdTypingSel`), so:

* `posTypingSel : PosTypingSel B hn` holds for every `B` and encoding;
* `typed_of_configOk_sel`: `ConfigOk ∧ BoundedSel → Typed`, in every `simEnv B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Target

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type} {B : Builtins}

/-! ## `instrSel` -/

/-- Every instruction of an `instrsSel` sequence is `instrSel`. -/
theorem instrsSel_mem : ∀ {l : List Instr}, instrsSel l = true → ∀ i ∈ l, instrSel i = true
  | [], _ => fun _ hi => absurd hi List.not_mem_nil
  | _ :: _, h => by
    simp only [instrsSel, Bool.and_eq_true] at h
    intro i hi
    rcases List.mem_cons.1 hi with rfl | hi
    · exact h.1
    · exact instrsSel_mem h.2 i hi

/-- The bodies of an `instrSel` instruction are `instrsSel`. -/
theorem instrSel_bodies {i : Instr} (h : instrSel i = true) :
    ∀ b ∈ i.bodies, instrsSel b = true := by
  cases i <;> simp_all [instrSel, Instr.bodies]

/-- An `instrSel` instruction is not `FloatMissel`. -/
theorem floatMissel_of_instrSel {i : Instr} (h : instrSel i = true) :
    SimdTy.FloatMissel i = false := by
  cases i <;> simp_all [instrSel, SimdTy.FloatMissel]

/-- `instrsSel` splits over `++`. -/
theorem instrsSel_append : ∀ {a b : List Instr},
    instrsSel (a ++ b) = true ↔ instrsSel a = true ∧ instrsSel b = true
  | [], b => by simp [instrsSel]
  | x :: a, b => by
    simp only [List.cons_append, instrsSel, Bool.and_eq_true]
    rw [instrsSel_append]
    exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨⟨h₁, h₂⟩, h₃⟩, fun ⟨⟨h₁, h₂⟩, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

/-! ## Instructions -/

set_option maxRecDepth 100000 in
/-- **The open classes are typed off `FloatMissel`**: the SIMD instructions by its proof's
`SimdTypingSel`, the numeric operators, conversions, loads and stores as in
`Pos.openTyping_of_simd`. -/
theorem openTypingSel (hS : SimdTy.SimdTypingSel B) {C : Context} {i : Instr} {it : InstrType}
    (hok : InstrOk C i it) (hb : Round4.instrBnd i = true) (hop : Pos.InstrOpen i = true)
    (hm : SimdTy.FloatMissel i = false) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV i) := by
  by_cases hs : Pos.InstrSimd i = true
  · exact hS C i it hok hb hs hm
  · cases i <;> (try simp [Pos.InstrOpen, Pos.InstrSimd] at hop hs)
    all_goals first
      | exact Pos.typedV_intNumeric hok (.inl ⟨_, _, rfl⟩)
      | exact Pos.typedV_intNumeric hok (.inr (.inl ⟨_, _, rfl⟩))
      | exact Pos.typedV_intNumeric hok (.inr (.inr (.inl ⟨_, _, rfl⟩)))
      | exact Pos.typedV_intNumeric hok (.inr (.inr (.inr ⟨_, _, rfl⟩)))
      | exact Pos.typedV_floatNumeric (.inl ⟨_, _, rfl⟩)
      | exact Pos.typedV_floatNumeric (.inr (.inl ⟨_, _, rfl⟩))
      | exact Pos.typedV_floatNumeric (.inr (.inr ⟨_, _, rfl⟩))
      | exact Pos.typedV_convert _
      | exact Pos.typedV_intLoad hok
      | exact Pos.typedV_intStore hok
      | exact Pos.typedV_floatLoad _ _ _
      | exact Pos.typedV_floatStore _ _ _

/-- **Every valid, bounded, `instrSel` instruction is typed**, by well-founded recursion on the
instruction (`Pos.instrTyping_aux` with `instrSel` threaded into the bodies). -/
theorem instrTypingSel_aux (hS : SimdTy.SimdTypingSel B) :
    ∀ (i : Instr) (C : Context) (it : InstrType), InstrOk C i it → Round4.instrBnd i = true →
      instrSel i = true → TypedV (simEnv B) (.varT "instr" []) (instrToV i)
  | i, C, it, hok, hb, hsel =>
    if hop : Pos.InstrOpen i = true then openTypingSel hS hok hb hop (floatMissel_of_instrSel hsel)
    else Pos.typedV_instrToV_of i (by simpa using hop) hb fun b hbm => by
      obtain ⟨C', it', hbo⟩ := Pos.instrOk_bodies hok b hbm
      rw [Exn.instrsToV_eq_map]
      exact typedV_list_iff.2 fun u hu => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hu
        obtain ⟨C'', it'', hjo⟩ := Pos.instrsOk_mem hbo j hj
        have := Pos.sizeOf_lt_of_body hbm hj
        exact instrTypingSel_aux hS j C'' it'' hjo
          (Pos.instrsBnd_mem (Pos.instrBnd_bodies hb b hbm) j hj)
          (instrsSel_mem (instrSel_bodies hsel b hbm) j hj)
termination_by i => sizeOf i

/-- **A valid, bounded, `instrsSel` sequence is a typed `instr*`.** -/
theorem typedV_instrsSel (hS : SimdTy.SimdTypingSel B) {C : Context} {is : List Instr}
    {it : InstrType} (h : InstrsOk C is it) (hb : Round4.instrsBnd is = true)
    (hsel : instrsSel is = true) : TypedV (simEnv B) instrsT (.list (instrsToV is)) := by
  rw [Exn.instrsToV_eq_map]
  exact typedV_list_iff.2 fun u hu => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hu
    obtain ⟨C', it', hok⟩ := Pos.instrsOk_mem h i hi
    exact instrTypingSel_aux hS i C' it' hok (Pos.instrsBnd_mem hb i hi) (instrsSel_mem hsel i hi)

/-! ## Stores -/

/-- **A valid Wasm function's code without `FloatMissel` instructions is a typed `funccode`.** -/
theorem typedV_funccodeSel (hS : SimdTy.SimdTypingSel B) {C : Context} {fn : Func} {d : DefType}
    (hf : FuncOk C fn d) (hb : Round4.instrsBnd fn.body = true) (hsel : instrsSel fn.body = true) :
    TypedV (simEnv B) (.varT "funccode" []) (.case "FUNC" (.tuple
      [Silmaril.SpecTec.Equiv.Execution.pctV fn.type.toNat,
       .list (fn.locals.map fun t => .case "LOCAL" (Encode.toValue t)),
       .list (instrsToV fn.body)])) := by
  obtain ⟨-, -, -, hbody⟩ := hf
  exact Typing.typedV_closedCase Pos.findTyp_funccode rfl (Pos.hasTyp_tup3
    (Pos.typedV_typeidxNat fn.type.value.isLt) (Pos.typedV_locals fn.locals)
    (Pos.typedV_expr (typedV_instrsSel hS hbody hb hsel)))

/-- **A valid, bounded, export-free function instance without `FloatMissel` code is a typed
`funcinst`.** -/
theorem typedV_funcinstSel (hS : SimdTy.SimdTypingSel B) (hn : H → String) {s : Store H}
    {fi : FuncInst H} (hok : FuncInstOk s fi) (hb : Round4.FuncBnd fi)
    (he : fi.module.exports = []) (hsel : ∀ fn, fi.code = .wasm fn → instrsSel fn.body = true) :
    TypedV (simEnv B) funcinstT (funcInstV hn fi) := by
  have hcode : TypedV (simEnv B) (.varT "funccode" []) (match fi.code with
      | .wasm fn => .case "FUNC" (.tuple [Silmaril.SpecTec.Equiv.Execution.pctV fn.type.toNat,
          .list (fn.locals.map fun t => .case "LOCAL" (Encode.toValue t)),
          .list (instrsToV fn.body)])
      | .host h => .case "_HOSTFUNC" (.text (hn h))) := by
    cases hok with
    | wasm _ _ hc hf _ =>
      rw [hc]
      exact typedV_funccodeSel hS hf (hb.2.2 _ hc) (hsel _ hc)
    | host _ _ hc =>
      rw [hc]
      exact Typing.typedV_closedCase Pos.findTyp_funccode rfl (hasTyp_textT_iff.2 ⟨_, rfl⟩)
  exact Pos.typedV_struct ConfigOk.findTyp_funcinst (Pos.hasTypFields_cons_of
    (Pos.typedV_deftype fi.type hb.1) (Pos.hasTypFields_cons_of
      (Pos.typedV_moduleinst_ne _ hb.2.1 he) (Pos.hasTypFields_one hcode)))

/-- **A valid, bounded, export-free store without `FloatMissel` function bodies is a typed
`store`** (`Pos.typedV_store_ne` with `typedV_funcinstSel`). -/
theorem typedV_storeSel (hS : SimdTy.SimdTypingSel B) (hn : H → String) (s : Store H)
    (hs : StoreOk s) (hb : Round4.StoreBnd s) (he : Pos.StoreNE s) (hsel : StoreSel s) :
    TypedV (simEnv B) storeT (storeV hn s) :=
  Pos.typedV_struct ConfigOk.findTyp_store' <|
    Pos.hasTypFields_cons_of (Pos.typedV_map fun ti hti => Pos.typedV_taginst ti (hb.tags ti hti)) <|
    Pos.hasTypFields_cons_of
      (Pos.typedV_map fun gi hgi => Pos.typedV_globalinst gi (hb.globals gi hgi)) <|
    Pos.hasTypFields_cons_of (Pos.typedV_map fun mi _ => Pos.typedV_meminst mi) <|
    Pos.hasTypFields_cons_of
      (Pos.typedV_map fun ti hti => Pos.typedV_tableinst ti (hb.tables ti hti)) <|
    Pos.hasTypFields_cons_of (Pos.typedV_map fun fi hfi =>
      typedV_funcinstSel hS hn (hs.funcs fi hfi) (hb.funcs fi hfi) (he fi hfi) (hsel fi hfi)) <|
    Pos.hasTypFields_cons_of (Pos.typedV_map fun di _ => Pos.typedV_datainst di) <|
    Pos.hasTypFields_cons_of
      (Pos.typedV_map fun ei hei => Pos.typedV_eleminst ei (hb.elems ei hei)) <|
    Pos.hasTypFields_cons_of
      (Pos.typedV_map fun si hsi => Pos.typedV_structinst si (hb.structs si hsi)) <|
    Pos.hasTypFields_cons_of
      (Pos.typedV_map fun ai hai => Pos.typedV_arrayinst ai (hb.arrays ai hai)) <|
    Pos.hasTypFields_one (Pos.typedV_map fun e _ =>
      Typing.typedV_exninst e (typedV_list_iff.2 fun u hu => by
        obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
        exact Typing.typedV_val v))

/-! ## `PosTypingSel` -/

/-- **`PosTypingSel` from `SimdTypingSel`.** -/
theorem posTypingSel_of_simdSel (hS : SimdTy.SimdTypingSel B) (hn : H → String) :
    PosTypingSel B hn where
  instr C i it hok hb hsel := instrTypingSel_aux hS i C it hok hb hsel
  callRefType d _ h := Pos.typedV_callRefType d h
  returnCallRefType d _ h := Pos.typedV_returnCallRefType d h
  moduleinst := Pos.moduleinst_ne
  store s hs _ hb he hsel := typedV_storeSel hS hn s hs hb he hsel

/-- **`PosTypingSel` holds**, for every `B` and encoding. -/
theorem posTypingSel (B : Builtins) (hn : H → String) : PosTypingSel B hn :=
  posTypingSel_of_simdSel (SimdTy.simdTypingSel B) hn

/-- `Pos.PosTypingNE` gives `PosTypingSel` (vacuously: `Pos.PosTypingNE` is false,
`SimdTy.not_posTypingNE`). -/
theorem posTypingSel_of_posTypingNE {hn : H → String} (K : Pos.PosTypingNE B hn) :
    PosTypingSel B hn where
  instr C i it hok hb _ := K.instr C i it hok hb
  callRefType := K.callRefType
  returnCallRefType := K.returnCallRefType
  moduleinst := K.moduleinst
  store s hs hs' hb he _ := K.store s hs hs' hb he

/-! ## Configurations -/

/-- `AdminsSel` splits over `++`. -/
theorem adminsSel_append : ∀ {a b : List Admin}, AdminsSel (a ++ b) ↔ AdminsSel a ∧ AdminsSel b
  | [], b => by simp [AdminsSel]
  | x :: a, b => by
    simp only [List.cons_append, AdminsSel]
    rw [adminsSel_append]
    exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨⟨h₁, h₂⟩, h₃⟩, fun ⟨⟨h₁, h₂⟩, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

/-- Source code is `AdminsSel` when its instructions are `instrsSel`. -/
theorem adminsSel_expression : ∀ {l : List Instr}, instrsSel l = true → AdminsSel (expression l)
  | [], _ => trivial
  | _ :: l, h => by
    simp only [instrsSel, Bool.and_eq_true] at h
    exact ⟨h.1, adminsSel_expression h.2⟩

variable {hn : H → String}

/-- The frame of a valid frame judgement, bounded and export-free, is typed. -/
theorem frame_typed_sel (K : PosTypingSel B hn) {s : Store H} {f : Frame} {C : Context}
    (hf : FrameOk s f C) (hb : Round4.ModuleBnd f.module) (he : f.module.exports = []) :
    TypedV (simEnv B) frameT (frameV f) := by
  obtain ⟨C₀, lts, hm, -, -⟩ := hf
  exact Round4.typedV_frame_of (K.moduleinst _ _ _ hm hb he)

mutual
/-- **Every valid, bounded, export-free administrative instruction without `FloatMissel` code is
typed.** -/
theorem adminOk_typed_sel (K : PosTypingSel B hn) {s : Store H} :
    ∀ {C : Context} {a : Admin} {it : InstrType}, AdminOk s C a it → Round4.AdminBnd a →
      Pos.AdminNE a → AdminSel a → TypedV (simEnv B) instrsT (.list [adminToV a])
  | _, _, _, .plain h, hb, _, hs => typedV_list_single.2 (K.instr _ _ _ h hb hs)
  | _, _, _, .callRefType hok _, hb, _, _ => typedV_list_single.2 (K.callRefType _ hok hb)
  | _, _, _, .returnCallRefType hok _ _ _ _, hb, _, _ =>
    typedV_list_single.2 (K.returnCallRefType _ hok hb)
  | _, _, _, .ref _, _, _, _ => typedV_list_single.2 (Round4.typedV_refAdmin _)
  | _, _, _, .label (n := n) (cont := cont) _ hc hbody, hb, he, hs => by
    have hcont := adminsOk_typed_sel K hc (Round4.adminsBnd_expression hb.1)
      (Pos.adminsNE_expression cont) (adminsSel_expression hs.1)
    rw [adminsToV_expression] at hcont
    exact FwdMem.typedV_label ((Typing.stateTyping_simEnv B).nat n) hcont
      (adminsOk_typed_sel K hbody hb.2 he hs.2)
  | _, _, _, .frame (n := n) hf _ hbody _, hb, he, hs =>
    FwdMem.typedV_frame ((Typing.stateTyping_simEnv B).nat n)
      (frame_typed_sel K hf hb.1 he.1) (adminsOk_typed_sel K hbody hb.2 he.2 hs)
  | _, _, _, .handler (n := n) _ hbody, hb, he, hs =>
    FwdMem.typedV_handler ((Typing.stateTyping_simEnv B).nat n)
      (typedV_list_iff.2 fun u hu => by
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 hu
        exact Round4.typedV_catch c)
      (adminsOk_typed_sel K hbody hb he hs)
  | _, _, _, .trap _, _, _, _ => typedV_list_single.2 Round4.typedV_trap
  | _, _, _, .throwRefInits _, _, _, _ => typedV_list_single.2 Round4.typedV_throwRef

/-- **Every valid, bounded, export-free code sequence without `FloatMissel` code is typed.** -/
theorem adminsOk_typed_sel (K : PosTypingSel B hn) {s : Store H} :
    ∀ {C : Context} {l : List Admin} {it : InstrType}, AdminsOk s C l it → Round4.AdminsBnd l →
      Pos.AdminsNE l → AdminsSel l → TypedV (simEnv B) instrsT (.list (adminsToV l))
  | _, _, _, .nil, _, _, _ => typedV_list_nil
  | _, _, _, .single h, hb, he, hs => adminOk_typed_sel K h hb.1 he.1 hs.1
  | _, _, _, .seq h₁ _ h₂, hb, he, hs => by
    obtain ⟨hb₁, hb₂⟩ := Round4.adminsBnd_append.1 hb
    obtain ⟨he₁, he₂⟩ := Pos.adminsNE_append.1 he
    obtain ⟨hs₁, hs₂⟩ := adminsSel_append.1 hs
    rw [adminsToV_append]
    exact typedV_list_append.2
      ⟨adminsOk_typed_sel K h₁ hb₁ he₁ hs₁, adminsOk_typed_sel K h₂ hb₂ he₂ hs₂⟩
  | _, _, _, .cons ha _ hl, hb, he, hs => by
    have h₁ := adminOk_typed_sel K ha hb.1 he.1 hs.1
    have h₂ := adminsOk_typed_sel K hl hb.2 he.2 hs.2
    exact typedV_list_cons_iff.2 ⟨typedV_list_single.1 h₁, h₂⟩
  | _, _, _, .sub h _ _, hb, he, hs => adminsOk_typed_sel K h hb he hs
  | _, _, _, .frame h _, hb, he, hs => adminsOk_typed_sel K h hb he hs
end

/-- **`ConfigOk ∧ BoundedSel → Typed`**, given `PosTypingSel`. -/
theorem typed_of_configOk_selK (K : PosTypingSel B hn) {c : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (hb : BoundedSel c) : Typed (simEnv B) hn c := by
  obtain ⟨C, ⟨hs, hf⟩, hcode⟩ := hc
  have T := Typing.typingFacts_simEnv B hn
  exact (T.config c).2 ⟨(T.state _ _).2
    ⟨K.store _ hs hb.1.1.store hb.1.1.storeBnd hb.1.2.store hb.2.store,
      frame_typed_sel K hf hb.1.1.frame hb.1.2.frame⟩,
    adminsOk_typed_sel K hcode hb.1.1.code hb.1.2.code hb.2.code⟩

/-- **`ConfigOk ∧ BoundedSel → Typed`**, in every `simEnv B`. -/
theorem typed_of_configOk_sel (B : Builtins) (hn : H → String) {c : Config H}
    {ts : List CValType} (hc : ConfigOk c ts) (hb : BoundedSel c) : Typed (simEnv B) hn c :=
  typed_of_configOk_selK (posTypingSel B hn) hc hb

end Silmaril.Wasm.SpecTec.Sim.Round5.Target
