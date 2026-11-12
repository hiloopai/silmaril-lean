module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.DispatchD
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.Restrict
public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Thms
public import Silmaril.Wasm.SpecTec.Sim.FwdMem.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.Thms

/-!
# Round 7, memory SIMD: valid `BoundedSelM` configurations have typed `configVD` images

Round 5's `Round5.Target.typed_of_configOk_sel` shows that a valid `BoundedSel` configuration
has a typed `configV` image. This file re-runs it at `configVD`, on the extended domain
`BoundedSelM`, where memory SIMD code may occur at every depth of the code and of the store's
function bodies:

* `typedV_instrToVD_of`: an instruction whose bodies are typed is a typed `instr` at
  `instrToVD`. At a memory SIMD instruction this is round 6's `typedV_vecMemV` (the encoding
  `instrToVM` is against the IL type `instr`); at the four block forms the bodies are re-encoded
  by `instrsToVD`; elsewhere `instrToVD` is `instrToV`, and round 5's
  `Round5.Target.instrTypingSel_aux` applies;
* `instrTypingSelD_aux`, `typedV_instrsSelD`: valid, `instrBndM`, `instrSel` code is typed at
  `instrToVD`, by well-founded recursion on the instruction;
* `typedV_funcinstSelD`, `typedV_storeSelD`: the store at `storeVD`;
* `adminOk_typed_selD`, `adminsOk_typed_selD`: the active code at `adminsToVD`;
* `typedD_of_configOk_selM`: **`ConfigOk ∧ BoundedSelM → TypedD`**, in every `simEnv B`. This is
  the `typed` field of `OpenRM`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round6.MemSimd (memSimd)
open Round5.Target (instrSel instrsSel AdminSel AdminsSel StoreSel instrsSel_mem instrSel_bodies
  adminsSel_append adminsSel_expression)

variable {H : Type} {B : Builtins}

/-! ## `instrBndM` on bodies and sequences -/

/-- `instrToVD` on a sequence is a map. -/
theorem instrsToVD_eq_map : ∀ l : List Instr, instrsToVD l = l.map instrToVD
  | [] => rfl
  | i :: l => by simp only [instrsToVD, List.map_cons, instrsToVD_eq_map l]

/-- Every instruction of an `instrsBndM` sequence is `instrBndM`. -/
theorem instrsBndM_mem : ∀ {l : List Instr}, instrsBndM l = true → ∀ i ∈ l, instrBndM i = true
  | [], _ => fun _ hi => absurd hi List.not_mem_nil
  | _ :: _, h => by
    simp only [instrsBndM, Bool.and_eq_true] at h
    intro i hi
    rcases List.mem_cons.1 hi with rfl | hi
    · exact h.1
    · exact instrsBndM_mem h.2 i hi

/-- The bodies of an `instrBndM` instruction are `instrsBndM`. -/
theorem instrBndM_bodies {i : Instr} (h : instrBndM i = true) :
    ∀ b ∈ i.bodies, instrsBndM b = true := by
  cases i <;> simp_all [instrBndM, Instr.bodies]

/-- `instrsBndM` splits over `++`. -/
theorem instrsBndM_append : ∀ {a b : List Instr},
    instrsBndM (a ++ b) = true ↔ instrsBndM a = true ∧ instrsBndM b = true
  | [], b => by simp [instrsBndM]
  | x :: a, b => by
    simp only [List.cons_append, instrsBndM, Bool.and_eq_true]
    rw [instrsBndM_append]
    exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨⟨h₁, h₂⟩, h₃⟩, fun ⟨⟨h₁, h₂⟩, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

/-- `AdminsBndM` splits over `++`. -/
theorem adminsBndM_append : ∀ {a b : List Admin}, AdminsBndM (a ++ b) ↔ AdminsBndM a ∧ AdminsBndM b
  | [], b => by simp [AdminsBndM]
  | x :: a, b => by
    simp only [List.cons_append, AdminsBndM]
    rw [adminsBndM_append]
    exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨⟨h₁, h₂⟩, h₃⟩, fun ⟨⟨h₁, h₂⟩, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

/-- Source code is `AdminsBndM` when its instructions are `instrsBndM`. -/
theorem adminsBndM_expression : ∀ {l : List Instr}, instrsBndM l = true → AdminsBndM (expression l)
  | [], _ => trivial
  | _ :: l, h => by
    simp only [instrsBndM, Bool.and_eq_true] at h
    exact ⟨h.1, adminsBndM_expression h.2⟩

/-- `adminsToVD` of source code is `instrsToVD`. -/
theorem adminsToVD_expression : ∀ l : List Instr, adminsToVD (expression l) = instrsToVD l
  | [] => rfl
  | i :: l => by
    show adminToVD (.plain i) :: adminsToVD (expression l) = instrToVD i :: instrsToVD l
    rw [adminsToVD_expression l]
    rfl

/-! ## Instructions -/

/-- **Off the four block forms, a valid, `instrSel` instruction is a typed `instr` at
`instrToVM`** (which is `instrToVD` there): round 6's `typedV_vecMemV` at memory SIMD, round 5's
`Round5.Target.instrTypingSel_aux` elsewhere. -/
theorem typedV_instrToVM_other {C : Context} {i : Instr} {it : InstrType}
    (h₁ : ∀ bt body, i = .block bt body → False) (h₂ : ∀ bt body, i = .loop bt body → False)
    (h₃ : ∀ bt b₁ b₂, i = .if_ bt b₁ b₂ → False)
    (h₄ : ∀ bt cs body, i = .tryTable bt cs body → False)
    (hok : InstrOk C i it) (hsel : instrSel i = true) :
    TypedV (simEnv B) (.varT "instr" []) (Round6.MemSimd.instrToVM i) := by
  by_cases hm : memSimd i = true
  · exact Round6.MemSimd.typedV_vecMemV i hm
  · have hm' : memSimd i = false := by simpa using hm
    rw [Round6.MemSimd.instrToVM_of_not hm']
    exact Round5.Target.instrTypingSel_aux (Round5.SimdTy.simdTypingSel B) i C it hok
      (instrBnd_other h₁ h₂ h₃ h₄ hm') hsel

/-- **An instruction whose bodies are typed is a typed `instr` at `instrToVD`**, when it is
valid, `instrBndM` and `instrSel`. -/
theorem typedV_instrToVD_of {C : Context} (i : Instr) {it : InstrType} (hok : InstrOk C i it)
    (hb : instrBndM i = true) (hsel : instrSel i = true)
    (hbodies : ∀ b ∈ i.bodies, TypedV (simEnv B) instrsT (.list (instrsToVD b))) :
    TypedV (simEnv B) (.varT "instr" []) (instrToVD i) := by
  unfold instrToVD
  split
  · rename_i bt body
    exact FwdMem.typedV_instrCase rfl rfl (Round5.Pos.hasTyp_tup2 (Typing.typedV_blocktype bt)
      (hbodies body (by simp [Instr.bodies])))
  · rename_i bt body
    exact FwdMem.typedV_instrCase rfl rfl (Round5.Pos.hasTyp_tup2 (Typing.typedV_blocktype bt)
      (hbodies body (by simp [Instr.bodies])))
  · rename_i bt b₁ b₂
    exact FwdMem.typedV_instrCase rfl rfl (Round5.Pos.hasTyp_tup3 (Typing.typedV_blocktype bt)
      (hbodies b₁ (by simp [Instr.bodies])) (hbodies b₂ (by simp [Instr.bodies])))
  · rename_i bt cs body
    have hb' : cs.length < Round4.bnd32 ∧ instrsBndM body = true := by
      simpa [instrBndM] using hb
    have hcs : cs.length < 2 ^ 32 := hb'.1
    exact FwdMem.typedV_instrCase rfl rfl (Round5.Pos.hasTyp_tup3 (Typing.typedV_blocktype bt)
      (Round5.Pos.typedV_catches cs hcs) (hbodies body (by simp [Instr.bodies])))
  · rename_i h₁ h₂ h₃ h₄
    exact typedV_instrToVM_other h₁ h₂ h₃ h₄ hok hsel

/-- **Every valid, `instrBndM`, `instrSel` instruction is a typed `instr` at `instrToVD`**, by
well-founded recursion on the instruction. -/
theorem instrTypingSelD_aux :
    ∀ (i : Instr) (C : Context) (it : InstrType), InstrOk C i it → instrBndM i = true →
      instrSel i = true → TypedV (simEnv B) (.varT "instr" []) (instrToVD i)
  | i, C, it, hok, hb, hsel => typedV_instrToVD_of i hok hb hsel fun b hbm => by
      obtain ⟨C', it', hbo⟩ := Round5.Pos.instrOk_bodies hok b hbm
      rw [instrsToVD_eq_map]
      exact typedV_list_iff.2 fun u hu => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hu
        obtain ⟨C'', it'', hjo⟩ := Round5.Pos.instrsOk_mem hbo j hj
        have := Round5.Pos.sizeOf_lt_of_body hbm hj
        exact instrTypingSelD_aux j C'' it'' hjo (instrsBndM_mem (instrBndM_bodies hb b hbm) j hj)
          (instrsSel_mem (instrSel_bodies hsel b hbm) j hj)
termination_by i => sizeOf i

/-- **A valid, `instrsBndM`, `instrsSel` sequence is a typed `instr*` at `instrsToVD`.** -/
theorem typedV_instrsSelD {C : Context} {is : List Instr} {it : InstrType} (h : InstrsOk C is it)
    (hb : instrsBndM is = true) (hsel : instrsSel is = true) :
    TypedV (simEnv B) instrsT (.list (instrsToVD is)) := by
  rw [instrsToVD_eq_map]
  exact typedV_list_iff.2 fun u hu => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hu
    obtain ⟨C', it', hok⟩ := Round5.Pos.instrsOk_mem h i hi
    exact instrTypingSelD_aux i C' it' hok (instrsBndM_mem hb i hi) (instrsSel_mem hsel i hi)

/-! ## Stores -/

/-- A valid Wasm function's `instrsBndM`, `instrsSel` code is a typed `funccode` at
`instrsToVD`. -/
theorem typedV_funccodeSelD {C : Context} {fn : Func} {d : DefType} (hf : FuncOk C fn d)
    (hb : instrsBndM fn.body = true) (hsel : instrsSel fn.body = true) :
    TypedV (simEnv B) (.varT "funccode" []) (.case "FUNC" (.tuple
      [Silmaril.SpecTec.Equiv.Execution.pctV fn.type.toNat,
       .list (fn.locals.map fun t => .case "LOCAL" (Encode.toValue t)),
       .list (instrsToVD fn.body)])) := by
  obtain ⟨-, -, -, hbody⟩ := hf
  exact Typing.typedV_closedCase Round5.Pos.findTyp_funccode rfl (Round5.Pos.hasTyp_tup3
    (Round5.Pos.typedV_typeidxNat fn.type.value.isLt) (Round5.Pos.typedV_locals fn.locals)
    (Round5.Pos.typedV_expr (typedV_instrsSelD hbody hb hsel)))

/-- **A valid, `FuncBndM`, export-free function instance without `FloatMissel` code is a typed
`funcinst` at `funcInstVD`.** -/
theorem typedV_funcinstSelD (hn : H → String) {s : Store H} {fi : FuncInst H}
    (hok : FuncInstOk s fi) (hb : FuncBndM fi) (he : fi.module.exports = [])
    (hsel : ∀ fn, fi.code = .wasm fn → instrsSel fn.body = true) :
    TypedV (simEnv B) funcinstT (funcInstVD hn fi) := by
  have hcode : TypedV (simEnv B) (.varT "funccode" []) (match fi.code with
      | .wasm fn => .case "FUNC" (.tuple [Silmaril.SpecTec.Equiv.Execution.pctV fn.type.toNat,
          .list (fn.locals.map fun t => .case "LOCAL" (Encode.toValue t)),
          .list (instrsToVD fn.body)])
      | .host h => .case "_HOSTFUNC" (.text (hn h))) := by
    cases hok with
    | wasm _ _ hc hf _ =>
      rw [hc]
      exact typedV_funccodeSelD hf (hb.2.2 _ hc) (hsel _ hc)
    | host _ _ hc =>
      rw [hc]
      exact Typing.typedV_closedCase Round5.Pos.findTyp_funccode rfl (hasTyp_textT_iff.2 ⟨_, rfl⟩)
  exact Round5.Pos.typedV_struct ConfigOk.findTyp_funcinst (Round5.Pos.hasTypFields_cons_of
    (Round5.Pos.typedV_deftype fi.type hb.1) (Round5.Pos.hasTypFields_cons_of
      (Round5.Pos.typedV_moduleinst_ne _ hb.2.1 he) (Round5.Pos.hasTypFields_one hcode)))

/-- **A valid, `StoreBndM`, export-free store without `FloatMissel` function bodies is a typed
`store` at `storeVD`.** -/
theorem typedV_storeSelD (hn : H → String) (s : Store H) (hs : StoreOk s) (hb : StoreBndM s)
    (he : Round5.Pos.StoreNE s) (hsel : StoreSel s) : TypedV (simEnv B) storeT (storeVD hn s) :=
  Round5.Pos.typedV_struct ConfigOk.findTyp_store' <|
    Round5.Pos.hasTypFields_cons_of (Round5.Pos.typedV_map fun ti hti => Round5.Pos.typedV_taginst ti (hb.tags ti hti)) <|
    Round5.Pos.hasTypFields_cons_of
      (Round5.Pos.typedV_map fun gi hgi => Round5.Pos.typedV_globalinst gi (hb.globals gi hgi)) <|
    Round5.Pos.hasTypFields_cons_of (Round5.Pos.typedV_map fun mi _ => Round5.Pos.typedV_meminst mi) <|
    Round5.Pos.hasTypFields_cons_of
      (Round5.Pos.typedV_map fun ti hti => Round5.Pos.typedV_tableinst ti (hb.tables ti hti)) <|
    Round5.Pos.hasTypFields_cons_of (Round5.Pos.typedV_map fun fi hfi =>
      typedV_funcinstSelD hn (hs.funcs fi hfi) (hb.funcs fi hfi) (he fi hfi) (hsel fi hfi)) <|
    Round5.Pos.hasTypFields_cons_of (Round5.Pos.typedV_map fun di _ => Round5.Pos.typedV_datainst di) <|
    Round5.Pos.hasTypFields_cons_of
      (Round5.Pos.typedV_map fun ei hei => Round5.Pos.typedV_eleminst ei (hb.elems ei hei)) <|
    Round5.Pos.hasTypFields_cons_of
      (Round5.Pos.typedV_map fun si hsi => Round5.Pos.typedV_structinst si (hb.structs si hsi)) <|
    Round5.Pos.hasTypFields_cons_of
      (Round5.Pos.typedV_map fun ai hai => Round5.Pos.typedV_arrayinst ai (hb.arrays ai hai)) <|
    Round5.Pos.hasTypFields_one (Round5.Pos.typedV_map fun e _ =>
      Typing.typedV_exninst e (typedV_list_iff.2 fun u hu => by
        obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
        exact Typing.typedV_val v))

/-! ## Configurations -/

set_option maxRecDepth 100000 in
/-- A label with typed components is typed, at `adminToVD`. -/
theorem typedV_labelD {n : Nat} {cont : List Instr} {body : List Admin}
    (h₁ : TypedV (simEnv B) nT (.num (.natN n)))
    (h₂ : TypedV (simEnv B) instrsT (.list (instrsToVD cont)))
    (h₃ : TypedV (simEnv B) instrsT (.list (adminsToVD body))) :
    TypedV (simEnv B) instrsT (.list [adminToVD (.label n cont body)]) :=
  FwdMem.typedV_admin3_intro rfl rfl h₁ h₂ h₃

set_option maxRecDepth 100000 in
/-- A handler with typed components is typed, at `adminToVD`. -/
theorem typedV_handlerD {n : Nat} {cs : List Catch} {body : List Admin}
    (h₁ : TypedV (simEnv B) nT (.num (.natN n)))
    (h₂ : TypedV (simEnv B) catchesT (.list (cs.map Encode.toValue)))
    (h₃ : TypedV (simEnv B) instrsT (.list (adminsToVD body))) :
    TypedV (simEnv B) instrsT (.list [adminToVD (.handler n cs body)]) :=
  FwdMem.typedV_admin3_intro rfl rfl h₁ h₂ h₃

set_option maxRecDepth 100000 in
/-- A frame with typed components is typed, at `adminToVD`. -/
theorem typedV_frameD {n : Nat} {f : Frame} {body : List Admin}
    (h₁ : TypedV (simEnv B) nT (.num (.natN n))) (h₂ : TypedV (simEnv B) frameT (frameV f))
    (h₃ : TypedV (simEnv B) instrsT (.list (adminsToVD body))) :
    TypedV (simEnv B) instrsT (.list [adminToVD (.frame n f body)]) :=
  FwdMem.typedV_admin3_intro rfl rfl h₁ h₂ h₃

variable {hn : H → String}

mutual
/-- **Every valid, `AdminBndM`, export-free administrative instruction without `FloatMissel`
code is typed at `adminToVD`.** -/
theorem adminOk_typed_selD (K : Round5.Target.PosTypingSel B hn) {s : Store H} :
    ∀ {C : Context} {a : Admin} {it : InstrType}, AdminOk s C a it → AdminBndM a →
      Round5.Pos.AdminNE a → AdminSel a → TypedV (simEnv B) instrsT (.list [adminToVD a])
  | _, _, _, .plain h, hb, _, hs => typedV_list_single.2 (instrTypingSelD_aux _ _ _ h hb hs)
  | _, _, _, .callRefType hok _, hb, _, _ => typedV_list_single.2 (K.callRefType _ hok hb)
  | _, _, _, .returnCallRefType hok _ _ _ _, hb, _, _ =>
    typedV_list_single.2 (K.returnCallRefType _ hok hb)
  | _, _, _, .ref _, _, _, _ => typedV_list_single.2 (Round4.typedV_refAdmin _)
  | _, _, _, .label (n := n) (cont := cont) _ hc hbody, hb, he, hs => by
    have hcont := adminsOk_typed_selD K hc (adminsBndM_expression hb.1)
      (Round5.Pos.adminsNE_expression cont) (adminsSel_expression hs.1)
    rw [adminsToVD_expression] at hcont
    exact typedV_labelD ((Typing.stateTyping_simEnv B).nat n) hcont
      (adminsOk_typed_selD K hbody hb.2 he hs.2)
  | _, _, _, .frame (n := n) hf _ hbody _, hb, he, hs =>
    typedV_frameD ((Typing.stateTyping_simEnv B).nat n)
      (Round5.Target.frame_typed_sel K hf hb.1 he.1) (adminsOk_typed_selD K hbody hb.2 he.2 hs)
  | _, _, _, .handler (n := n) _ hbody, hb, he, hs =>
    typedV_handlerD ((Typing.stateTyping_simEnv B).nat n)
      (typedV_list_iff.2 fun u hu => by
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 hu
        exact Round4.typedV_catch c)
      (adminsOk_typed_selD K hbody hb he hs)
  | _, _, _, .trap _, _, _, _ => typedV_list_single.2 Round4.typedV_trap
  | _, _, _, .throwRefInits _, _, _, _ => typedV_list_single.2 Round4.typedV_throwRef

/-- **Every valid, `AdminsBndM`, export-free code sequence without `FloatMissel` code is typed at
`adminsToVD`.** -/
theorem adminsOk_typed_selD (K : Round5.Target.PosTypingSel B hn) {s : Store H} :
    ∀ {C : Context} {l : List Admin} {it : InstrType}, AdminsOk s C l it → AdminsBndM l →
      Round5.Pos.AdminsNE l → AdminsSel l → TypedV (simEnv B) instrsT (.list (adminsToVD l))
  | _, _, _, .nil, _, _, _ => typedV_list_nil
  | _, _, _, .single h, hb, he, hs => adminOk_typed_selD K h hb.1 he.1 hs.1
  | _, _, _, .seq h₁ _ h₂, hb, he, hs => by
    obtain ⟨hb₁, hb₂⟩ := adminsBndM_append.1 hb
    obtain ⟨he₁, he₂⟩ := Round5.Pos.adminsNE_append.1 he
    obtain ⟨hs₁, hs₂⟩ := adminsSel_append.1 hs
    rw [adminsToVD_append]
    exact typedV_list_append.2
      ⟨adminsOk_typed_selD K h₁ hb₁ he₁ hs₁, adminsOk_typed_selD K h₂ hb₂ he₂ hs₂⟩
  | _, _, _, .cons ha _ hl, hb, he, hs => by
    have h₁ := adminOk_typed_selD K ha hb.1 he.1 hs.1
    have h₂ := adminsOk_typed_selD K hl hb.2 he.2 hs.2
    exact typedV_list_cons_iff.2 ⟨typedV_list_single.1 h₁, h₂⟩
  | _, _, _, .sub h _ _, hb, he, hs => adminsOk_typed_selD K h hb he hs
  | _, _, _, .frame h _, hb, he, hs => adminsOk_typed_selD K h hb he hs
end

/-- **`ConfigOk ∧ BoundedSelM → TypedD`**, in every `simEnv B`: a valid configuration in the
extended domain has a typed `configVD` image. This is the `typed` field of `OpenRM`. -/
theorem typedD_of_configOk_selM (B : Builtins) (hn : H → String) {c : Config H}
    {ts : List CValType} (hc : ConfigOk c ts) (hb : BoundedSelM c) : TypedD (simEnv B) hn c := by
  obtain ⟨C, ⟨hs, hf⟩, hcode⟩ := hc
  have K := Round5.Target.posTypingSel B hn
  have T := typingFactsD_simEnv B hn
  exact (T.config c).2 ⟨(T.state _ _).2
    ⟨typedV_storeSelD hn _ hs hb.1.1.storeBnd hb.1.2.store hb.2.store,
      Round5.Target.frame_typed_sel K hf hb.1.1.frame hb.1.2.frame⟩,
    adminsOk_typed_selD K hcode hb.1.1.code hb.1.2.code hb.2.code⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
