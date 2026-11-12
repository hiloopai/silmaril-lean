module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.FwdRef2.Inj
public import Silmaril.Wasm.SpecTec.Sim.ConfigOk.Thms
public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Thms

/-!
# Round 5, pass 3, track fwdref: `storeV` is injective on typed store images

* `goodV_typed`: the IL typing of `instr` is a good predicate (`GoodV`). It excludes the junk value
  `.tuple []` and passes to the bodies of `block`, `loop`, `if` and `try_table`. So `instrToV`
  is injective at typed images (`instrToV_inj_typed`).
* `storeV_inj_typed`: `storeV hn` is injective on stores whose image is a typed `store`, for an
  injective `hn`. The only components whose encodings are not injective outright are the function
  bodies. A typed `store` image types every function body as `expr = instr*`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d271)

variable {B : Builtins} {H : Type}

/-- A typed `instr`, in the empty scope. -/
abbrev InstrG (B : Builtins) (v : Value) : Prop :=
  HasTyp (simEnv B) VarEnv.empty (.varT "instr" []) v

/-- The `CODE` field of `funcInstV`. -/
def funcInstCodeV (hn : H → String) : FuncCode H → Value
  | .wasm fn => .case "FUNC" (.tuple [pctV fn.type.toNat,
      .list (fn.locals.map fun t => .case "LOCAL" (Encode.toValue t)),
      .list (instrsToV fn.body)])
  | .host h => .case "_HOSTFUNC" (.text (hn h))

theorem funcInstV_eq (hn : H → String) (ty : _) (m : ModuleInst) (c : FuncCode H) :
    funcInstV hn ⟨ty, m, c⟩ = .struct [("TYPE", CT.defType ty),
      ("MODULE", moduleInstToValue CT m), ("CODE", funcInstCodeV hn c)] := by
  cases c <;> rfl

theorem valsOnly_bindVal {σ : VarEnv} (h : ValsOnly σ) (x : IL.Id) (w : Value) :
    ValsOnly (σ.bindVal x w) := h

/-- The elements of a typed `instr*`, in a term-only scope, are typed `instr`s. -/
theorem instrs_elems {σ : VarEnv} (hσ : ValsOnly σ) {vs : List Value}
    (h : HasTyp (simEnv B) σ instrsT (.list vs)) : ∀ v ∈ vs, InstrG B v := by
  obtain ⟨l, hl, hall⟩ := hasTyp_iterT_list_iff.1 h
  cases hl
  intro v hv
  exact IntNumeric.hasTyp_varT_nil_congr hσ ⟨rfl, rfl, rfl⟩ (hasTypList_iff.1 hall v hv)

theorem tup2_snd {env : Env} {σ : VarEnv} {a b : IL.Id} {τ₁ τ₂ : Typ} {u v : Value}
    (h : HasTyp env σ (.tupT [.mk a τ₁, .mk b τ₂]) (.tuple [u, v])) :
    HasTyp env (σ.bindVal a u) τ₂ v := by
  obtain ⟨_, he, ht⟩ := hasTyp_tupT_iff.1 h
  obtain rfl := (Value.tuple.inj he).symm
  obtain ⟨_, _, he₁, -, ht₁⟩ := hasTypTup_cons_iff.1 ht
  obtain ⟨rfl, rfl⟩ := List.cons.inj he₁
  obtain ⟨_, _, he₂, h₂, -⟩ := hasTypTup_cons_iff.1 ht₁
  obtain ⟨rfl, -⟩ := List.cons.inj he₂
  exact h₂

theorem tup3_inv {env : Env} {σ : VarEnv} {a b c : IL.Id} {τ₁ τ₂ τ₃ : Typ} {u₁ u₂ u₃ : Value}
    (h : HasTyp env σ (.tupT [.mk a τ₁, .mk b τ₂, .mk c τ₃]) (.tuple [u₁, u₂, u₃])) :
    HasTyp env (σ.bindVal a u₁) τ₂ u₂ ∧ HasTyp env ((σ.bindVal a u₁).bindVal b u₂) τ₃ u₃ := by
  obtain ⟨_, he, ht⟩ := hasTyp_tupT_iff.1 h
  obtain rfl := (Value.tuple.inj he).symm
  obtain ⟨_, _, he₁, -, ht₁⟩ := hasTypTup_cons_iff.1 ht
  obtain ⟨rfl, rfl⟩ := List.cons.inj he₁
  obtain ⟨_, _, he₂, h₂, ht₂⟩ := hasTypTup_cons_iff.1 ht₁
  obtain ⟨rfl, rfl⟩ := List.cons.inj he₂
  obtain ⟨_, _, he₃, h₃, -⟩ := hasTypTup_cons_iff.1 ht₂
  obtain ⟨rfl, -⟩ := List.cons.inj he₃
  exact ⟨h₂, h₃⟩

/-! ## The block cases of `instr` -/

set_option maxRecDepth 100000 in
theorem findCase_block : ∃ τ, IntNumeric.findCase (IntNumeric.recCases Original.d271 0 0) "BLOCK" =
    some (.tupT [.mk "blocktype" τ, .mk "instr*" instrsT], []) := ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem findCase_loop : ∃ τ, IntNumeric.findCase (IntNumeric.recCases Original.d271 0 0) "LOOP" =
    some (.tupT [.mk "blocktype" τ, .mk "instr*" instrsT], []) := ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem findCase_if : ∃ τ, IntNumeric.findCase (IntNumeric.recCases Original.d271 0 0)
    "IF%%ELSE%" = some (.tupT [.mk "blocktype" τ, .mk "instr*" instrsT, .mk "instr*" instrsT],
      []) := ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem findCase_tryTable : ∃ τ τ', IntNumeric.findCase (IntNumeric.recCases Original.d271 0 0)
    "TRY_TABLE" = some (.tupT [.mk "blocktype" τ, .mk "_" τ', .mk "instr*" instrsT], []) :=
  ⟨_, _, rfl⟩

/-- **Typed `instr` images are good.** -/
theorem goodV_typed (B : Builtins) : GoodV (InstrG B) where
  junk := IntNumeric.not_hasTyp_instr_tuple B ⟨rfl, rfl, rfl⟩ []
  block a vs h := by
    obtain ⟨τ, hf⟩ := findCase_block
    exact instrs_elems ⟨rfl, rfl, rfl⟩
      (tup2_snd (IntNumeric.hasTyp_instr_inv ⟨rfl, rfl, rfl⟩ h hf))
  loop a vs h := by
    obtain ⟨τ, hf⟩ := findCase_loop
    exact instrs_elems ⟨rfl, rfl, rfl⟩
      (tup2_snd (IntNumeric.hasTyp_instr_inv ⟨rfl, rfl, rfl⟩ h hf))
  ifThen a vs ws h := by
    obtain ⟨τ, hf⟩ := findCase_if
    exact instrs_elems ⟨rfl, rfl, rfl⟩
      (tup3_inv (IntNumeric.hasTyp_instr_inv ⟨rfl, rfl, rfl⟩ h hf)).1
  ifElse a vs ws h := by
    obtain ⟨τ, hf⟩ := findCase_if
    exact instrs_elems ⟨rfl, rfl, rfl⟩
      (tup3_inv (IntNumeric.hasTyp_instr_inv ⟨rfl, rfl, rfl⟩ h hf)).2
  tryTable a c vs h := by
    obtain ⟨τ, τ', hf⟩ := findCase_tryTable
    exact instrs_elems ⟨rfl, rfl, rfl⟩
      (tup3_inv (IntNumeric.hasTyp_instr_inv ⟨rfl, rfl, rfl⟩ h hf)).2

/-- **`instrToV` is injective at typed images.** -/
theorem instrToV_inj_typed {i j : Instr} (hi : InstrG B (instrToV i))
    (h : instrToV i = instrToV j) : i = j :=
  instrToV_inj (goodV_typed B) hi h

/-- **`instrsToV` is injective at typed images.** -/
theorem instrsToV_inj_typed : ∀ {b b' : List Instr}, (∀ v ∈ instrsToV b, InstrG B v) →
    instrsToV b = instrsToV b' → b = b'
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [instrsToV] at h
  | _ :: _, [], _, h => by simp [instrsToV] at h
  | k :: b, k' :: b', hb, h => by
      simp only [instrsToV, List.cons.injEq] at h
      rw [instrToV_inj_typed (hb _ (List.Mem.head _)) h.1,
        instrsToV_inj_typed (fun v hv => hb v (List.Mem.tail _ hv)) h.2]

/-! ## Function instances -/

set_option maxRecDepth 100000 in
theorem findTyp_funccode : ∃ cs, (simEnv B).findTyp? "funccode" =
    some ([], [.instD [] [] (.variantT cs)]) ∧
    IntNumeric.findCase cs "FUNC" = some (.tupT [.mk "typeidx" (.varT "typeidx" []),
      .mk "local*" (.iterT (.varT "local" []) .list), .mk "expr" (.varT "expr" [])], []) :=
  ⟨_, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_expr : (simEnv B).findTyp? "expr" = some ([], [.instD [] [] (.aliasT instrsT)]) :=
  rfl

/-- A typed `expr` is a typed `instr*`, in the empty scope. -/
theorem hasTyp_expr_inv {σ : VarEnv} (hσ : ValsOnly σ) {v : Value}
    (h : HasTyp (simEnv B) σ (.varT "expr" []) v) : HasTyp (simEnv B) VarEnv.empty instrsT v := by
  have hl : localTyp? σ "expr" [] = none := by simp [localTyp?, VarEnv.findTyp?, hσ.1]
  obtain ⟨td, ws, htd', -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [findTyp_expr] at htd'
  obtain rfl := (Option.some.inj htd').symm
  rcases hasTypInsts_cons_inv hi with ⟨σ', hm, hd⟩ | hrest
  · obtain rfl := IntNumeric.matchArgs_nil_scope hm
    exact hasTypDef_aliasT_iff.1 hd
  · exact absurd hrest not_hasTypInsts_nil

/-- The body of a function instance with a typed image is typed. -/
theorem body_typed {hn : H → String} {ty m fn}
    (hf : HasTyp (simEnv B) VarEnv.empty (.varT "funcinst" []) (funcInstV hn ⟨ty, m, .wasm fn⟩)) :
    ∀ v ∈ instrsToV fn.body, InstrG B v := by
  have hF := ConfigOk.hasTypFields_of_closedStruct ConfigOk.valsOnly_empty
    ConfigOk.findTyp_funcinst hf
  simp only [List.forall₂_cons, ConfigOk.fieldTyp] at hF
  obtain ⟨cs, htd, hfc⟩ := findTyp_funccode (B := B)
  have hc := IntNumeric.hasTyp_of_hasTypCase (Typing.hasTypCase_of_closedVariant htd hF.2.2.1) hfc
  exact instrs_elems ⟨rfl, rfl, rfl⟩ (hasTyp_expr_inv ⟨rfl, rfl, rfl⟩ (tup3_inv hc).2)

/-- Function code is determined by its image, given a typed body. -/
theorem codeV_inj {hn : H → String} (hinj : Function.Injective hn) {c c' : FuncCode H}
    (hb : ∀ fn, c = .wasm fn → ∀ v ∈ instrsToV fn.body, InstrG B v)
    (h : funcInstCodeV hn c = funcInstCodeV hn c') : c = c' := by
  cases c with
  | wasm fn =>
      show FuncCode.wasm fn = c'
      cases c' with
      | wasm fn' =>
          show FuncCode.wasm fn = .wasm fn'
          obtain ⟨t, ls, body⟩ := fn
          obtain ⟨t', ls', body'⟩ := fn'
          have h' : t.toNat = t'.toNat ∧ ls.map (fun t => Value.case "LOCAL" (Encode.toValue t)) =
              ls'.map (fun t => Value.case "LOCAL" (Encode.toValue t)) ∧
              instrsToV body = instrsToV body' := by
            simpa only [funcInstCodeV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
              Value.list.injEq, pctV_eq_iff, true_and, and_true] using h
          have hl : ls = ls' := List.map_injective_iff.2 (fun a b hab => by simpa using hab) h'.2.1
          have hbd : body = body' := instrsToV_inj_typed (hb _ rfl) h'.2.2
          rw [Silmaril.Wasm.Idx.toNat_injective h'.1, hl, hbd]
      | host _ => simp [funcInstCodeV] at h
  | host x =>
      cases c' with
      | wasm _ => simp [funcInstCodeV] at h
      | host x' =>
          have hx : hn x = hn x' := by simpa [funcInstCodeV] using h
          rw [hinj hx]

/-- `funcInstV` is injective at a typed image. -/
theorem funcInstV_inj_typed {hn : H → String} (hinj : Function.Injective hn) {f f' : FuncInst H}
    (hf : HasTyp (simEnv B) VarEnv.empty (.varT "funcinst" []) (funcInstV hn f))
    (h : funcInstV hn f = funcInstV hn f') : f = f' := by
  obtain ⟨ty, m, code⟩ := f
  obtain ⟨ty', m', code'⟩ := f'
  have h' : CT.defType ty = CT.defType ty' ∧ moduleInstToValue CT m = moduleInstToValue CT m' ∧
      funcInstCodeV hn code = funcInstCodeV hn code' := by
    rw [funcInstV_eq, funcInstV_eq] at h
    simpa only [Value.struct.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] using h
  have hb : ∀ fn, code = .wasm fn → ∀ v ∈ instrsToV fn.body, InstrG B v := by
    rintro fn rfl
    exact body_typed hf
  rw [CT.defType_inj h'.1, moduleInstToValue_inj CT h'.2.1, codeV_inj hinj hb h'.2.2]

/-! ## The other store components -/

theorem globalInstV_inj : Function.Injective globalInstV := by
  intro a b h
  obtain ⟨t, v⟩ := a
  obtain ⟨t', v'⟩ := b
  simp only [globalInstV, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq, true_and,
    and_true] at h
  simp only [GlobalInst.mk.injEq]
  exact ⟨CT.globalType_inj h.1, Typing.valV_injective h.2⟩

theorem refToValue_ne_pack (r : Ref) (w : Value) : refToValue r ≠ .case "PACK" w := by
  intro h
  have hh := Typing.refToValue_head r
  rw [h] at hh
  cases r <;> simp [Typing.headOf, Typing.refHead] at hh

/-- A value's image is never a `PACK`. -/
theorem valV_ne_pack (v : Val) (w : Value) : valV v ≠ .case "PACK" w := by
  cases v with
  | num n => simp [valV]
  | vec b => simp [valV]
  | ref r => exact refToValue_ne_pack r w

theorem fieldValV_inj : Function.Injective fieldValV := by
  intro a b h
  cases a with
  | val v =>
      cases b with
      | val v' => rw [Typing.valV_injective h]
      | pack p x => exact absurd h (valV_ne_pack v _)
  | pack p x =>
      cases b with
      | val v' => exact absurd h.symm (valV_ne_pack v' _)
      | pack p' x' =>
          simp only [fieldValV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
            toValue_eq_iff, pctV_eq_iff, true_and, and_true] at h
          obtain ⟨rfl, hx⟩ := h
          rw [BitVec.toNat_inj.1 hx]

theorem structInstV_inj : Function.Injective structInstV := by
  intro a b h
  obtain ⟨t, fs⟩ := a
  obtain ⟨t', fs'⟩ := b
  simp only [structInstV, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq, Value.list.injEq,
    true_and, and_true] at h
  simp only [StructInst.mk.injEq]
  exact ⟨CT.defType_inj h.1, List.map_injective_iff.2 fieldValV_inj h.2⟩

theorem arrayInstV_inj : Function.Injective arrayInstV := by
  intro a b h
  obtain ⟨t, fs⟩ := a
  obtain ⟨t', fs'⟩ := b
  simp only [arrayInstV, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq, Value.list.injEq,
    true_and, and_true] at h
  simp only [ArrayInst.mk.injEq]
  exact ⟨CT.defType_inj h.1, List.map_injective_iff.2 fieldValV_inj h.2⟩

theorem exnInstV_inj : Function.Injective exnInstV := by
  intro a b h
  obtain ⟨t, fs⟩ := a
  obtain ⟨t', fs'⟩ := b
  simp only [exnInstV, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq, Value.list.injEq,
    Value.num.injEq, Num.natN.injEq, true_and, and_true] at h
  simp only [ExnInst.mk.injEq]
  exact ⟨h.1, List.map_injective_iff.2 Typing.valV_injective h.2⟩

/-- A map is injective on the elements of the left list where `f` is. -/
theorem map_inj_on {α : Type} {f : α → Value} :
    ∀ {l l' : List α}, (∀ a ∈ l, ∀ b, f a = f b → a = b) → l.map f = l'.map f → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: l, b :: l', hl, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hl a (List.Mem.head _) b h.1, map_inj_on (fun x hx => hl x (List.Mem.tail _ hx)) h.2]

/-- The function instances of a store with a typed image are typed. -/
theorem funcs_typed {hn : H → String} {s : Store H}
    (hs : TypedV (simEnv B) storeT (storeV hn s)) :
    ∀ f ∈ s.funcs, HasTyp (simEnv B) VarEnv.empty (.varT "funcinst" []) (funcInstV hn f) := by
  have hF := ConfigOk.hasTypFields_of_closedStruct ConfigOk.valsOnly_empty ConfigOk.findTyp_store'
    (hs _ ConfigOk.valsOnly_empty)
  have hfu : HasTyp (simEnv B) VarEnv.empty (.iterT (.varT "funcinst" []) .list)
      (.list (s.funcs.map (funcInstV hn))) := by
    simp only [List.forall₂_cons, ConfigOk.fieldTyp] at hF
    exact hF.2.2.2.2.1
  obtain ⟨l, hl, hall⟩ := hasTyp_iterT_list_iff.1 hfu
  intro f hf
  exact hasTypList_iff.1 hall _ (by rw [← Value.list.inj hl]; exact List.mem_map_of_mem hf)

/-- **`storeV` is injective on stores with typed images**, for an injective host naming. -/
theorem storeV_inj_typed {hn : H → String} (hinj : Function.Injective hn) {s s' : Store H}
    (hs : TypedV (simEnv B) storeT (storeV hn s)) (h : storeV hn s = storeV hn s') : s = s' := by
  have hft := funcs_typed hs
  obtain ⟨tg, gl, me, ta, fu, da, el, st, ar, ex⟩ := s
  obtain ⟨tg', gl', me', ta', fu', da', el', st', ar', ex'⟩ := s'
  have h' : tg.map (tagInstToValue CT) = tg'.map (tagInstToValue CT) ∧
      gl.map globalInstV = gl'.map globalInstV ∧ me.map memInstToValue = me'.map memInstToValue ∧
      ta.map (tableInstToValue CT) = ta'.map (tableInstToValue CT) ∧
      fu.map (funcInstV hn) = fu'.map (funcInstV hn) ∧
      da.map dataInstToValue = da'.map dataInstToValue ∧
      el.map (elemInstToValue CT) = el'.map (elemInstToValue CT) ∧
      st.map structInstV = st'.map structInstV ∧ ar.map arrayInstV = ar'.map arrayInstV ∧
      ex.map exnInstV = ex'.map exnInstV := by
    simpa only [storeV, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq, Value.list.injEq,
      true_and, and_true] using h
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ := h'
  have hfu : fu = fu' := map_inj_on (fun f hf f' hff => funcInstV_inj_typed hinj (hft f hf) hff) h₅
  rw [List.map_injective_iff.2 (tagInstToValue_inj CT) h₁,
    List.map_injective_iff.2 globalInstV_inj h₂,
    List.map_injective_iff.2 memInstToValue_inj h₃,
    List.map_injective_iff.2 (tableInstToValue_inj CT) h₄, hfu,
    List.map_injective_iff.2 dataInstToValue_inj h₆,
    List.map_injective_iff.2 (elemInstToValue_inj CT) h₇,
    List.map_injective_iff.2 structInstV_inj h₈, List.map_injective_iff.2 arrayInstV_inj h₉,
    List.map_injective_iff.2 exnInstV_inj h₁₀]

end Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2
