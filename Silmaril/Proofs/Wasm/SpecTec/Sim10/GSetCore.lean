module

public import Silmaril.Wasm.Versions.Thms
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.SpecTec.Sim10.Whole.Defs

/-!
# `global.set` operands in a typed Core image

The Core 3.0 side of deriving `GSetOk` from validation. Write `sC` for a Core store with
`StoreOk sC` and `fC` for a Core frame with `FrameOk sC fC Cf`.

* `infix_typed`: a typed sequence types each of its non-empty infixes, in a context that differs
  only in its locals.
* `globalSet_core`: in a typed sequence, the operand of a `global.set x` redex has the value type
  of the global `x` names, read in the store.
* `gsetOk_of_core`: the induction over V1's `ActiveF`. Let a V1 configuration be related to a Core
  one by the copied `Lime1 → Core` simulation relation (`Lime1.Execution.Sim`, through the lock-step
  `V1 → Lime1` transport `Config.toLime`), and let the Core configuration be typed (`ConfigOk`).
  Then the V1 configuration satisfies `GSetOk`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Valid

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## Core inversions -/

theorem forall₂_last {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β} {a : α} {b : β}
    (h : List.Forall₂ R (l₁ ++ [a]) (l₂ ++ [b])) : R a b := by
  have h' := List.forall₂_reverse_iff.mpr h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at h'
  cases h' with
  | cons hab _ => exact hab

theorem initLocals_globals (C : Context) (xs : List Nat) : (C.initLocals xs).globals = C.globals := by
  obtain ⟨L, hL, -⟩ := C.initLocals_spec xs
  rw [hL]

/-- A typed sequence types each of its non-empty suffixes, after initialising some locals. -/
theorem suffix_typed {s : Store H} {C : Context} {L₁ w : List Admin} {it : InstrType}
    (h : AdminsOk s C (L₁ ++ w) it) (hw : w ≠ []) (hC : C.Wf) :
    ∃ xs it', AdminsOk s (C.initLocals xs) w it' := by
  obtain ⟨_, xs₁, _, -, h₂, -⟩ := AdminsOk.split h hC L₁ w rfl hw
  exact ⟨xs₁, _, h₂⟩

/-- A typed sequence types each of its prefixes. -/
theorem prefix_typed {s : Store H} {C : Context} {w L₂ : List Admin} {it : InstrType}
    (h : AdminsOk s C (w ++ L₂) it) (hC : C.Wf) : ∃ it', AdminsOk s C w it' := by
  by_cases hL : L₂ = []
  · subst hL
    exact ⟨it, by simpa using h⟩
  · obtain ⟨_, _, _, h₁, -, -⟩ := AdminsOk.split h hC w L₂ rfl hL
    exact ⟨_, h₁⟩

/-- **A typed sequence types each of its non-empty infixes**, in a well-formed context with the
same globals. -/
theorem infix_typed {s : Store H} {C : Context} {L₁ w L₂ : List Admin} {it : InstrType}
    (h : AdminsOk s C (L₁ ++ w ++ L₂) it) (hw : w ≠ []) (hC : C.Wf) :
    ∃ C' it', AdminsOk s C' w it' ∧ C'.globals = C.globals ∧ C'.Wf := by
  rw [List.append_assoc] at h
  obtain ⟨xs, it₁, h₁⟩ := suffix_typed h (by simp [hw]) hC
  obtain ⟨it', h'⟩ := prefix_typed h₁ (hC.initLocals xs)
  exact ⟨_, it', h', initLocals_globals C xs, hC.initLocals xs⟩

/-- A typed `global.set x` redex: the global `x` of the context is mutable at the operand's
number type. -/
theorem globalSet_ctx {s : Store H} (hs : StoreOk s) (hts : StoreTypesOk s) {C : Context}
    (hC : C.Wf) {n : NumVal} {x : GlobalIdx} {it : InstrType}
    (h : AdminsOk s C [Val.toAdmin (.num n), .plain (.globalSet x)] it) :
    C.globals[x.toNat]? = some ⟨.var, .num n.type⟩ := by
  obtain ⟨tv, F, it₁, hv, hi, -, hp, -, -⟩ := AdminsOk.redex1_inv hs hts hC h
  obtain ⟨t, ht, rfl⟩ := hi.globalSet_invVar
  have hsub : Sub C.toTypeCtx tv t := forall₂_last hp
  have htv : tv = .num n.type := by cases hv; rfl
  have htn : t = .num n.type := Sub.num_fwd (htv ▸ hsub)
  rw [← htn]
  exact ht

/-- A mutable global of a frame context at a number type is stored at that type. -/
theorem global_type_of_ctx {s : Store H} (hs : StoreOk s) {f : Frame} {Cf : Context}
    (hf : FrameOk s f Cf) {x : GlobalIdx} {nt : NumType}
    (ht : Cf.globals[x.toNat]? = some ⟨.var, .num nt⟩) {a : Nat} {gi : GlobalInst}
    (ha : f.module.globals[x.toNat]? = some a) (hgi : s.globals[a]? = some gi) :
    gi.type.type = .num nt := by
  obtain ⟨a', ha', hxa⟩ := hf.globalVar ht
  have haa : a' = a := Option.some.inj (ha'.symm.trans ha)
  subst haa
  obtain ⟨gi', hgi', -, -, -, hbw⟩ := hxa.global_invVar hs a' _ rfl rfl
  have hgg : gi' = gi := Option.some.inj (hgi'.symm.trans hgi)
  subst hgg
  have hv : ValOk s (.num ⟨nt, 0⟩) gi'.type.type := hbw rfl _ (.num ⟨nt, 0⟩)
  generalize gi'.type.type = T at hv
  cases hv
  rfl

/-- A stored global at a number type holds a number of that type. -/
theorem global_value_of_type {s : Store H} (hs : StoreOk s) {a : Nat} {gi : GlobalInst}
    (hgi : s.globals[a]? = some gi) {nt : NumType} (ht : gi.type.type = .num nt) :
    ∃ m, gi.value = .num m ∧ m.type = nt := by
  have hval : ValOk s gi.value gi.type.type := (hs.globals gi (List.mem_of_getElem? hgi)).2
  rw [ht] at hval
  generalize e : gi.value = w at hval
  generalize e' : (Ty.num nt : CValType) = T at hval
  cases hval with
  | num m => exact ⟨m, rfl, by injection e' with e''; exact e''.symm⟩
  | vec => cases e'
  | ref => cases e'

/-- **The operand of a typed `global.set x` redex has the value type of the global `x` names.** -/
theorem globalSet_core {s : Store H} (hs : StoreOk s) (hts : StoreTypesOk s) {f : Frame}
    {Cf C : Context} (hf : FrameOk s f Cf) (hg : C.globals = Cf.globals) (hC : C.Wf)
    {L₁ L₂ : List Admin} {n : NumVal} {x : GlobalIdx} {it : InstrType}
    (hty : AdminsOk s C (L₁ ++ [Val.toAdmin (.num n), .plain (.globalSet x)] ++ L₂) it)
    {a : Nat} {gi : GlobalInst} (ha : f.module.globals[x.toNat]? = some a)
    (hgi : s.globals[a]? = some gi) :
    ∃ m, gi.value = .num m ∧ m.type = n.type := by
  obtain ⟨C', it', h', hg', hC'⟩ := infix_typed hty (by simp) hC
  have ht : C'.globals[x.toNat]? = some ⟨.var, .num n.type⟩ := globalSet_ctx hs hts hC' h'
  have ht' : Cf.globals[x.toNat]? = some ⟨.var, .num n.type⟩ := by rw [← hg, ← hg']; exact ht
  exact global_value_of_type hs hgi (global_type_of_ctx hs hf ht' ha hgi)

/-! ## Through the simulation relation -/

open Silmaril.Wasm.Lime1.Execution.ToCore (Rigid map_norm_eq_of_rigid norm_eq_label norm_eq_frame)

/-- `GlobalInst.erase` keeps the value. -/
theorem erase_value (g : GlobalInst) : (Lime1.Execution.ToCore.GlobalInst.erase g).value = g.value := by
  unfold Lime1.Execution.ToCore.GlobalInst.erase
  split <;> rfl

/-- A Core global whose erasure is the image of a V1 global holds the image of its value. -/
theorem global_of_erase {s : V1.Execution.Store H} {sC : Store H}
    (hsS : Lime1.Execution.ToCore.Store.erase sC = (s.mapCode V1.Func.toLime).toCore)
    {a : Execution.Runtime.GlobalAddr} {g : Execution.Runtime.GlobalInst}
    (hg : s.globals[a.value]? = some g) :
    ∃ gi, sC.globals[a.value]? = some gi ∧ gi.value = g.value.toCore := by
  have e := congrArg (fun t => t.globals[a.value]?) hsS
  simp only [Lime1.Execution.ToCore.Store.erase, Execution.Runtime.Store.toCore,
    List.getElem?_map] at e
  have e' : (s.mapCode V1.Func.toLime).globals = s.globals := rfl
  rw [e', hg] at e
  cases hc : sC.globals[a.value]? with
  | none => rw [hc] at e; cases e
  | some gi =>
    rw [hc] at e
    simp only [Option.map_some, Option.some.injEq] at e
    refine ⟨gi, rfl, ?_⟩
    rw [← erase_value gi, e]
    rfl

/-- The statement of the `ActiveF` induction. -/
def GSetCoreP (s : V1.Execution.Store H) (sC : Store H) (f : Execution.Runtime.Frame)
    (code : List V1.Execution.Admin) (f' : Execution.Runtime.Frame)
    (w : List V1.Execution.Admin) : Prop :=
  ∀ (v : Execution.Runtime.Value) (x : GlobalIdx),
    w = [V1.Execution.value v, .source (.globalSet x)] →
    ∀ (fC : Frame) (L : List Admin) (Cf C : Context) (it : InstrType),
      Lime1.Execution.ToCore.Frame.erase fC = f.toCore →
      L.map (Lime1.Execution.ToCore.Admin.norm fC.module) =
        Lime1.Execution.Admin.listToCore (s.mapCode V1.Func.toLime) (V1.Execution.codeToLime code) →
      FrameOk sC fC Cf → C.globals = Cf.globals → C.Wf → AdminsOk sC C L it →
      ∀ (a : Execution.Runtime.GlobalAddr) (g : Execution.Runtime.GlobalInst),
        f'.module.globals[x.toNat]? = some a → s.globals[a.value]? = some g →
        v.type = g.value.type

/-- Split a normalised image around an infix. -/
theorem map_norm_split {m : ModuleInst} {L A M B : List Admin}
    (h : L.map (Lime1.Execution.ToCore.Admin.norm m) = A ++ M ++ B) :
    ∃ L₁ M' L₂, L = L₁ ++ M' ++ L₂ ∧ M'.map (Lime1.Execution.ToCore.Admin.norm m) = M := by
  obtain ⟨LA, LMB, rfl, -, hMB⟩ := List.map_eq_append_iff.mp (by simpa [List.append_assoc] using h)
  obtain ⟨LM, LB, rfl, hM, -⟩ := List.map_eq_append_iff.mp hMB
  exact ⟨LA, LM, LB, by simp [List.append_assoc], hM⟩

/-- An element of a V1 code sequence splits it. -/
theorem split_mem {α : Type} {a : α} {l : List α} (h : a ∈ l) : ∃ l₁ l₂, l = l₁ ++ [a] ++ l₂ := by
  obtain ⟨l₁, l₂, e⟩ := List.append_of_mem h
  exact ⟨l₁, l₂, by simp [e]⟩

/-- The image of a `global.set` redex. -/
theorem listToCore_gset (s : V1.Execution.Store H) (v : Execution.Runtime.Value) (x : GlobalIdx) :
    Lime1.Execution.Admin.listToCore (s.mapCode V1.Func.toLime)
      (V1.Execution.codeToLime [V1.Execution.value v, .source (.globalSet x)]) =
      [Val.toAdmin (.num ⟨v.type, v.bits⟩), .plain (.globalSet x)] := by
  simp
  exact ⟨rfl, rfl⟩

/-- A normalised image with a `global.set` redex in its middle has that redex in its middle. -/
theorem split_gset {m : ModuleInst} {L A B : List Admin} {n : NumVal} {x : GlobalIdx}
    (h : L.map (Lime1.Execution.ToCore.Admin.norm m) =
      A ++ [Val.toAdmin (.num n), .plain (.globalSet x)] ++ B) :
    ∃ L₁ L₂, L = L₁ ++ [Val.toAdmin (.num n), .plain (.globalSet x)] ++ L₂ := by
  obtain ⟨L₁, M, L₂, rfl, hM⟩ := map_norm_split h
  have hr : ∀ y ∈ [Val.toAdmin (.num n), .plain (.globalSet x)], Rigid y := by
    intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl
    · exact Lime1.Execution.ToCore.Rigid.val _
    · simp [Lime1.Execution.ToCore.Rigid]
  exact ⟨L₁, L₂, by rw [map_norm_eq_of_rigid hr hM]⟩

/-- The Core frame's global addresses are the V1 frame's. -/
theorem frame_global {fC : Frame} {f : Execution.Runtime.Frame}
    (hfe : Lime1.Execution.ToCore.Frame.erase fC = f.toCore) {x : GlobalIdx}
    {a : Execution.Runtime.GlobalAddr} (ha : f.module.globals[x.toNat]? = some a) :
    fC.module.globals[x.toNat]? = some a.value := by
  have e := congrArg (fun t => t.module.globals[x.toNat]?) hfe
  simp only [Lime1.Execution.ToCore.Frame.erase, Lime1.Execution.ToCore.ModuleInst.erase,
    Execution.Runtime.Frame.toCore, Execution.Runtime.ModuleInst.toCore, List.getElem?_map,
    ha, Option.map_some] at e
  exact e

/-- The piece case: the redex is a contiguous piece of the code of `f`. -/
theorem gsetCoreP_piece {s : V1.Execution.Store H} {sC : Store H} (hs : StoreOk sC)
    (hts : StoreTypesOk sC)
    (hsS : Lime1.Execution.ToCore.Store.erase sC = (s.mapCode V1.Func.toLime).toCore)
    {f : Execution.Runtime.Frame} {l₁ w l₂ : List V1.Execution.Admin} :
    GSetCoreP s sC f (l₁ ++ w ++ l₂) f w := by
  intro v x hw fC L Cf C it hfe hL hf hg hC hty a g ha hga
  subst hw
  simp only [V1.Execution.codeToLime_append, Lime1.Execution.listToCore_append,
    listToCore_gset] at hL
  obtain ⟨L₁, L₂, rfl⟩ := split_gset hL
  obtain ⟨gi, hgi, hgv⟩ := global_of_erase hsS hga
  obtain ⟨m, hm, hmt⟩ := globalSet_core hs hts hf hg hC hty (frame_global hfe ha) hgi
  have hmg : m = ⟨g.value.type, g.value.bits⟩ := by
    rw [hgv] at hm
    exact (Val.num.inj hm).symm
  rw [hmg] at hmt
  exact hmt.symm

/-- A typed sequence with a single element in its middle types that element as an `AdminOk`. -/
theorem single_typed {s : Store H} {C : Context} {L₁ L₂ : List Admin} {z : Admin} {it : InstrType}
    (h : AdminsOk s C (L₁ ++ [z] ++ L₂) it) (hC : C.Wf) :
    ∃ C' it', AdminOk s C' z it' ∧ C'.globals = C.globals ∧ C'.Wf := by
  obtain ⟨C', it', h', hg', hC'⟩ := infix_typed h (by simp) hC
  obtain ⟨_, it₀, ha, -⟩ := AdminsOk.single_aux' h' z rfl hC'.types
  exact ⟨C', it₀, ha, hg', hC'⟩

/-- The label case. -/
theorem gsetCoreP_label {s : V1.Execution.Store H} {sC : Store H}
    {f f' : Execution.Runtime.Frame} {code w body : List V1.Execution.Admin} {n : Nat}
    {cont : V1.Expr} (hm : .label n cont body ∈ code) (ih : GSetCoreP s sC f body f' w) :
    GSetCoreP s sC f code f' w := by
  intro v x hw fC L Cf C it hfe hL hf hg hC hty a g ha hga
  obtain ⟨l₁, l₂, rfl⟩ := split_mem hm
  simp only [V1.Execution.codeToLime_append, Lime1.Execution.listToCore_append] at hL
  obtain ⟨L₁, M, L₂, rfl, hM⟩ := map_norm_split hL
  simp only [V1.Execution.codeToLime_cons, V1.Execution.codeToLime_nil,
    Execution.Runtime.AdminInstr.map, Lime1.Execution.listToCore_cons,
    Lime1.Execution.listToCore_nil, List.append_nil] at hM
  obtain ⟨z, rfl, hz⟩ := List.map_eq_singleton_iff.mp hM
  obtain ⟨b', rfl, hb'⟩ := norm_eq_label hz
  obtain ⟨C', it', ha', hg', hC'⟩ := single_typed hty hC
  cases ha' with
  | label hn hc hb =>
    have hr := (AdminsOk.params_ok hC' hc).1
    exact ih v x hw fC b' Cf _ _ hfe hb' hf (by rw [← hg, ← hg']; rfl) (hC'.withLabel hr) hb a g
      ha hga

/-- The frame case. -/
theorem gsetCoreP_frame {s : V1.Execution.Store H} {sC : Store H} (hs : StoreOk sC)
    (hts : StoreTypesOk sC) {f fi f' : Execution.Runtime.Frame}
    {code w body : List V1.Execution.Admin} {n : Nat}
    (hm : .frame n fi body ∈ code) (ih : GSetCoreP s sC fi body f' w) :
    GSetCoreP s sC f code f' w := by
  intro v x hw fC L Cf C it hfe hL hf hg hC hty a g ha hga
  obtain ⟨l₁, l₂, rfl⟩ := split_mem hm
  simp only [V1.Execution.codeToLime_append, Lime1.Execution.listToCore_append] at hL
  obtain ⟨L₁, M, L₂, rfl, hM⟩ := map_norm_split hL
  simp only [V1.Execution.codeToLime_cons, V1.Execution.codeToLime_nil,
    Execution.Runtime.AdminInstr.map, Lime1.Execution.listToCore_cons,
    Lime1.Execution.listToCore_nil, List.append_nil] at hM
  obtain ⟨z, rfl, hz⟩ := List.map_eq_singleton_iff.mp hM
  obtain ⟨fz, b', rfl, hfz, hb'⟩ := norm_eq_frame hz
  obtain ⟨C', it', ha', -, -⟩ := single_typed hty hC
  cases ha' with
  | frame hf' hn hb hok =>
    rename_i C'' ts
    have hwf : ({ C'' with return_ := some ts } : Context).Wf :=
      (FrameOk.ctxWf hs hts hf').withReturn fun t h => TyOk.of_empty _ (hok t h)
    exact ih v x hw fz b' C'' { C'' with return_ := some ts } _ hfz hb' hf' rfl hwf hb a g ha hga

/-- **The `ActiveF` induction.** -/
theorem gsetCoreP_of_active {s : V1.Execution.Store H} {sC : Store H} (hs : StoreOk sC)
    (hts : StoreTypesOk sC)
    (hsS : Lime1.Execution.ToCore.Store.erase sC = (s.mapCode V1.Func.toLime).toCore)
    {f f' : Execution.Runtime.Frame} {code w : List V1.Execution.Admin}
    (h : Silmaril.Wasm.SpecTec.Sim10.ActiveF f code f' w) : GSetCoreP s sC f code f' w := by
  induction h with
  | piece => exact gsetCoreP_piece hs hts hsS
  | label hm _ ih => exact gsetCoreP_label hm ih
  | frame hm _ ih => exact gsetCoreP_frame hs hts hm ih

/-- **A V1 configuration related to a typed Core configuration satisfies `GSetOk`.** -/
theorem gsetOk_of_core {c : V1.Execution.Config H} {cc : Config H} {ts : List CValType}
    (hsim : Lime1.Execution.Sim c.toLime cc) (hok : ConfigOk cc ts) :
    Silmaril.Wasm.SpecTec.Sim10.GSetOk c.store c.frame c.code := by
  obtain ⟨C, ⟨hs, hf⟩, hty⟩ := hok
  have hts : StoreTypesOk cc.store := ⟨hs.structsClosed, hs.arraysClosed⟩
  have hn := hsim.1
  rcases cc with ⟨sC, fC, L⟩
  obtain ⟨hsS, hfe, hL⟩ := Lime1.Execution.ToCore.Config.norm_eq_toCore_iff.mp hn
  intro f' v x a g hact ha hg
  exact gsetCoreP_of_active hs hts hsS hact v x rfl fC L C C _ hfe hL hf rfl
    (FrameOk.ctxWf hs hts hf) hty a g ha hg

end Silmaril.Wasm.SpecTec.Sim10.Valid
