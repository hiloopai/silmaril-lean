module

public import Silmaril.Raw.Wasm.Versions.V2.ToCore.Runtime
public import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

/-! # Shared machinery for the `2.0 → 3.0` step simulation

The per-constructor simulation lemmas of `V2/ToCore/Sim/*.lean` all have the
same shape:

```
Sim ⟨s, f, before⟩ c  →  ∃ c', TransGen (Core.Step coreProfile tgt) c c' ∧ Sim ⟨s', f', after⟩ c'
```

and are all discharged by the same three moves, packaged here.

1. **Project `Sim`.** `sim_store`, `sim_frame`, `sim_code` read the three
   components out of `Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩`: the Core store erases to
   the image of the 2.0 store, the Core frame erases to the image of the 2.0
   frame, and the Core code *normalises* to the image of the 2.0 code.

2. **Catch up on `REF.NULL`.** The Core code is only related *up to*
   `ToCore.Admin.norm`, and `Admin.norm` is not injective: a Core
   `REF.NULL ht` normalises to the Core value `REF.NULL_ADDR`, which is what the
   2.0 value `REF.NULL rt` maps to (see the module docstring of
   `V2/ToCore/Runtime.lean`). So the Core configuration may be up to one
   `Step_read/ref.null` *behind* its 2.0 counterpart, once for every null
   reference on the operand stack. `catchUp` runs exactly those steps: if the
   image of the 2.0 code is `cvals vs ++ R` with every element of `R` rigid,
   then the Core code reduces — in zero or more `Step_read/ref.null` steps — to
   that image.

   This is why the milestone theorem uses `Relation.TransGen` for one 2.0 step
   and why `Lime1`'s `map_norm_vals` has no analogue here.

3. **Rebuild `Sim`.** `simMk` turns "the Core store erases correctly, the Core
   frame erases correctly, the 2.0 code has an image, and the 2.0 configuration
   is well formed" back into `Sim`; the normality side condition is discharged
   by `map_norm_listToCore` of `V2/ToCore/Runtime.lean`.

`finish`, `finish₁` and `finishSame` chain the three.
-/

namespace Silmaril.Wasm.V2.Execution.ToCoreSim

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.V2.Execution.ToCore

variable {H : Type} {P : Profile}

/-- Core 3.0's `val*` as administrative code, under a name that does not clash
with `Silmaril.Wasm.V2.Execution.vals`. -/
abbrev cvals (vs : List CVal) : List CAdmin := Silmaril.Wasm.Execution.Core.vals vs

/-- Core 3.0's reduction relation, under a short name. -/
abbrev CStep (P : Profile) (tgt : CHostSemantics H) : CConfig H → CConfig H → Prop :=
  Silmaril.Wasm.Execution.Core.Step P tgt

/-- One or more Core steps. -/
abbrev CPlus (P : Profile) (tgt : CHostSemantics H) : CConfig H → CConfig H → Prop :=
  Relation.TransGen (CStep P tgt)

/-- The conclusion shared by every simulation lemma. -/
abbrev Target (P : Profile) (tgt : CHostSemantics H) (b : Config H) (c : CConfig H) : Prop :=
  ∃ c', CPlus P tgt c c' ∧ Sim b c'

/-- Compute the Core image of a short, explicit 2.0 code sequence. -/
macro "v2img" : tactic =>
  `(tactic| simp [cvals, Silmaril.Wasm.Execution.Core.vals, Instr.toCore, ToCore.plainOrNull,
      Val.toCore, Ref.toCore, Silmaril.Wasm.Execution.Core.Val.toAdmin, store8, load8u] <;>
      rfl)

/-- Discharge a `Rigid` side condition on an explicit list. -/
macro "v2rigid" : tactic => `(tactic| simp [ToCore.Rigid])

/-! ## Projecting `Sim` -/

theorem sim_parts {s : Store H} {f : Frame} {code : List Admin} {cs : CStore H} {cf : CFrame}
    {cl : List CAdmin} (hs : Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩) :
    s.toCore = some (ToCore.Store.erase cs) ∧ f.toCore = ToCore.Frame.erase cf ∧
      Admin.listToCore s code = some (cl.map (ToCore.Admin.norm cf.module)) := by
  obtain ⟨hn, -⟩ := hs
  simp only [Config.toCore, ToCore.Config.norm, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at hn
  obtain ⟨S, hS, L, hL, hE⟩ := hn
  refine ⟨?_, ?_, ?_⟩
  · have h1 : S = ToCore.Store.erase cs :=
      congrArg Silmaril.Wasm.Execution.Core.Config.store hE
    rw [hS, h1]
  · exact congrArg Silmaril.Wasm.Execution.Core.Config.frame hE
  · have h3 : L = ToCore.Admin.normList cf.module cl :=
      congrArg Silmaril.Wasm.Execution.Core.Config.code hE
    rw [hL, h3, ToCore.Admin.normList_eq_map]

theorem sim_store {s : Store H} {f : Frame} {code : List Admin} {cs : CStore H} {cf : CFrame}
    {cl : List CAdmin} (hs : Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩) :
    s.toCore = some (ToCore.Store.erase cs) := (sim_parts hs).1

theorem sim_frame {s : Store H} {f : Frame} {code : List Admin} {cs : CStore H} {cf : CFrame}
    {cl : List CAdmin} (hs : Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩) :
    f.toCore = ToCore.Frame.erase cf := (sim_parts hs).2.1

theorem sim_code {s : Store H} {f : Frame} {code : List Admin} {cs : CStore H} {cf : CFrame}
    {cl : List CAdmin} (hs : Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩) :
    Admin.listToCore s code = some (cl.map (ToCore.Admin.norm cf.module)) := (sim_parts hs).2.2

theorem sim_wf {a : Config H} {c : CConfig H} (hs : Sim a c) : ConfigWF a := hs.2

/-! ## Rebuilding `Sim` -/

/-- The general form: the Core code need only *normalise* to the image of the
2.0 code. This is what `Step_pure/br-zero` and the other rules whose right-hand
side contains an `expr` need, because Core 3.0's `expression cs` is
`cs.map .plain` while the image of a 2.0 `expression es` is
`cs.map ToCore.plainOrNull` (see `expression_toCore`). -/
theorem simMkNorm {s : Store H} {f : Frame} {code : List Admin} {cs : CStore H} {cf : CFrame}
    {L : List CAdmin} (hst : s.toCore = some (ToCore.Store.erase cs))
    (hfr : f.toCore = ToCore.Frame.erase cf)
    (hcode : Admin.listToCore s code = some (L.map (ToCore.Admin.norm cf.module)))
    (hwf : ConfigWF (⟨s, f, code⟩ : Config H)) :
    Sim (⟨s, f, code⟩ : Config H) ⟨cs, cf, L⟩ := by
  refine ⟨?_, hwf⟩
  simp only [Config.toCore, ToCore.Config.norm, hst, hcode, Option.bind_some, Option.map_some,
    hfr, ToCore.Admin.normList_eq_map]

theorem simMk {s : Store H} {f : Frame} {code : List Admin} {cs : CStore H} {cf : CFrame}
    {L : List CAdmin} (hst : s.toCore = some (ToCore.Store.erase cs))
    (hfr : f.toCore = ToCore.Frame.erase cf) (hcode : Admin.listToCore s code = some L)
    (hwf : ConfigWF (⟨s, f, code⟩ : Config H)) :
    Sim (⟨s, f, code⟩ : Config H) ⟨cs, cf, L⟩ := by
  refine simMkNorm hst hfr ?_ hwf
  have hnorm := map_norm_listToCore s code cf.module
  rw [hcode] at hnorm
  simp only [Option.map_some, Option.some.injEq] at hnorm
  rw [hcode, hnorm]

/-! ## Catching up on `REF.NULL` -/

/-- A Core administrative instruction whose normal form is `y` reduces to `y`,
provided `y` is rigid or the null reference. -/
theorem catchUp_one {tgt : CHostSemantics H} {cs : CStore H} {cf : CFrame} {x y : CAdmin}
    {rest : List CAdmin} (hy : Rigid y ∨ y = .ref .null)
    (h : ToCore.Admin.norm cf.module x = y) :
    Silmaril.Wasm.Execution.Core.Steps P tgt ⟨cs, cf, x :: rest⟩ ⟨cs, cf, y :: rest⟩ := by
  rcases hy with hy | rfl
  · rw [hy.eq_of_norm h]
  · rcases ToCore.norm_eq_null h with rfl | ⟨ht, rfl⟩
    · exact .refl
    · have := Silmaril.Wasm.Execution.Core.Steps.ctxtInstrs
        (P := P) (host := tgt) (vs := ([] : List CVal)) (rest := rest)
        (Relation.ReflTransGen.single (Silmaril.Wasm.Execution.Core.Step.reference
          (Silmaril.Wasm.Execution.Core.RefStep.refNull (s := cs) (f := cf) ht)))
      simpa [Silmaril.Wasm.Execution.Core.vals] using this

/-- **The catch-up lemma.** If the Core code normalises to the image of the 2.0
code, and that image is a value prefix followed by rigid instructions, then the
Core code reduces to the image in zero or more `Step_read/ref.null` steps. -/
theorem catchUp {tgt : CHostSemantics H} {cs : CStore H} {cf : CFrame} {cl : List CAdmin}
    {vs : List CVal} {R : List CAdmin} (hR : ∀ y ∈ R, Rigid y)
    (h : cl.map (ToCore.Admin.norm cf.module) = cvals vs ++ R) :
    Silmaril.Wasm.Execution.Core.Steps P tgt ⟨cs, cf, cl⟩ ⟨cs, cf, cvals vs ++ R⟩ := by
  induction vs generalizing cl with
  | nil =>
    simp only [cvals, Silmaril.Wasm.Execution.Core.vals, List.map_nil, List.nil_append] at h ⊢
    rw [ToCore.map_norm_eq_of_rigid hR h]
  | cons v vs ih =>
    rcases cl with _ | ⟨x, cl'⟩
    · simp [cvals, Silmaril.Wasm.Execution.Core.vals] at h
    · simp only [cvals, Silmaril.Wasm.Execution.Core.vals, List.map_cons, List.cons_append,
        List.cons.injEq] at h ⊢
      obtain ⟨hx, hcl⟩ := h
      have hstep := ih (cl := cl') hcl
      have hfirst : Silmaril.Wasm.Execution.Core.Steps P tgt ⟨cs, cf, x :: cl'⟩
          ⟨cs, cf, v.toAdmin :: cl'⟩ := by
        refine catchUp_one ?_ hx
        by_cases hv : v = .ref .null
        · subst hv; exact Or.inr rfl
        · exact Or.inl (ToCore.Rigid.val hv)
      refine hfirst.trans ?_
      have := Silmaril.Wasm.Execution.Core.Steps.ctxtInstrs
        (P := P) (host := tgt) (vs := [v]) (rest := ([] : List CAdmin)) hstep
      simpa [Silmaril.Wasm.Execution.Core.vals] using this

/-- Catching up in a context: the trailing code is left alone. -/
theorem catchUpVals {tgt : CHostSemantics H} {cs : CStore H} {cf : CFrame} :
    (vs : List CVal) → (l tail : List CAdmin) → l.map (ToCore.Admin.norm cf.module) = cvals vs →
      Silmaril.Wasm.Execution.Core.Steps P tgt ⟨cs, cf, l ++ tail⟩ ⟨cs, cf, cvals vs ++ tail⟩
  | [], l, tail, h => by
    simp only [cvals, Silmaril.Wasm.Execution.Core.vals, List.map_nil] at h
    rw [List.map_eq_nil_iff.mp h]
    simp only [cvals, Silmaril.Wasm.Execution.Core.vals, List.map_nil, List.nil_append]
    exact .refl
  | v :: vs, l, tail, h => by
    rcases l with _ | ⟨x, l'⟩
    · simp [cvals, Silmaril.Wasm.Execution.Core.vals] at h
    · simp only [cvals, Silmaril.Wasm.Execution.Core.vals, List.map_cons,
        List.cons.injEq] at h
      obtain ⟨hx, hl⟩ := h
      have hfirst : Silmaril.Wasm.Execution.Core.Steps P tgt ⟨cs, cf, x :: (l' ++ tail)⟩
          ⟨cs, cf, v.toAdmin :: (l' ++ tail)⟩ := by
        refine catchUp_one ?_ hx
        by_cases hv : v = .ref .null
        · subst hv; exact Or.inr rfl
        · exact Or.inl (ToCore.Rigid.val hv)
      have hrest := catchUpVals (tgt := tgt) (cs := cs) (cf := cf) vs l' tail (by
        simpa [cvals, Silmaril.Wasm.Execution.Core.vals] using hl)
      have := Silmaril.Wasm.Execution.Core.Steps.ctxtInstrs
        (P := P) (host := tgt) (vs := [v]) (rest := ([] : List CAdmin)) hrest
      simp only [Silmaril.Wasm.Execution.Core.vals, List.map_cons, List.map_nil,
        List.singleton_append, List.append_nil] at this
      simpa only [List.cons_append, Silmaril.Wasm.Execution.Core.vals, List.map_cons] using
        hfirst.trans this

/-- **The catch-up lemma, general form.** If the Core code normalises to a value
prefix, a rigid middle and an arbitrary tail, then the Core code reduces — in
`Step_read/ref.null` steps only — to a configuration with that value prefix and
middle, and a tail that still normalises to the image. -/
theorem catchUpSplit {tgt : CHostSemantics H} {cs : CStore H} {cf : CFrame} {cl : List CAdmin}
    {vs : List CVal} {R T : List CAdmin} (hR : ∀ y ∈ R, Rigid y)
    (h : cl.map (ToCore.Admin.norm cf.module) = cvals vs ++ R ++ T) :
    ∃ t : List CAdmin, t.map (ToCore.Admin.norm cf.module) = T ∧
      Silmaril.Wasm.Execution.Core.Steps P tgt ⟨cs, cf, cl⟩ ⟨cs, cf, cvals vs ++ R ++ t⟩ := by
  rw [List.append_assoc] at h
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.mp h
  obtain ⟨m₁, m₂, rfl, hm₁, hm₂⟩ := List.map_eq_append_iff.mp h₂
  refine ⟨m₂, hm₂, ?_⟩
  rw [ToCore.map_norm_eq_of_rigid hR hm₁]
  simpa only [List.append_assoc] using
    catchUpVals (P := P) (tgt := tgt) (cs := cs) (cf := cf) vs l₁ (R ++ m₂) h₁

/-- A store extension keeps every module instance well formed. -/
theorem StoreExt.modWF {s s' : Store H} (hext : StoreExt s s') {m : ModuleInst}
    (h : ModWF s m) : ModWF s' m := fun a ha => ListExt.lt hext (h a ha)

/-! ## The store/frame bridge

The seven accessors `$table`, `$mem`, `$elem`, `$data`, `$global`, `$local` and
`$func` (`5-runtime-aux:83-90`) transfer across the embedding: a 2.0 lookup gives
the corresponding Core 3.0 lookup, at the same address, of the image of the
instance. These are what every `Sim/Read.lean` and `Sim/State.lean` lemma needs
before it can build its Core step. -/

theorem erase_tables {s : Store H} {cs : CStore H}
    (h : s.toCore = some (ToCore.Store.erase cs)) :
    cs.tables = s.tables.map TableInst.toCore := by
  simp only [Store.toCore, Option.map_eq_some_iff] at h
  obtain ⟨fs, hfs, hE⟩ := h
  exact (congrArg Silmaril.Wasm.Execution.Core.Store.tables hE).symm

theorem erase_mems {s : Store H} {cs : CStore H}
    (h : s.toCore = some (ToCore.Store.erase cs)) :
    cs.mems = s.mems.map MemInst.toCore := by
  simp only [Store.toCore, Option.map_eq_some_iff] at h
  obtain ⟨fs, hfs, hE⟩ := h
  exact (congrArg Silmaril.Wasm.Execution.Core.Store.mems hE).symm

theorem erase_globals {s : Store H} {cs : CStore H}
    (h : s.toCore = some (ToCore.Store.erase cs)) :
    cs.globals = s.globals.map GlobalInst.toCore := by
  simp only [Store.toCore, Option.map_eq_some_iff] at h
  obtain ⟨fs, hfs, hE⟩ := h
  exact (congrArg Silmaril.Wasm.Execution.Core.Store.globals hE).symm

theorem erase_elems {s : Store H} {cs : CStore H}
    (h : s.toCore = some (ToCore.Store.erase cs)) :
    cs.elems = s.elems.map ElemInst.toCore := by
  simp only [Store.toCore, Option.map_eq_some_iff] at h
  obtain ⟨fs, hfs, hE⟩ := h
  exact (congrArg Silmaril.Wasm.Execution.Core.Store.elems hE).symm

theorem erase_datas {s : Store H} {cs : CStore H}
    (h : s.toCore = some (ToCore.Store.erase cs)) :
    cs.datas = s.datas.map DataInst.toCore := by
  simp only [Store.toCore, Option.map_eq_some_iff] at h
  obtain ⟨fs, hfs, hE⟩ := h
  exact (congrArg Silmaril.Wasm.Execution.Core.Store.datas hE).symm

theorem erase_locals {f : Frame} {cf : CFrame} (h : f.toCore = ToCore.Frame.erase cf) :
    cf.locals = f.locals.map (some ∘ Val.toCore) :=
  (congrArg Silmaril.Wasm.Execution.Core.Frame.locals h).symm

theorem erase_module_tables {f : Frame} {cf : CFrame} (h : f.toCore = ToCore.Frame.erase cf) :
    cf.module.tables = f.module.tables :=
  (congrArg (fun fr : CFrame => fr.module.tables) h).symm

theorem erase_module_mems {f : Frame} {cf : CFrame} (h : f.toCore = ToCore.Frame.erase cf) :
    cf.module.mems = f.module.mems :=
  (congrArg (fun fr : CFrame => fr.module.mems) h).symm

theorem erase_module_globals {f : Frame} {cf : CFrame} (h : f.toCore = ToCore.Frame.erase cf) :
    cf.module.globals = f.module.globals :=
  (congrArg (fun fr : CFrame => fr.module.globals) h).symm

theorem erase_module_elems {f : Frame} {cf : CFrame} (h : f.toCore = ToCore.Frame.erase cf) :
    cf.module.elems = f.module.elems :=
  (congrArg (fun fr : CFrame => fr.module.elems) h).symm

theorem erase_module_datas {f : Frame} {cf : CFrame} (h : f.toCore = ToCore.Frame.erase cf) :
    cf.module.datas = f.module.datas :=
  (congrArg (fun fr : CFrame => fr.module.datas) h).symm

theorem erase_module_funcs {f : Frame} {cf : CFrame} (h : f.toCore = ToCore.Frame.erase cf) :
    cf.module.funcs = f.module.funcs :=
  (congrArg (fun fr : CFrame => fr.module.funcs) h).symm

/-- `$table(z, x)` transfers. -/
theorem bridge_table {s : Store H} {f : Frame} {cs : CStore H} {cf : CFrame} {x : TableIdx}
    {ti : TableInst} (hst : s.toCore = some (ToCore.Store.erase cs))
    (hfr : f.toCore = ToCore.Frame.erase cf) (h : (⟨s, f⟩ : State H).table? x = some ti) :
    ∃ a, cs.table? cf x = some (a, ti.toCore) := by
  simp only [State.table?, ModuleInst.tableAddr?, Store.tableInst?] at h
  cases ha : f.module.tables[x.toNat]? with
  | none => rw [ha] at h; simp at h
  | some a =>
    rw [ha] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      exists_eq_left'] at h
    refine ⟨a, ?_⟩
    simp [Silmaril.Wasm.Execution.Core.Store.table?, erase_module_tables hfr, ha,
      erase_tables hst, h]

/-- `$mem(z, x)` transfers. -/
theorem bridge_mem {s : Store H} {f : Frame} {cs : CStore H} {cf : CFrame} {x : MemIdx}
    {mi : MemInst} (hst : s.toCore = some (ToCore.Store.erase cs))
    (hfr : f.toCore = ToCore.Frame.erase cf) (h : (⟨s, f⟩ : State H).mem? x = some mi) :
    ∃ a, cs.mem? cf x = some (a, mi.toCore) := by
  simp only [State.mem?, ModuleInst.memAddr?, Store.memInst?] at h
  cases ha : f.module.mems[x.toNat]? with
  | none => rw [ha] at h; simp at h
  | some a =>
    rw [ha] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      exists_eq_left'] at h
    refine ⟨a, ?_⟩
    simp [Silmaril.Wasm.Execution.Core.Store.mem?, erase_module_mems hfr, ha,
      erase_mems hst, h]

/-- `$global(z, x)` transfers. -/
theorem bridge_global {s : Store H} {f : Frame} {cs : CStore H} {cf : CFrame} {x : GlobalIdx}
    {gi : GlobalInst} (hst : s.toCore = some (ToCore.Store.erase cs))
    (hfr : f.toCore = ToCore.Frame.erase cf) (h : (⟨s, f⟩ : State H).global? x = some gi) :
    ∃ a, cs.global? cf x = some (a, gi.toCore) := by
  simp only [State.global?, ModuleInst.globalAddr?, Store.globalInst?] at h
  cases ha : f.module.globals[x.toNat]? with
  | none => rw [ha] at h; simp at h
  | some a =>
    rw [ha] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      exists_eq_left'] at h
    refine ⟨a, ?_⟩
    simp [Silmaril.Wasm.Execution.Core.Store.global?, erase_module_globals hfr, ha,
      erase_globals hst, h]

/-- `$elem(z, x)` transfers. -/
theorem bridge_elem {s : Store H} {f : Frame} {cs : CStore H} {cf : CFrame} {x : ElemIdx}
    {ei : ElemInst} (hst : s.toCore = some (ToCore.Store.erase cs))
    (hfr : f.toCore = ToCore.Frame.erase cf) (h : (⟨s, f⟩ : State H).elem? x = some ei) :
    ∃ a, cs.elem? cf x = some (a, ei.toCore) := by
  simp only [State.elem?, ModuleInst.elemAddr?, Store.elemInst?] at h
  cases ha : f.module.elems[x.toNat]? with
  | none => rw [ha] at h; simp at h
  | some a =>
    rw [ha] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      exists_eq_left'] at h
    refine ⟨a, ?_⟩
    simp [Silmaril.Wasm.Execution.Core.Store.elem?, erase_module_elems hfr, ha,
      erase_elems hst, h]

/-- `$data(z, x)` transfers. -/
theorem bridge_data {s : Store H} {f : Frame} {cs : CStore H} {cf : CFrame} {x : DataIdx}
    {di : DataInst} (hst : s.toCore = some (ToCore.Store.erase cs))
    (hfr : f.toCore = ToCore.Frame.erase cf) (h : (⟨s, f⟩ : State H).data? x = some di) :
    ∃ a, cs.data? cf x = some (a, di.toCore) := by
  simp only [State.data?, ModuleInst.dataAddr?, Store.dataInst?] at h
  cases ha : f.module.datas[x.toNat]? with
  | none => rw [ha] at h; simp at h
  | some a =>
    rw [ha] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      exists_eq_left'] at h
    refine ⟨a, ?_⟩
    simp [Silmaril.Wasm.Execution.Core.Store.data?, erase_module_datas hfr, ha,
      erase_datas hst, h]

/-- `$local(z, x)` transfers; every 2.0 local is set. -/
theorem bridge_local {s : Store H} {f : Frame} {cf : CFrame} {x : LocalIdx} {v : Val}
    (hfr : f.toCore = ToCore.Frame.erase cf) (h : (⟨s, f⟩ : State H).local? x = some v) :
    cf.local? x = some (some v.toCore) := by
  simp only [State.local?, Frame.local?] at h
  simp [Silmaril.Wasm.Execution.Core.Frame.local?, erase_locals hfr, h]

/-! ## Chaining -/

/-- The common skeleton: catch up, then take the Core steps, then rebuild. -/
theorem finish {tgt : CHostSemantics H} {s s' : Store H} {f f' : Frame}
    {before after : List Admin} {cs : CStore H} {cf : CFrame} {cl : List CAdmin}
    {cs' : CStore H} {cf' : CFrame} {L' : List CAdmin} {vs : List CVal} {R : List CAdmin}
    (hs : Sim ⟨s, f, before⟩ ⟨cs, cf, cl⟩)
    (hbefore : Admin.listToCore s before = some (cvals vs ++ R)) (hR : ∀ y ∈ R, Rigid y)
    (hafter : Admin.listToCore s' after = some L')
    (hstep : CPlus P tgt ⟨cs, cf, cvals vs ++ R⟩ ⟨cs', cf', L'⟩)
    (hst : s'.toCore = some (ToCore.Store.erase cs')) (hfr : f'.toCore = ToCore.Frame.erase cf')
    (hwf : ConfigWF (⟨s', f', after⟩ : Config H)) :
    Target P tgt ⟨s', f', after⟩ ⟨cs, cf, cl⟩ := by
  refine ⟨⟨cs', cf', L'⟩, ?_, simMk hst hfr hafter hwf⟩
  have hcode := sim_code hs
  rw [hbefore] at hcode
  exact Relation.TransGen.trans_right (catchUp hR (by simpa using hcode.symm)) hstep

/-- `finish` with a single Core step that changes neither store nor frame. -/
theorem finishSame {tgt : CHostSemantics H} {s : Store H} {f : Frame}
    {before after : List Admin} {cs : CStore H} {cf : CFrame} {cl : List CAdmin}
    {L' : List CAdmin} {vs : List CVal} {R : List CAdmin}
    (hs : Sim ⟨s, f, before⟩ ⟨cs, cf, cl⟩)
    (hbefore : Admin.listToCore s before = some (cvals vs ++ R)) (hR : ∀ y ∈ R, Rigid y)
    (hafter : Admin.listToCore s after = some L') (hwf : Admin.listWF s after)
    (hstep : CStep P tgt ⟨cs, cf, cvals vs ++ R⟩ ⟨cs, cf, L'⟩) :
    Target P tgt ⟨s, f, after⟩ ⟨cs, cf, cl⟩ :=
  finish hs hbefore hR hafter (Relation.TransGen.single hstep) (sim_store hs) (sim_frame hs)
    ⟨(sim_wf hs).1, (sim_wf hs).2.1, hwf⟩

/-! ## Well-formedness of 2.0 code, by cases -/

@[simp] theorem listWF_nil' (s : Store H) : Admin.listWF s [] := by simp [Admin.listWF]

@[simp] theorem listWF_cons' (s : Store H) (a : Admin) (l : List Admin) :
    Admin.listWF s (a :: l) ↔ Admin.WF s a ∧ Admin.listWF s l := by simp [Admin.listWF]

@[simp] theorem WF_plain (s : Store H) (i : Instr) : Admin.WF s (.plain i) := by simp [Admin.WF]

@[simp] theorem WF_trap (s : Store H) : Admin.WF s .trap := by simp [Admin.WF]

@[simp] theorem WF_refFuncAddr (s : Store H) (a : FuncAddr) : Admin.WF s (.refFuncAddr a) := by
  simp [Admin.WF]

@[simp] theorem WF_refHostAddr (s : Store H) (a : HostAddr) : Admin.WF s (.refHostAddr a) := by
  simp [Admin.WF]

@[simp] theorem WF_callAddr (s : Store H) (a : FuncAddr) :
    Admin.WF s (.callAddr a) ↔ a < s.funcs.length := by simp [Admin.WF]

@[simp] theorem WF_label (s : Store H) (n : Nat) (cont : Expr) (body : List Admin) :
    Admin.WF s (.label n cont body) ↔ Admin.listWF s body := by simp [Admin.WF]

@[simp] theorem WF_frame (s : Store H) (n : Nat) (fr : Frame) (body : List Admin) :
    Admin.WF s (.frame n fr body) ↔ ModWF s fr.module ∧ Admin.listWF s body := by simp [Admin.WF]

@[simp] theorem listWF_append (s : Store H) (l l' : List Admin) :
    Admin.listWF s (l ++ l') ↔ Admin.listWF s l ∧ Admin.listWF s l' := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, and_assoc]

@[simp] theorem WF_value (s : Store H) (v : Val) : Admin.WF s v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;> simp [Val.toAdmin]

@[simp] theorem listWF_vals (s : Store H) (vs : List Val) : Admin.listWF s (vals vs) := by
  induction vs with
  | nil => simp [vals]
  | cons v vs ih => simpa [vals] using ih

@[simp] theorem listWF_expression (s : Store H) (e : Expr) : Admin.listWF s (expression e) := by
  induction e with
  | nil => simp [expression]
  | cons i e ih => simpa [expression] using ih

/-! ## Computing the Core image of a 2.0 code sequence -/

theorem listToCore_vals_append (s : Store H) (vs : List Val) {rest : List Admin}
    {L : List CAdmin} (h : Admin.listToCore s rest = some L) :
    Admin.listToCore s (vals vs ++ rest) = some (cvals (vs.map Val.toCore) ++ L) :=
  Admin.listToCore_append s (values_toCore s vs) h

/-- `Rigid` for a list of plain, non-`REF.NULL`, non-`CALL_REF` instructions and
traps. -/
theorem rigid_singleton {y : CAdmin} (h : Rigid y) : ∀ z ∈ [y], Rigid z := by
  simpa using h

/-! ## Normal forms of the two shapes that occur on the right of a Core rule -/

/-- Core values are their own normal form. -/
@[simp] theorem map_norm_cvals (m : CModuleInst) (vs : List CVal) :
    (cvals vs).map (ToCore.Admin.norm m) = cvals vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [cvals, Silmaril.Wasm.Execution.Core.vals, List.map_cons, List.map_map] at ih ⊢
    refine congrArg₂ List.cons ?_ ih
    cases v with
    | num x => cases x with | mk t b => cases t <;> rfl
    | vec => rfl
    | ref => rfl

/-- **Note.** The image of a 2.0 `expr` is `cs.map ToCore.plainOrNull`, not Core
3.0's `expression cs = cs.map .plain`; the two differ exactly on `REF.NULL`, and
`Admin.norm` identifies them. -/
theorem map_norm_expression {m : CModuleInst} {es : Expr} {cs : Wasm.Expr}
    (h : Expr.toCore es = some cs) :
    (Silmaril.Wasm.Execution.Core.expression cs).map (ToCore.Admin.norm m) =
      cs.map ToCore.plainOrNull := by
  simp only [Silmaril.Wasm.Execution.Core.expression, List.map_map]
  refine List.map_congr_left ?_
  intro c hc
  simpa using ToCore.normPlain_eq_plainOrNull m (Expr.toCore_ne_callRef h c hc)

/-- The image of a 2.0 configuration always exists under `Sim`. -/
theorem sim_exists {s : Store H} {f : Frame} {code : List Admin} {cs : CStore H} {cf : CFrame}
    {cl : List CAdmin} (hs : Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩) :
    ∃ L, Admin.listToCore s code = some L := ⟨_, sim_code hs⟩

/-! ## Inverting the two structural shapes -/

/-- The Core image of a `LABEL_n{cont} body`. -/
theorem listToCore_label (s : Store H) (n : Nat) (cont : Expr) (body : List Admin)
    {L : List CAdmin} (h : Admin.listToCore s [.label n cont body] = some L) :
    ∃ (k : Wasm.Expr) (B : List CAdmin), Expr.toCore cont = some k ∧
      Admin.listToCore s body = some B ∧ L = [.label n k B] := by
  simp only [Admin.listToCore_cons, Admin.listToCore_nil, Admin.label_toCore] at h
  cases hk : Expr.toCore cont with
  | none => rw [hk] at h; simp at h
  | some k =>
    cases hB : Admin.listToCore s body with
    | none => rw [hk, hB] at h; simp at h
    | some B =>
      rw [hk, hB] at h
      simp only [Option.map_some, Option.bind_some, List.append_nil, Option.some.injEq] at h
      exact ⟨k, B, rfl, rfl, h.symm⟩

/-- The Core image of a `FRAME_n{fr} body`. -/
theorem listToCore_frame (s : Store H) (n : Nat) (fr : Frame) (body : List Admin)
    {L : List CAdmin} (h : Admin.listToCore s [.frame n fr body] = some L) :
    ∃ B : List CAdmin, Admin.listToCore s body = some B ∧ L = [.frame n fr.toCore B] := by
  simp only [Admin.listToCore_cons, Admin.listToCore_nil, Admin.frame_toCore] at h
  cases hB : Admin.listToCore s body with
  | none => rw [hB] at h; simp at h
  | some B =>
    rw [hB] at h
    simp only [Option.map_some, Option.bind_some, List.append_nil, Option.some.injEq] at h
    exact ⟨B, rfl, h.symm⟩

/-- A `LABEL_n{cont} body` on the 2.0 side forces a `LABEL_n{k} b` on the Core
side, with `k` the image of `cont` and `b` normalising to the image of `body`. -/
theorem sim_label {s : Store H} {f : Frame} {n : Nat} {cont : Expr} {body : List Admin}
    {cs : CStore H} {cf : CFrame} {cl : List CAdmin}
    (hs : Sim ⟨s, f, [.label n cont body]⟩ ⟨cs, cf, cl⟩) :
    ∃ (k : Wasm.Expr) (b B : List CAdmin), cl = [.label n k b] ∧ Expr.toCore cont = some k ∧
      Admin.listToCore s body = some B ∧ b.map (ToCore.Admin.norm cf.module) = B := by
  have hcode := sim_code hs
  obtain ⟨k, B, hk, hB, hEq⟩ := listToCore_label s n cont body hcode
  rcases cl with _ | ⟨x, cl'⟩
  · simp at hEq
  · simp only [List.map_cons, List.cons.injEq] at hEq
    obtain ⟨b, rfl, hb⟩ := ToCore.norm_eq_label hEq.1
    rw [List.map_eq_nil_iff.mp hEq.2]
    exact ⟨k, b, B, rfl, hk, hB, hb⟩

/-- A `FRAME_n{fr} body` on the 2.0 side forces a `FRAME_n{fc} b` on the Core
side, with `fc` erasing to the image of `fr`. -/
theorem sim_frame_adm {s : Store H} {f : Frame} {n : Nat} {fr : Frame} {body : List Admin}
    {cs : CStore H} {cf : CFrame} {cl : List CAdmin}
    (hs : Sim ⟨s, f, [.frame n fr body]⟩ ⟨cs, cf, cl⟩) :
    ∃ (fc : CFrame) (b B : List CAdmin), cl = [.frame n fc b] ∧
      ToCore.Frame.erase fc = fr.toCore ∧ Admin.listToCore s body = some B ∧
      b.map (ToCore.Admin.norm fc.module) = B := by
  have hcode := sim_code hs
  obtain ⟨B, hB, hEq⟩ := listToCore_frame s n fr body hcode
  rcases cl with _ | ⟨x, cl'⟩
  · simp at hEq
  · simp only [List.map_cons, List.cons.injEq] at hEq
    obtain ⟨fc, b, rfl, hfc, hb⟩ := ToCore.norm_eq_frame hEq.1
    rw [List.map_eq_nil_iff.mp hEq.2]
    exact ⟨fc, b, B, rfl, hfc, hB, hb⟩

/-! ## Chaining, normalised form -/

/-- `finish`, allowing the Core code reached to be one `REF.NULL` step *ahead*
of the 2.0 code (which is what Core's `expression` does). -/
theorem finishNorm {tgt : CHostSemantics H} {s s' : Store H} {f f' : Frame}
    {before after : List Admin} {cs : CStore H} {cf : CFrame} {cl : List CAdmin}
    {cs' : CStore H} {cf' : CFrame} {L' : List CAdmin} {vs : List CVal} {R : List CAdmin}
    (hs : Sim ⟨s, f, before⟩ ⟨cs, cf, cl⟩)
    (hbefore : Admin.listToCore s before = some (cvals vs ++ R)) (hR : ∀ y ∈ R, Rigid y)
    (hafter : Admin.listToCore s' after = some (L'.map (ToCore.Admin.norm cf'.module)))
    (hstep : CPlus P tgt ⟨cs, cf, cvals vs ++ R⟩ ⟨cs', cf', L'⟩)
    (hst : s'.toCore = some (ToCore.Store.erase cs')) (hfr : f'.toCore = ToCore.Frame.erase cf')
    (hwf : ConfigWF (⟨s', f', after⟩ : Config H)) :
    Target P tgt ⟨s', f', after⟩ ⟨cs, cf, cl⟩ := by
  refine ⟨⟨cs', cf', L'⟩, ?_, simMkNorm hst hfr hafter hwf⟩
  have hcode := sim_code hs
  rw [hbefore] at hcode
  exact Relation.TransGen.trans_right (catchUp hR (by simpa using hcode.symm)) hstep

/-- `finishNorm` when the Core code is already known exactly (no catch-up). -/
theorem finishFrom {tgt : CHostSemantics H} {s' : Store H} {f' : Frame}
    {after : List Admin} {cs : CStore H} {cf : CFrame} {cl : List CAdmin}
    {cs' : CStore H} {cf' : CFrame} {L' : List CAdmin}
    (hstep : CPlus P tgt ⟨cs, cf, cl⟩ ⟨cs', cf', L'⟩)
    (hafter : Admin.listToCore s' after = some (L'.map (ToCore.Admin.norm cf'.module)))
    (hst : s'.toCore = some (ToCore.Store.erase cs')) (hfr : f'.toCore = ToCore.Frame.erase cf')
    (hwf : ConfigWF (⟨s', f', after⟩ : Config H)) :
    Target P tgt ⟨s', f', after⟩ ⟨cs, cf, cl⟩ :=
  ⟨⟨cs', cf', L'⟩, hstep, simMkNorm hst hfr hafter hwf⟩

/-- `finishNorm` with a single Core step that changes neither store nor frame. -/
theorem finishNormSame {tgt : CHostSemantics H} {s : Store H} {f : Frame}
    {before after : List Admin} {cs : CStore H} {cf : CFrame} {cl : List CAdmin}
    {L' : List CAdmin} {vs : List CVal} {R : List CAdmin}
    (hs : Sim ⟨s, f, before⟩ ⟨cs, cf, cl⟩)
    (hbefore : Admin.listToCore s before = some (cvals vs ++ R)) (hR : ∀ y ∈ R, Rigid y)
    (hafter : Admin.listToCore s after = some (L'.map (ToCore.Admin.norm cf.module)))
    (hwf : Admin.listWF s after)
    (hstep : CStep P tgt ⟨cs, cf, cvals vs ++ R⟩ ⟨cs, cf, L'⟩) :
    Target P tgt ⟨s, f, after⟩ ⟨cs, cf, cl⟩ :=
  finishNorm hs hbefore hR hafter (Relation.TransGen.single hstep) (sim_store hs) (sim_frame hs)
    ⟨(sim_wf hs).1, (sim_wf hs).2.1, hwf⟩

end Silmaril.Wasm.V2.Execution.ToCoreSim
