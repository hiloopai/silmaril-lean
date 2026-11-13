module

public import Silmaril.Proofs.Wasm.Game.ULink.Funcs
public import Silmaril.Proofs.Wasm.Game.Linking.Callout
public import Silmaril.Proofs.Wasm.Game.Linking.Split.Top

/-!
# The stubbed and the real store

* `stubS_get`, `sameTypes_stub`, `unstub_stub`: stubbing keeps types, and the resolver's
  `unstubS` inverts it on stores with the link's layout.
* `consumer_step`: **a host-free step of the consumer in the stubbed store is a step of the
  linked module in the real store** (from `step_withFuncs`: the consumer cannot call a provider
  function without a host call).
* `linked_step`: a host-free linked step is a consumer step, or a call into the provider.
* `decompose_real_of_stub`, `decompose_stub_of_real`, `stub_callout`: callouts of the
  consumer are forwarded host calls (the same in both stores) or stub calls (provider calls
  in the real store).
* `Ctx.comp`: callout contexts of the provider inside the consumer's context.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.ULink

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.ULink Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Binaryen.InlS Silmaril.Proofs.Wasm.Game.Linking

variable {L : ULink}

/-! ### Stubbing -/

theorem stubS_get (s : Store Nat) (a : Nat) :
    (L.stubS s).funcs[a]? = (s.funcs[a]?).map (L.stubFI a) := by
  simp [ULink.stubS, List.getElem?_mapIdx]

theorem stubFI_type (a : Nat) (fi : FuncInst Nat) : (L.stubFI a fi).type = fi.type := by
  unfold ULink.stubFI
  split <;> rfl

theorem stubFI_none {a : Nat} (h : L.stub a = none) (fi : FuncInst Nat) : L.stubFI a fi = fi := by
  simp [ULink.stubFI, h]

theorem stubFI_some {a k : Nat} {c : Func} (h : L.stub a = some (k, c)) (fi : FuncInst Nat) :
    L.stubFI a fi = { fi with code := .host k } := by
  simp [ULink.stubFI, h]

theorem unstubFI_stubFI {a : Nat} {fi : FuncInst Nat}
    (h : ∀ k c, L.stub a = some (k, c) → fi.code = .wasm c) : L.unstubFI a (L.stubFI a fi) = fi := by
  cases hs : L.stub a with
  | none => simp [ULink.unstubFI, ULink.stubFI, hs]
  | some kc =>
    obtain ⟨k, c⟩ := kc
    have hc : fi.code = .wasm c := h k c hs
    simp only [ULink.unstubFI, ULink.stubFI, hs]
    rw [← hc]

theorem sameTypes_mapIdx (fs : List (FuncInst Nat)) :
    SameTypes fs (fs.mapIdx L.stubFI) := by
  unfold SameTypes
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map, List.getElem?_mapIdx, Option.map_map]
  cases fs[i]? with
  | none => rfl
  | some fi => simp [stubFI_type]

/-- Stubbing keeps the function types. -/
theorem sameTypes_stub (s : Store Nat) : SameTypes s.funcs (L.stubS s).funcs :=
  sameTypes_mapIdx s.funcs

theorem withFuncs_stub (s : Store Nat) : withFuncs (L.stubS s) s.funcs = s := rfl

theorem stubS_withFuncs (σ : Store Nat) (X : List (FuncInst Nat)) :
    L.stubS (withFuncs σ X) = withFuncs σ (X.mapIdx L.stubFI) := rfl

/-- **`unstubS` inverts stubbing on stores with the layout.** -/
theorem unstub_stub {s : Store Nat} (h : L.Layout s) : L.unstubS (L.stubS s) = s := by
  have hf : ((s.funcs.mapIdx L.stubFI).mapIdx L.unstubFI) = s.funcs := by
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_mapIdx]
    cases hi : s.funcs[i]? with
    | none => rfl
    | some fi => exact congrArg some (unstubFI_stubFI fun k c hs => h.prov i fi k c hi hs)
  show { s with funcs := (s.funcs.mapIdx L.stubFI).mapIdx L.unstubFI } = s
  rw [hf]

/-- Layouts only depend on the functions. -/
theorem Layout.of_funcs {s s' : Store Nat} (h : L.Layout s) (hf : s'.funcs = s.funcs) :
    L.Layout s' :=
  ⟨fun a fi k c ha hs => h.prov a fi k c (hf ▸ ha) hs, fun a fi k ha hc => h.noStub a fi k (hf ▸ ha) hc⟩

/-- Threads denote the same code in the stubbed store. -/
theorem config_stub (s : Store Nat) (t : Thread) :
    t.config (L.stubS s) = ⟨L.stubS s, (t.config s).frame, (t.config s).code⟩ := by
  cases t with
  | active f code => rfl
  | pending a args =>
    simp only [Thread.config, Execution.Core.invoke, stubS_get, Option.map_map]
    congr 4
    cases s.funcs[a]? with
    | none => rfl
    | some fi => simp [stubFI_type]

/-! ### Steps -/

/-- **A host-free consumer step in the stubbed store is a linked step in the real store.** -/
theorem consumer_step {P : Profile} {s σ' : Store Nat} {f f' : Frame} {code code' : List Admin}
    (h : Execution.Core.Step P (fun _ _ _ _ => False) ⟨L.stubS s, f, code⟩ ⟨σ', f', code'⟩) :
    ∃ s', σ' = L.stubS s' ∧ s'.funcs = s.funcs ∧
      Execution.Core.Step P (fun _ _ _ _ => False) ⟨s, f, code⟩ ⟨s', f', code'⟩ := by
  have hfun : σ'.funcs = (L.stubS s).funcs := (Step.framesLocal h).1
  rcases step_withFuncs h (X := s.funcs) (sameTypes_stub (L := L) s) with h' | h'
  · refine ⟨withFuncs σ' s.funcs, ?_, rfl, h'⟩
    show σ' = withFuncs σ' (s.funcs.mapIdx L.stubFI)
    have hσ : σ' = withFuncs σ' σ'.funcs := rfl
    rw [hσ, hfun]
    rfl
  · exfalso
    obtain ⟨E, vs, a, cr, fi, ps, rs, cd, -, -, hf, -, -, hcode, hX, -⟩ := h'
    have hf' : (s.funcs[a]?).map (L.stubFI a) = some fi := (stubS_get s a).symm.trans hf
    obtain ⟨fi₀, h₀, hfi⟩ := Option.map_eq_some_iff.mp hf'
    cases hs : L.stub a with
    | none => exact hX (by rw [h₀, ← hfi, stubFI_none hs])
    | some kc =>
      obtain ⟨k, c⟩ := kc
      rw [stubFI_some hs] at hfi
      rw [← hfi] at hcode
      cases hcode

/-- A host-free linked step in the real store is a consumer step in the stubbed store, or a
call into a provider function. -/
theorem linked_step {P : Profile} {s s' : Store Nat} {f f' : Frame} {code code' : List Admin}
    (h : Execution.Core.Step P (fun _ _ _ _ => False) ⟨s, f, code⟩ ⟨s', f', code'⟩) :
    Execution.Core.Step P (fun _ _ _ _ => False) ⟨L.stubS s, f, code⟩ ⟨L.stubS s', f', code'⟩ ∨
      CallAt (L.stubS s).funcs ⟨s, f, code⟩ ⟨s', f', code'⟩ := by
  have hfun : s'.funcs = s.funcs := (Step.framesLocal h).1
  rcases step_withFuncs h (X := (L.stubS s).funcs) (sameTypes_stub (L := L) s).symm with h' | h'
  · left
    have he : withFuncs s' (L.stubS s).funcs = L.stubS s' := by
      show withFuncs s' (s.funcs.mapIdx L.stubFI) = withFuncs s' (s'.funcs.mapIdx L.stubFI)
      rw [hfun]
    rw [← he]
    exact h'
  · exact .inr h'

/-! ### Callouts -/

/-- A forwarded callout of the consumer is the same callout in the real store. -/
theorem decompose_real_of_stub {s : Store Nat} {code : List Admin} {E : Ctx} {a h : Nat}
    {args : List Val} (hd : decompose? (L.stubS s) code = some (E, a, h, args))
    (ht : L.target h = none) : decompose? s code = some (E, a, h, args) := by
  obtain ⟨fi, yy, ps, rs, hf, hcode, hyy, he, hn, hc⟩ := decompose?_sound hd
  have hf' : (s.funcs[a]?).map (L.stubFI a) = some fi := (stubS_get s a).symm.trans hf
  obtain ⟨fi₀, h₀, hfi⟩ := Option.map_eq_some_iff.mp hf'
  cases hs : L.stub a with
  | some kc =>
    obtain ⟨k, c⟩ := kc
    rw [stubFI_some hs] at hfi
    have hk : FuncCode.host k = .host h := by rw [← hfi] at hcode; exact hcode
    cases hk
    have := (L.target_iff h a).2 ⟨c, hs⟩
    rw [ht] at this
    cases this
  | none =>
    rw [stubFI_none hs] at hfi
    subst hfi
    rw [hc]
    exact decompose?_fill E hyy h₀ he hn hcode

/-- A callout of the linked module is a forwarded callout of the consumer. -/
theorem decompose_stub_of_real {s : Store Nat} (hl : L.Layout s) {code : List Admin} {E : Ctx}
    {a h : Nat} {args : List Val} (hd : decompose? s code = some (E, a, h, args)) :
    decompose? (L.stubS s) code = some (E, a, h, args) ∧ L.target h = none := by
  obtain ⟨fi, yy, ps, rs, hf, hcode, hyy, he, hn, hc⟩ := decompose?_sound hd
  have ht : L.target h = none := hl.noStub a fi h hf hcode
  cases hs : L.stub a with
  | some kc =>
    obtain ⟨k, c⟩ := kc
    have := hl.prov a fi k c hf hs
    rw [hcode] at this
    cases this
  | none =>
    have hf' : (L.stubS s).funcs[a]? = some fi := by rw [stubS_get, hf, Option.map_some, stubFI_none hs]
    rw [hc]
    exact ⟨decompose?_fill E hyy hf' he hn hcode, ht⟩

/-- The host function of a stubbed store with a stub code is a stub. -/
theorem stub_of_host {s : Store Nat} (hl : L.Layout s) {a k a' : Nat} {fi : FuncInst Nat}
    (h₀ : s.funcs[a]? = some fi) (hk : (L.stubFI a fi).code = .host k)
    (ht : L.target k = some a') : ∃ c, L.stub a = some (k, c) := by
  cases hs : L.stub a with
  | none =>
    rw [stubFI_none hs] at hk
    have := hl.noStub a fi k h₀ hk
    rw [ht] at this
    cases this
  | some kc =>
    obtain ⟨k', c⟩ := kc
    rw [stubFI_some hs] at hk
    cases hk
    exact ⟨c, rfl⟩

/-- **A stub callout of the consumer is a call of the provider function in the real store.** -/
theorem stub_callout {s : Store Nat} (hl : L.Layout s) {code : List Admin} {E : Ctx} {a k : Nat}
    {args : List Val} (hd : decompose? (L.stubS s) code = some (E, a, k, args)) {a' : Nat}
    (ht : L.target k = some a') :
    a' = a ∧ ∃ (fi : FuncInst Nat) (c : Func) (ps rs : Ty (.list .val)) (yy : Admin),
      s.funcs[a]? = some fi ∧ fi.code = .wasm c ∧ L.stub a = some (k, c) ∧
      Expand fi.type (.func ps rs) ∧ args.length = ps.length ∧
      code = E.fill (vals args ++ [.ref (.func a), yy]) ∧ yy.IsCallRef := by
  obtain ⟨fiσ, yy, ps, rs, hf, hcode, hyy, he, hn, hc⟩ := decompose?_sound hd
  obtain ⟨fi, h₀, hfi⟩ : ∃ fi, s.funcs[a]? = some fi ∧ L.stubFI a fi = fiσ :=
    Option.map_eq_some_iff.mp ((stubS_get s a).symm.trans hf)
  have hk : (L.stubFI a fi).code = .host k := hfi ▸ hcode
  obtain ⟨c, hs⟩ : ∃ c, L.stub a = some (k, c) := stub_of_host hl h₀ hk ht
  have ha : a' = a := Option.some.inj (ht.symm.trans ((L.target_iff k a).2 ⟨c, hs⟩))
  have hwasm : fi.code = .wasm c := hl.prov a fi k c h₀ hs
  have hty : fi.type = fiσ.type := by rw [← hfi, stubFI_type]
  have he' : Expand fi.type (.func ps rs) := hty ▸ he
  exact ⟨ha, fi, c, ps, rs, yy, h₀, hwasm, hs, he', hn, hc, hyy⟩

/-- Resumption at a forwarded callout is the same thread in both stores. -/
theorem resume_stub {s : Store Nat} {t : Thread} {E : Ctx} {a h : Nat} {args : List Val}
    (hd : decompose? (L.stubS s) (t.config (L.stubS s)).code = some (E, a, h, args))
    (ht : L.target h = none) (r : Result) :
    resumeResult (L.stubS s) t r = resumeResult s t r := by
  have hcode : (t.config (L.stubS s)).code = (t.config s).code := by rw [config_stub]
  have hframe : (t.config (L.stubS s)).frame = (t.config s).frame := by rw [config_stub]
  have hd' : decompose? s (t.config s).code = some (E, a, h, args) :=
    decompose_real_of_stub (hcode ▸ hd) ht
  unfold resumeResult
  simp only
  rw [hd, hd', hframe]

/-! ### Contexts -/

/-- Plug a context into the hole of another. -/
def Ctx.comp : Ctx → Ctx → Ctx
  | .top pre rest, .top pre' rest' => .top (pre ++ pre') (rest' ++ rest)
  | .top pre rest, .label pre' n c E r => .label (pre ++ pre') n c E (r ++ rest)
  | .top pre rest, .handler pre' n cs E r => .handler (pre ++ pre') n cs E (r ++ rest)
  | .top pre rest, .frame pre' n f E r => .frame (pre ++ pre') n f E (r ++ rest)
  | .label pre n c E rest, E' => .label pre n c (Ctx.comp E E') rest
  | .handler pre n cs E rest, E' => .handler pre n cs (Ctx.comp E E') rest
  | .frame pre n f E rest, E' => .frame pre n f (Ctx.comp E E') rest

theorem Ctx.comp_fill : ∀ (E E' : Ctx) (xs : List Admin),
    (Ctx.comp E E').fill xs = E.fill (E'.fill xs)
  | .top pre rest, .top pre' rest', xs => by simp [Ctx.comp, Ctx.fill, vals]
  | .top pre rest, .label pre' n c E r, xs => by simp [Ctx.comp, Ctx.fill, vals]
  | .top pre rest, .handler pre' n cs E r, xs => by simp [Ctx.comp, Ctx.fill, vals]
  | .top pre rest, .frame pre' n f E r, xs => by simp [Ctx.comp, Ctx.fill, vals]
  | .label pre n c E rest, E', xs => by simp [Ctx.comp, Ctx.fill, Ctx.comp_fill E E' xs]
  | .handler pre n cs E rest, E', xs => by simp [Ctx.comp, Ctx.fill, Ctx.comp_fill E E' xs]
  | .frame pre n f E rest, E', xs => by simp [Ctx.comp, Ctx.fill, Ctx.comp_fill E E' xs]

open Silmaril.Proofs.Wasm.Game.Linking.Split in
/-- Replacing the redex of top-level code by top-level code keeps it top-level. -/
theorem topOK_fill {E : Ctx} {X Y : List Admin} (h : TopOK (E.fill X)) (hY : TopOK Y) :
    TopOK (E.fill Y) := by
  cases E with
  | top pre rest =>
    simp only [Ctx.fill] at h ⊢
    obtain ⟨hvx, hr⟩ := TopOK.append.mp h
    obtain ⟨hv, -⟩ := TopOK.append.mp hvx
    exact TopOK.append.mpr ⟨TopOK.append.mpr ⟨hv, hY⟩, hr⟩
  | label pre n c E rest =>
    simp only [Ctx.fill] at h
    exact absurd (h (.label n c (E.fill X)) (by simp)) (by simp [TopAdmin])
  | handler pre n cs E rest =>
    simp only [Ctx.fill] at h
    exact absurd (h (.handler n cs (E.fill X)) (by simp)) (by simp [TopAdmin])
  | frame pre n f E rest =>
    simp only [Ctx.fill] at h ⊢
    obtain ⟨hvx, hr⟩ := TopOK.append.mp h
    obtain ⟨hv, -⟩ := TopOK.append.mp hvx
    exact TopOK.append.mpr ⟨TopOK.append.mpr ⟨hv, TopOK.cons.mpr ⟨trivial, TopOK.nil⟩⟩, hr⟩

end Silmaril.Proofs.Wasm.Game.ULink
