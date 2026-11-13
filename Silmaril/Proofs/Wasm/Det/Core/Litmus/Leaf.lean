module

public import Silmaril.Wasm.Det.Core.Thms
public import Silmaril.Wasm.SSA.CoreCert.Thms
public import Silmaril.Wasm.Interp.Thms
public import Silmaril.Wasm.Det.Core.Litmus.Defs

/-!
# Store-free leaf functions are deterministic and stateless (proofs)

A store-free leaf function (`Silmaril.Wasm.SSA.leafFunc`: store-free, call-free code with integer
locals) whose body is native-profile code (`nativeFuncsB [fi]`) is, at **every** profile and in
**every** store holding it, deterministic modulo traps and imports, and stateless: its runs do
not depend on the rest of the store.

The invariant `LeafInv a fi` combines the leaf invariant `LeafConf` of
`Silmaril.Wasm.SSA.CoreCert.Leaf` (runs of leaf code are runs in any store holding the same function,
`steps_swap`, and keep the store) with silmaril-lean's native-profile code `NAdmins`
(`Silmaril.Wasm.Interp`). Runs are moved into the store `nativeStore a fi s`, which holds only
copies of `fi`, where host-free normal forms are unique at every profile
(`Silmaril.Wasm.Interp.eq_of_steps_nf`). Leaf configurations never stop at an import call
(`leafInv_no_call`): resuming one would put an exception reference into leaf code.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Core.Leaf

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Det.Core
open Silmaril.Wasm.SSA.CoreCert (LeafConf swapStore PAdmins PAdmin FrameP LeafAt step_swap
  step_swap' steps_swap pAdmins_append pAdmins_cons)
open Silmaril.Proofs.Wasm.Det.Core (inv_steps)
open Silmaril.Wasm.Numerics (Profile)

/-- The store `s` with only copies of `fi`, at addresses `0 … a`. -/
def nativeStore (a : Nat) (fi : FuncInst Nat) (s : Store Nat) : Store Nat :=
  { s with funcs := List.replicate a fi ++ [fi] }

theorem nativeStore_get (a : Nat) (fi : FuncInst Nat) (s : Store Nat) :
    (nativeStore a fi s).funcs[a]? = some fi := by
  simp [nativeStore]

theorem nativeStore_ok {a : Nat} {fi : FuncInst Nat} {s : Store Nat}
    (h : Binaryen.NativeFuncsOk [fi]) : Binaryen.NativeFuncsOk (nativeStore a fi s).funcs := by
  intro g hg
  have hg' : g = fi := by
    simp only [nativeStore, List.mem_append, List.mem_replicate, List.mem_singleton] at hg
    rcases hg with ⟨-, rfl⟩ | rfl <;> rfl
  exact h g (by simp [hg'])

/-- The leaf invariant: leaf code in a store holding `fi` at `a`, and native-profile code. -/
def LeafInv (a : Nat) (fi : FuncInst Nat) (c : Config Nat) : Prop :=
  LeafConf a c ∧ Silmaril.Wasm.Interp.NAdmins c.code ∧ c.store.funcs[a]? = some fi

/-- The leaf invariant is preserved by host-free steps. -/
theorem leafInv_step {P : Profile} {a : Nat} {fi : FuncInst Nat}
    (hn : Binaryen.NativeFuncsOk [fi]) {c d : Config Nat} (hc : LeafInv a fi c)
    (h : Step P Det.noHost c d) : LeafInv a fi d := by
  have ht : (nativeStore a fi c.store).funcs[a]? = c.store.funcs[a]? :=
    (nativeStore_get a fi c.store).trans hc.2.2.symm
  obtain ⟨hs, hst, hl⟩ := step_swap' h hc.1 ht
  have hN : Silmaril.Wasm.Interp.NAdmins d.code :=
    (Silmaril.Wasm.Interp.nAdmins_step hst hc.2.1 (nativeStore_ok hn)).1
  exact ⟨hl, hN, by rw [hs]; exact hc.2.2⟩

/-- Leaf code around a hole is leaf code inside it. -/
theorem pAdmins_fill {a : Nat} : ∀ (E : Ctx) (xs : List Admin), PAdmins a (E.fill xs) →
    PAdmins a xs
  | .top _ _, _, h => by
    simp only [Ctx.fill, pAdmins_append] at h
    exact h.1.2
  | .label _ _ _ E _, xs, h => by
    simp only [Ctx.fill, pAdmins_append, pAdmins_cons] at h
    exact pAdmins_fill E xs h.1.2.1.2
  | .handler _ _ _ E _, xs, h => by
    simp only [Ctx.fill, pAdmins_append, pAdmins_cons] at h
    exact pAdmins_fill E xs h.1.2.1
  | .frame _ _ _ E _, xs, h => by
    simp only [Ctx.fill, pAdmins_append, pAdmins_cons] at h
    exact pAdmins_fill E xs h.1.2.1.2

/-- **Leaf code never stops at an import call.** -/
theorem leafInv_no_call {a : Nat} {fi : FuncInst Nat} {c : Config Nat} (hc : LeafInv a fi c)
    {E : Ctx} {a' h : Nat} {args : List Val}
    (hd : decompose? c.store c.code = some (E, a', h, args)) : False := by
  have hco : Silmaril.Wasm.Game.CalloutAt c.store (.active c.frame c.code) h args := ⟨E, a', hd⟩
  have hst : Step (Profile.spec) (Silmaril.Wasm.Game.answerHost h args (.throw 0)) c
      ((resumeResult c.store (.active c.frame c.code) (.throw 0)).config c.store) :=
    Silmaril.Wasm.Game.calloutAt_step hco ⟨rfl, rfl, rfl⟩
  have hres : (resumeResult c.store (.active c.frame c.code) (.throw 0)).config c.store =
      ⟨c.store, c.frame, E.fill (Result.throw 0).toAdmin⟩ := by
    simp only [resumeResult, Thread.config, hd]
  obtain ⟨-, -, hp, -⟩ := step_swap hst hc.1.1 hc.1.2.1 hc.1.2.2 (t := c.store) rfl
  rw [hres] at hp
  have hp' : PAdmins a (Result.throw 0).toAdmin := pAdmins_fill E _ hp
  simp [Result.toAdmin, PAdmins, PAdmin] at hp'

/-- A non-trapping stop of leaf code is a result; its output only depends on the code. -/
theorem outAt_swap {a : Nat} {fi : FuncInst Nat} {d : Config Nat} (hd : LeafInv a fi d)
    {o : Out} (ho : OutAt d o) (t : Store Nat) : OutAt (swapStore t d) o := by
  cases ho with
  | ret hr hc => exact .ret hr hc
  | call hd' => exact (leafInv_no_call hd hd').elim

/-- **Host-free runs of leaf code reach at most one non-trapping stop**, at every profile. -/
theorem leafInv_segDet {P : Profile} {a : Nat} {fi : FuncInst Nat}
    (hn : Binaryen.NativeFuncsOk [fi]) {c : Config Nat} (hc : LeafInv a fi c) : SegDet P c := by
  intro d₁ d₂ h₁ h₂ hs₁ hs₂
  have ht : (nativeStore a fi c.store).funcs[a]? = c.store.funcs[a]? :=
    (nativeStore_get a fi c.store).trans hc.2.2.symm
  have hI₁ : LeafInv a fi d₁ := inv_steps (fun _ _ hx hxy => leafInv_step hn hx hxy) h₁ hc
  have hI₂ : LeafInv a fi d₂ := inv_steps (fun _ _ hx hxy => leafInv_step hn hx hxy) h₂ hc
  obtain ⟨e₁, r₁, -⟩ := steps_swap h₁ hc.1 ht
  obtain ⟨e₂, r₂, -⟩ := steps_swap h₂ hc.1 ht
  have hN : Silmaril.Wasm.Interp.NConfig (swapStore (nativeStore a fi c.store) c) :=
    ⟨hc.2.1, nativeStore_ok hn⟩
  have n₁ : Stop (swapStore (nativeStore a fi c.store) d₁) :=
    ⟨_, outAt_swap hI₁ hs₁.choose_spec _⟩
  have n₂ : Stop (swapStore (nativeStore a fi c.store) d₂) :=
    ⟨_, outAt_swap hI₂ hs₂.choose_spec _⟩
  have he : swapStore (nativeStore a fi c.store) d₁ = swapStore (nativeStore a fi c.store) d₂ :=
    Silmaril.Wasm.Interp.eq_of_steps_nf hN r₁ r₂ (fun _ hx => Stop.no_step n₁ hx)
      (fun _ hx => Stop.no_step n₂ hx)
  have hf : d₁.frame = d₂.frame := by simpa only [swapStore] using congrArg Config.frame he
  have hcode : d₁.code = d₂.code := by simpa only [swapStore] using congrArg Config.code he
  have hs : d₁.store = d₂.store := e₁.trans e₂.symm
  rcases d₁ with ⟨s₁, f₁, k₁⟩
  rcases d₂ with ⟨s₂, f₂, k₂⟩
  simp only at hf hcode hs
  rw [hf, hcode, hs]

/-- Numbers are leaf code. -/
theorem pAdmins_vals {a : Nat} : ∀ {vs : List Val}, (∀ v ∈ vs, ∃ n, v = .num n) →
    PAdmins a (vals vs)
  | [], _ => trivial
  | v :: vs, h => by
    obtain ⟨n, rfl⟩ := h v List.mem_cons_self
    refine ⟨?_, pAdmins_vals fun w hw => h w (List.mem_cons_of_mem _ hw)⟩
    rcases n with ⟨⟨t | t⟩, b⟩ <;> rfl

/-- The invocation of a leaf function on numbers satisfies the leaf invariant. -/
theorem leafInv_invoke {s : Store Nat} {a : Nat} {fi : FuncInst Nat} {fn : Func}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hleaf : Silmaril.Wasm.SSA.leafFunc fn = true) {vs : List Val} (hvs : ∀ v ∈ vs, ∃ n, v = .num n) :
    LeafInv a fi (invoke s a vs) := by
  have hp : PAdmins a (vals vs ++ [.ref (.func a),
      .callRefType ((s.funcs[a]?.map FuncInst.type).getD default)]) :=
    pAdmins_append.mpr ⟨pAdmins_vals hvs, ⟨Or.inr rfl, trivial, trivial⟩⟩
  have hfr : FrameP a ({} : Frame) := fun _ hv => by simp at hv
  exact ⟨⟨hp, hfr, ⟨fi, fn, hfi, hcode, hleaf⟩⟩, Silmaril.Wasm.Interp.nAdmins_invoke s a vs, hfi⟩

/-- The leaf invariant is `Closed`. -/
theorem leafInv_closed {P : Profile} {a : Nat} {fi : FuncInst Nat}
    (hn : Binaryen.NativeFuncsOk [fi]) : Closed P (LeafInv a fi) where
  step _ _ hc h := leafInv_step hn hc h
  resume _ _ _ _ _ _ hc hd := (leafInv_no_call hc hd).elim

/-- **A native store-free leaf function is deterministic modulo traps and imports**, at every
profile, in every store holding it, on numeric arguments. -/
theorem detCall_leaf {P : Profile} {s : Store Nat} {a : Nat} {fi : FuncInst Nat} {fn : Func}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hleaf : Silmaril.Wasm.SSA.leafFunc fn = true) (hn : Binaryen.NativeFuncsOk [fi]) {vs : List Val}
    (hvs : ∀ v ∈ vs, ∃ n, v = .num n) : DetCall P s a vs :=
  detCfg_of_closed (leafInv_closed hn) (fun _ hc => leafInv_segDet hn hc)
    (leafInv_invoke hfi hcode hleaf hvs)

/-- **A native store-free leaf function is stateless**: invocations on the same numbers in any
two stores holding it agree, at every profile. -/
theorem obsAgree_leaf {P : Profile} {s₁ s₂ : Store Nat} {a : Nat} {fi : FuncInst Nat} {fn : Func}
    (hfi₁ : s₁.funcs[a]? = some fi) (hfi₂ : s₂.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hleaf : Silmaril.Wasm.SSA.leafFunc fn = true) (hn : Binaryen.NativeFuncsOk [fi]) {vs : List Val}
    (hvs : ∀ v ∈ vs, ∃ n, v = .num n) : ObsAgree P (invoke s₁ a vs) (invoke s₂ a vs) := by
  intro tr d₁ d₂ o₁ o₂ h₁ h₂ ho₁ ho₂
  have hI₁ : LeafInv a fi (invoke s₁ a vs) := leafInv_invoke hfi₁ hcode hleaf hvs
  have hI₂ : LeafInv a fi (invoke s₂ a vs) := leafInv_invoke hfi₂ hcode hleaf hvs
  have hstep : ∀ x y, LeafInv a fi x → Step P Det.noHost x y → LeafInv a fi y :=
    fun _ _ hx hxy => leafInv_step hn hx hxy
  cases h₁ with
  | call hs hd _ => exact (leafInv_no_call (inv_steps hstep hs hI₁) hd).elim
  | stop hs₁ =>
    show o₁ = o₂
    cases h₂ with
    | stop hs₂ =>
      show o₁ = o₂
      have hJ₂ : LeafInv a fi d₂ := inv_steps hstep hs₂ hI₂
      have ht : s₁.funcs[a]? = (invoke s₂ a vs).store.funcs[a]? := hfi₁.trans hfi₂.symm
      obtain ⟨-, r₂, -⟩ := steps_swap hs₂ hI₂.1 ht
      have hinv : swapStore s₁ (invoke s₂ a vs) = invoke s₁ a vs := by
        simp only [swapStore, invoke, hfi₁, hfi₂]
      rw [hinv] at r₂
      have ho₂' : OutAt (swapStore s₁ d₂) o₂ := outAt_swap hJ₂ ho₂ s₁
      have he : d₁ = swapStore s₁ d₂ :=
        leafInv_segDet hn hI₁ d₁ _ hs₁ r₂ ⟨_, ho₁⟩ ⟨_, ho₂'⟩
      rw [he] at ho₁
      exact OutAt.unique ho₁ ho₂'

/-! ## The executable leaf check -/

open Silmaril.Wasm.Det.Core.Litmus (leafCheck numParam leafCode numParams)

/-- What `leafCheck` establishes. -/
theorem leafCheck_spec {s : Store Nat} {a : Nat} (h : leafCheck s a = true) :
    ∃ fi fn, s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧ Silmaril.Wasm.SSA.leafFunc fn = true ∧
      Binaryen.NativeFuncsOk [fi] ∧
      ∀ ps rs, fi.type.funcType? = some (ps, rs) → ∀ t ∈ ps, numParam t = true := by
  unfold leafCheck at h
  rcases hfi : s.funcs[a]? with _ | fi
  · rw [hfi] at h
    cases h
  · rw [hfi] at h
    have h' : leafCode fi.code = true ∧ Silmaril.Wasm.Interp.nativeFuncsB [fi] = true ∧
        numParams fi.type = true := by
      simpa only [Bool.and_eq_true, and_assoc] using h
    rcases hc : fi.code with fn | hh
    · have hl : Silmaril.Wasm.SSA.leafFunc fn = true := by
        simpa only [hc, leafCode] using h'.1
      refine ⟨fi, fn, rfl, hc, hl, Silmaril.Wasm.Interp.nativeFuncsOk_of_check h'.2.1, ?_⟩
      intro ps rs hty t ht
      have hall : ps.all numParam = true := by simpa only [numParams, hty] using h'.2.2
      exact List.all_eq_true.mp hall t ht
    · have hl : leafCode fi.code = true := h'.1
      rw [hc] at hl
      cases hl

/-- Values of numeric types are numbers. -/
theorem nums_of_forall₂ {s : Store Nat} : ∀ {vs : List Val} {ts : List Validation.CValType},
    List.Forall₂ (ValOk s) vs ts → (∀ t ∈ ts, numParam t = true) → ∀ v ∈ vs, ∃ n, v = .num n
  | [], [], .nil, _ => fun _ hv => by simp at hv
  | v :: vs, t :: ts, .cons hv hrest, hts => by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw'
    · have ht : numParam t = true := hts t List.mem_cons_self
      cases hv with
      | num n => exact ⟨n, rfl⟩
      | vec b => simp [numParam] at ht
      | ref _ => simp [numParam] at ht
    · exact nums_of_forall₂ hrest (fun t' ht' => hts t' (List.mem_cons_of_mem _ ht')) w hw'

/-- **Leaf check ⇒ determinism**, at every profile. -/
theorem detFn_of_leafCheck {P : Profile} {s : Store Nat} {a : Nat} (h : leafCheck s a = true) :
    DetFn P s a := by
  obtain ⟨fi, fn, hfi, hcode, hleaf, hn, hps⟩ := leafCheck_spec h
  intro vs hok
  obtain ⟨fi', ps, rs, hfi', he, hvs⟩ := hok
  have hfe : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  subst hfe
  have hty : fi'.type.funcType? = some (ps.toList, rs.toList) := by
    unfold Validation.DefType.funcType?
    rw [Validation.Expand.iff.mp he]
  exact detCall_leaf hfi hcode hleaf hn (nums_of_forall₂ hvs (hps _ _ hty))

/-- **Leaf check ⇒ statelessness** over every store holding the same function, at every
profile. -/
theorem statelessFn_of_leafCheck {P : Profile} {s : Store Nat} {a : Nat}
    (h : leafCheck s a = true) : StatelessFn P (fun t => t.funcs[a]? = s.funcs[a]?) a := by
  obtain ⟨fi, fn, hfi, hcode, hleaf, hn, hps⟩ := leafCheck_spec h
  intro s₁ s₂ vs h₁ h₂ hok _
  obtain ⟨fi', ps, rs, hfi', he, hvs⟩ := hok
  have hfe : fi' = fi := Option.some.inj (hfi'.symm.trans (h₁.trans hfi))
  subst hfe
  have hty : fi'.type.funcType? = some (ps.toList, rs.toList) := by
    unfold Validation.DefType.funcType?
    rw [Validation.Expand.iff.mp he]
  exact obsAgree_leaf (h₁.trans hfi) (h₂.trans hfi) hcode hleaf hn
    (nums_of_forall₂ hvs (hps _ _ hty))

end Silmaril.Proofs.Wasm.Det.Core.Leaf
