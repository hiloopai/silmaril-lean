module

public import Silmaril.Proofs.Wasm.Resource.ClientArg.Basic

/-!
# Handles passed to internal callees: the protocol invariant

`JH`: the protocol invariant of `I.dlts P I.store` for `(clientSpec ia iu if_).comap moveEvent`:
an invariant, guarded or entering thread for the live list. Entering threads take one silent
step, into the helper's frame (`enterH_step`); they are never at a callout and never finished.
`argIn_sound`: the client sentence over `wasmSem P`, every profile; `checkClientArg_sound`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.ClientArg

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Resource Silmaril.Wasm.Resource.Client
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (StoreIn Avoids typed_refIn answer_refIn callout_mem decompose_toAdmin_none
  ifaceOp?_fst ifaceOp?_snd)

/-- What the check with helpers establishes. -/
structure ArgIn (I : ScalarInstance) (G : Nat → Prop) (H : List Nat) (fs : List Nat)
    (ia iu if_ : Nat) (ps : List (Nat × Nat)) : Prop extends ArgCore I G H fs ia iu if_ ps where
  exports : ∀ j, G (I.addr j)

section
variable {I : ScalarInstance} {G : Nat → Prop} {H : List Nat} {fs : List Nat}
  {ps : List (Nat × Nat)} {ia iu if_ : (ifaceOf I).Imp}

/-- The invariant of a resumed thread. -/
def JRH (I : ScalarInstance) (G : Nat → Prop) (H : List Nat) (fs : List Nat) (ia iu if_ : Nat)
    (ps : List (Nat × Nat)) : Option (List Val) → Config Nat → Prop
  | none, _ => True
  | some L, c => InvH I G H fs ia iu if_ ps L c

/-- **The protocol invariant**: everything holds after an environment fault; otherwise an
invariant, guarded or entering thread for the live list. -/
def JH (I : ScalarInstance) (G : Nat → Prop) (H : List Nat) (fs : List Nat)
    (ia iu if_ : (ifaceOf I).Imp) (ps : List (Nat × Nat)) : Option (List Val) → I.HState → Prop
  | none, _ => True
  | some L, .idle s => StoreIn G s ∧ s.funcs = I.store.funcs ∧ Sigma ps L s.globals
  | some L, .running _ s t =>
    (InvH I G H fs ia.val iu.val if_.val ps L (t.config s) ∨
      GuardedH I G H fs ia.val iu.val if_.val ps L (t.config s) ∨
      EnterH I G H fs ia.val iu.val if_.val ps L (t.config s)) ∧ s.funcs = I.store.funcs
  | some L, .waiting _ s t e => s.funcs = I.store.funcs ∧
    ∀ (v : I.E.Ar e) (q' : Option (List Val)), (πC I ia iu if_).step (some L) (.inl (.ans e v)) =
      some q' → JRH I G H fs ia.val iu.val if_.val ps q'
        ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) v)).config s)

section Vis
variable {f : I.F.Op} {s : Store Nat} {t : Thread} {e : I.E.Op} {L : List Val}

/-- A callout of an invariant thread: another import, skipped by the protocol. -/
theorem visH_inv (hR : ArgIn I G H fs ia.val iu.val if_.val ps) {h : Nat} {args : List Val}
    (callout : CalloutAt s t h args) (op : I.importOp? h args = some e)
    (hy : InvH I G H fs ia.val iu.val if_.val ps L (t.config s)) (hfy : s.funcs = I.store.funcs) :
    ∃ q', (πC I ia iu if_).step (some L) (.inl (.ask e)) = some q' ∧
      JH I G H fs ia iu if_ ps q' (.waiting f s t e) := by
  obtain ⟨a, fi, ha, hf, hcode⟩ := callout_mem callout hy.1
  have he := ifaceOp?_fst op
  have hne : ∀ j : (ifaceOf I).Imp, ∀ hav : Avoids G I.store.funcs j.val, e.1 ≠ j :=
    fun j hav ej => hav a fi ha (hfy ▸ hf) (by rw [hcode, ← he, ej])
  refine ⟨some L, step_skip L _ (ev_ask_ne (ia := ia) (hne _ hR.avU) (hne _ hR.avF)), hfy, ?_⟩
  intro w q' hq'
  obtain rfl := step_eq_skip (ev_ans_ne (iu := iu) (if_ := if_) w (hne _ hR.avA)) hq'
  exact resume_invH hy _ (answer_refIn w)

/-- The answer of a use or a free: skipped by the protocol, the prepared resumption. -/
theorem visH_ret_skip {L' : List Val} {E : Ctx} {b : Nat} {args : List Val} (he : e.1 ≠ ia)
    (hd : decompose? s (t.config s).code = some (E, b, iu.val, args) ∨
      decompose? s (t.config s).code = some (E, b, if_.val, args))
    (hres : ∀ r, RefsOK G r →
      InvH I G H fs ia.val iu.val if_.val ps L' ⟨s, (t.config s).frame, E.fill r.toAdmin⟩) :
    ∀ (w : I.E.Ar e) (q' : Option (List Val)),
      (πC I ia iu if_).step (some L') (.inl (.ans e w)) = some q' →
      JRH I G H fs ia.val iu.val if_.val ps q'
        ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) w)).config s) := by
  intro w q' hq'
  obtain rfl := step_eq_skip (ev_ans_ne (iu := iu) (if_ := if_) w he) hq'
  rcases hd with hd | hd <;>
  · rw [resumeResult_config hd]
    exact hres _ (answer_refIn w)

/-- The answer of an allocation. -/
theorem visH_ret_alloc (hR : ArgIn I G H fs ia.val iu.val if_.val ps) {E : Ctx} {b : Nat}
    (he1 : @Eq (ifaceOf I).Imp e.1 ia) (hd : decompose? s (t.config s).code = some (E, b, ia.val, []))
    (hres₁ : ∀ h, h ∉ L → RefsOK G (.values [h]) → InvH I G H fs ia.val iu.val if_.val ps (h :: L)
      ⟨s, (t.config s).frame, E.fill (Result.values [h]).toAdmin⟩)
    (hres₂ : ∀ r, RefsOK G r → (∀ ws, r ≠ .values ws) →
      InvH I G H fs ia.val iu.val if_.val ps L ⟨s, (t.config s).frame, E.fill r.toAdmin⟩)
    (w : I.E.Ar e) (q' : Option (List Val))
    (hq' : (πC I ia iu if_).step (some L) (.inl (.ans e w)) = some q') :
    JRH I G H fs ia.val iu.val if_.val ps q'
      ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) w)).config s) := by
  rw [step_alloc he1] at hq'
  rw [resumeResult_config hd]
  cases w with
  | values vs =>
    obtain ⟨ws, hws⟩ := vs
    have hres : (I.imports.get e.1).results.length = 1 := by
      have he' : e.1 = ⟨ia.val, ia.isLt⟩ := Fin.ext (congrArg Fin.val he1)
      rw [he']; exact (hR.arA ia.isLt).2
    obtain ⟨h₁, rfl⟩ := List.length_eq_one_iff.1 ((List.Forall₂.length_eq hws).symm.trans hres)
    by_cases hh : h₁ ∈ L
    · simp [Answer.toBehaviour, Answer.toResult, HEv.allocOf, handleStep, hh, fault] at hq'
      subst hq'; trivial
    · simp [Answer.toBehaviour, Answer.toResult, HEv.allocOf, handleStep, hh] at hq'
      subst hq'
      exact hres₁ h₁ hh (answer_refIn (Answer.values (ft := I.imports.get e.1) ⟨[h₁], hws⟩))
  | trap =>
    simp [Answer.toBehaviour, Answer.toResult, HEv.allocOf, handleStep] at hq'
    subst hq'
    exact hres₂ .trap (answer_refIn (Answer.trap (ft := I.imports.get e.1))) (fun _ => nofun)
  | throw a =>
    simp [Answer.toBehaviour, Answer.toResult, HEv.allocOf, handleStep] at hq'
    subst hq'
    exact hres₂ (.throw a) (answer_refIn (Answer.throw (ft := I.imports.get e.1) a)) (fun _ => nofun)

theorem visH_use (hR : ArgIn I G H fs ia.val iu.val if_.val ps) {h : Nat} {E₀ E : Ctx}
    {a₀ b : Nat} {args : List Val} {v : Val} (op : I.importOp? h args = some e)
    (hfy : s.funcs = I.store.funcs) (hd₀ : decompose? s (t.config s).code = some (E₀, a₀, h, args))
    (hd : decompose? s (t.config s).code = some (E, b, iu.val, [v])) (hv : v ∈ L)
    (hres : ∀ r, RefsOK G r →
      InvH I G H fs ia.val iu.val if_.val ps L ⟨s, (t.config s).frame, E.fill r.toAdmin⟩) :
    ∃ q', (πC I ia iu if_).step (some L) (.inl (.ask e)) = some q' ∧
      JH I G H fs ia iu if_ ps q' (.waiting f s t e) := by
  obtain ⟨rfl, rfl⟩ := callout_eq hd₀ hd
  have he1 : @Eq (ifaceOf I).Imp e.1 iu := Fin.ext (ifaceOp?_fst op)
  exact ⟨some L, step_use he1 (ifaceOp?_snd op) hv, hfy,
    visH_ret_skip (fun h' => hR.dAU (by rw [← h', he1])) (.inl hd) hres⟩

theorem visH_free (hR : ArgIn I G H fs ia.val iu.val if_.val ps) {h : Nat} {E₀ E : Ctx}
    {a₀ b : Nat} {args : List Val} {v : Val} (op : I.importOp? h args = some e)
    (hfy : s.funcs = I.store.funcs) (hd₀ : decompose? s (t.config s).code = some (E₀, a₀, h, args))
    (hd : decompose? s (t.config s).code = some (E, b, if_.val, [v])) (hv : v ∈ L)
    (hres : ∀ r, RefsOK G r → InvH I G H fs ia.val iu.val if_.val ps (L.erase v)
      ⟨s, (t.config s).frame, E.fill r.toAdmin⟩) :
    ∃ q', (πC I ia iu if_).step (some L) (.inl (.ask e)) = some q' ∧
      JH I G H fs ia iu if_ ps q' (.waiting f s t e) := by
  obtain ⟨rfl, rfl⟩ := callout_eq hd₀ hd
  have he1 : @Eq (ifaceOf I).Imp e.1 if_ := Fin.ext (ifaceOp?_fst op)
  exact ⟨some (L.erase v), step_free he1 (fin_ne (Ne.symm hR.dUF)) (ifaceOp?_snd op) hv, hfy,
    visH_ret_skip (fun h' => hR.dAF (by rw [← h', he1])) (.inr hd) hres⟩

theorem visH_alloc (hR : ArgIn I G H fs ia.val iu.val if_.val ps) {h : Nat} {E₀ E : Ctx}
    {a₀ b : Nat} {args : List Val} (op : I.importOp? h args = some e)
    (hfy : s.funcs = I.store.funcs) (hd₀ : decompose? s (t.config s).code = some (E₀, a₀, h, args))
    (hd : decompose? s (t.config s).code = some (E, b, ia.val, []))
    (hres₁ : ∀ h, h ∉ L → RefsOK G (.values [h]) → InvH I G H fs ia.val iu.val if_.val ps (h :: L)
      ⟨s, (t.config s).frame, E.fill (Result.values [h]).toAdmin⟩)
    (hres₂ : ∀ r, RefsOK G r → (∀ ws, r ≠ .values ws) →
      InvH I G H fs ia.val iu.val if_.val ps L ⟨s, (t.config s).frame, E.fill r.toAdmin⟩) :
    ∃ q', (πC I ia iu if_).step (some L) (.inl (.ask e)) = some q' ∧
      JH I G H fs ia iu if_ ps q' (.waiting f s t e) := by
  obtain ⟨rfl, rfl⟩ := callout_eq hd₀ hd
  have he1 : @Eq (ifaceOf I).Imp e.1 ia := Fin.ext (ifaceOp?_fst op)
  exact ⟨some L, step_skip L _ (ev_ask_ne (ia := ia) (fun h' => hR.dAU (by rw [← h', he1]))
    (fun h' => hR.dAF (by rw [← h', he1]))), hfy, visH_ret_alloc hR he1 hd hres₁ hres₂⟩

/-- A callout of a guarded thread: a use, a free or an allocation. -/
theorem visH_guard (hR : ArgIn I G H fs ia.val iu.val if_.val ps) {h : Nat}
    {args : List Val} (callout : CalloutAt s t h args) (op : I.importOp? h args = some e)
    (hy : GuardedH I G H fs ia.val iu.val if_.val ps L (t.config s))
    (hfy : s.funcs = I.store.funcs) :
    ∃ q', (πC I ia iu if_).step (some L) (.inl (.ask e)) = some q' ∧
      JH I G H fs ia iu if_ ps q' (.waiting f s t e) := by
  have hf₀ : (t.config s).store.funcs = I.store.funcs := by rw [Thread.config_store]; exact hfy
  obtain ⟨E₀, a₀, hd₀⟩ := callout
  obtain ⟨E, b, ⟨v, hd, hv, hres⟩ | ⟨v, hd, hv, hres⟩ | ⟨hd, hres₁, hres₂⟩⟩ :=
    guardedH_cases hR.toArgCore hf₀ hy
  · exact visH_use hR op hfy hd₀ (by simpa [Thread.config_store] using hd) hv
      (by simpa [Thread.config_store] using hres)
  · exact visH_free hR op hfy hd₀ (by simpa [Thread.config_store] using hd) hv
      (by simpa [Thread.config_store] using hres)
  · exact visH_alloc hR op hfy hd₀ (by simpa [Thread.config_store] using hd)
      (by simpa [Thread.config_store] using hres₁) (by simpa [Thread.config_store] using hres₂)

/-- A finished thread is neither guarded nor entering; its store is invariant. -/
theorem visH_oret (hR : ArgIn I G H fs ia.val iu.val if_.val ps) {r : Result}
    (final : ResultAt s t r)
    (hx : (InvH I G H fs ia.val iu.val if_.val ps L (t.config s) ∨
      GuardedH I G H fs ia.val iu.val if_.val ps L (t.config s) ∨
      EnterH I G H fs ia.val iu.val if_.val ps L (t.config s)) ∧ s.funcs = I.store.funcs) :
    StoreIn G s ∧ s.funcs = I.store.funcs ∧ Sigma ps L s.globals := by
  obtain ⟨hy | hy | hy, hfy⟩ := hx
  · exact ⟨Thread.config_store s t ▸ hy.1.1, hfy, Thread.config_store s t ▸ hy.2.1⟩
  · have hf₀ : (t.config s).store.funcs = I.store.funcs := by rw [Thread.config_store]; exact hfy
    obtain ⟨E, b, ⟨v, hd, -⟩ | ⟨v, hd, -⟩ | ⟨hd, -⟩⟩ := guardedH_cases hR.toArgCore hf₀ hy <;>
      · rw [final, decompose_toAdmin_none] at hd
        cases hd
  · exact absurd final (enterH_not_result hy r)

end Vis

/-- The vis steps. -/
theorem jh_vis (hR : ArgIn I G H fs ia.val iu.val if_.val ps) {P : Profile}
    {q : Option (List Val)} {x y : I.HState} {o : Move I.E I.F} (hs : I.DTrans P x (some o) y)
    (hx : JH I G H fs ia iu if_ ps q x) :
    ∃ q', (πC I ia iu if_).step q o = some q' ∧ JH I G H fs ia iu if_ ps q' y := by
  rcases q with _ | L
  · exact ⟨none, step_none o, trivial⟩
  cases hs with
  | call s f =>
    exact ⟨some L, step_skip L _ rfl,
      .inl (invH_invoke hx.1 hx.2.2 (hR.exports f.1) (typed_refIn f.2.2)), hx.2.1⟩
  | ucall callout op =>
    obtain ⟨hy | hy | hy, hfy⟩ := hx
    · exact visH_inv hR callout op hy hfy
    · exact visH_guard hR callout op hy hfy
    · exact absurd callout (enterH_no_callout hy)
  | uret v =>
    obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1
      (clientSpec_oTotal ia iu if_ (some L) (.inl (.ans _ v)) trivial)
    exact ⟨q', hq', match q' with
      | none => trivial
      | some _ => ⟨.inl (hx.2 v _ hq'), hx.1⟩⟩
  | oret final answer => exact ⟨some L, step_skip L _ rfl, visH_oret hR final hx⟩

/-- The silent steps. -/
theorem jh_tau (hR : ArgIn I G H fs ia.val iu.val if_.val ps) {P : Profile}
    {q : Option (List Val)} {x y : I.HState} (hst : I.DTrans P x none y)
    (hx : JH I G H fs ia iu if_ ps q x) : JH I G H fs ia iu if_ ps q y := by
  rcases q with _ | L
  · trivial
  cases hst with
  | @tau f s s' t t' h =>
    obtain ⟨hy | hy | hy, hfy⟩ := hx
    · obtain ⟨f', code', ht', hstep⟩ := h
      have hf₀ : (t.config s).store.funcs = I.store.funcs := by
        rw [Thread.config_store]; exact hfy
      obtain ⟨hz, hfz⟩ := step_invH hR.toArgCore hstep hf₀ hy
      subst ht'
      exact ⟨hz, hfz.trans hf₀⟩
    · obtain ⟨hh, _, hc⟩ := guardedH_callout hR.toArgCore hfy hy
      exact absurd h (calloutAt_no_internal hc _)
    · obtain ⟨f', code', ht', hstep⟩ := h
      obtain ⟨hz, hsz⟩ := enterH_step hy hstep
      subst ht'
      refine ⟨.inl hz, ?_⟩
      have hs' : s' = s := by simpa [Thread.config_store] using hsz
      exact hs' ▸ hfy

/-- **The protocol invariant of the instance's transition system** (every profile). -/
def argLTSInv (hR : ArgIn I G H fs ia.val iu.val if_.val ps) (P : Profile) :
    LTSInv (I.dlts P I.store) (πC I ia iu if_) where
  J := JH I G H fs ia iu if_ ps
  init := by
    refine ⟨hR.store, rfl, fun p hp hon => ?_⟩
    obtain ⟨v, hv, hv0⟩ := hon
    rw [hR.init p hp] at hv; cases hv; exact absurd rfl hv0
  tau := fun hst hx => jh_tau hR hst hx
  vis := fun hst hx => jh_vis hR hst hx

/-- **Soundness of the analysis with helpers** (every profile): every play of the instance is
accepted by the client sentence. -/
theorem argIn_accepts (hR : ArgIn I G H fs ia.val iu.val if_.val ps) (P : Profile) :
    ∀ p ∈ I.strategy P I.store, (πC I ia iu if_).Accepts p :=
  dlts_accepts (argLTSInv hR P) (clientSpec_oTotal ia iu if_)

/-- **The client sentence over `wasmSem P`** (every profile). -/
theorem argIn_sound (hR : ArgIn I G H fs ia.val iu.val if_.val ps) (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
      (WasmProg.ofInstance I) (clientSpec ia iu if_) :=
  models_of_plays _ _ (argIn_accepts hR P)

end

end Silmaril.Wasm.Resource.ClientArg

/-! ## The checker -/

namespace Silmaril.Wasm.Resource.ClientArg

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Resource Silmaril.Wasm.Resource.Client
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (instOf progOf instance? isInstance_instOf mem_exprRF mem_exprCalls
  avoidsB_sound PlOK CallPl storeIn_of_rootsB addr_mem_roots)

theorem funcOkH_sound {s : Store Nat} {fs G : List Nat} {ia iu if_ : Nat} {ps : List (Nat × Nat)}
    {H : List Nat} {F : List Fact} {a : Nat} {fi : FuncInst Nat} {code : Func}
    (h : funcOkH s fs G ia iu if_ ps H F a = true)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code) :
    fi.module.funcs = fs ∧
      (∀ ins ∈ code.body, PlOK (CallPl (· ∈ G) (badH s ia iu if_ H) fs) ins) ∧
      okL (cfgH s fs ia iu if_ ps H) fi.module.globals F .other code.body = true := by
  simp only [funcOkH, hf, hcode, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hm, hrf⟩, hcall⟩, hok⟩ := h
  refine ⟨hm, fun ins hins => .inr ⟨fun x hx b hb => ?_, fun x hx b hb => ?_⟩, hok⟩
  · simpa [hb] using hrf x (mem_exprRF hins hx)
  · have h₁ := hcall x (mem_exprCalls hins hx)
    simpa only [hb, Bool.or_eq_true, List.contains_iff_mem] using h₁

theorem helperOK_sound {s : Store Nat} {b : Nat} (h : helperOK s b = true) :
    ∃ (fi : FuncInst Nat) (code : Func) (pt rt : Ty (.list .val)), s.funcs[b]? = some fi ∧
      fi.code = .wasm code ∧ Expand fi.type (.func pt rt) ∧ pt.length = 1 := by
  unfold helperOK at h
  split at h
  · rename_i fi hf
    simp only [Bool.and_eq_true] at h
    obtain ⟨hw, ht⟩ := h
    split at hw
    · rename_i code hcode
      split at ht
      · rename_i pt rt he
        exact ⟨fi, code, pt, rt, hf, hcode, Expand.iff.2 he, by simpa using ht⟩
      · cases ht
    · cases hw
  · cases h

/-- **The checker establishes `ArgIn`.** -/
theorem argIn_of_checkArgInst {I : ScalarInstance} (hok : I.Ok) {ia iu if_ : Nat}
    {ps : List (Nat × Nat)} {hs : List Nat} (h : checkArgInst I ia iu if_ ps hs = true) :
    ArgIn I (· ∈ reachArg I ia iu if_ (helpersOf I hs)) (helpersOf I hs) (fsOf I) ia iu if_ ps := by
  simp only [checkArgInst, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hAU, hAF⟩, hUF⟩, haA⟩, hrA⟩, haU⟩, haF⟩, hP⟩, hinit⟩, hfun⟩, hhelp⟩,
    hroots⟩, hvA⟩, hvU⟩, hvF⟩ := h
  refine ⟨⟨hok, fun a fi code ha hf hcode => ?_, fun a fi code ha hf hcode => ?_, fun b hb => ?_,
    storeIn_of_rootsB hroots, avoidsB_sound hvA, avoidsB_sound hvU,
    avoidsB_sound hvF, fun a ha hb => ?_, hP, fun p hp => by simpa using hinit p hp, hAU, hAF, hUF,
    fun hi => ⟨arity_of haA hi, arity_res hrA hi⟩, fun hi => arity_of haU hi,
    fun hi => arity_of haF hi⟩, addr_mem_roots hok hroots⟩
  · obtain ⟨h₁, h₂, -⟩ := funcOkH_sound (hfun a ha) hf hcode
    exact ⟨h₁, h₂⟩
  · exact (funcOkH_sound (hfun a ha) hf hcode).2.2
  · obtain ⟨fi, code, pt, rt, hf, hcode, hexp, hpt⟩ := helperOK_sound (hhelp b hb).1
    obtain ⟨hm, hpl, hokb⟩ := funcOkH_sound (hhelp b hb).2 hf hcode
    exact ⟨fi, code, pt, rt, hf, hcode, hexp, hpt, hm, hpl, hokb⟩
  · have := (List.mem_filter.1 ha).2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    simp [hb] at this

/-- **Soundness of the client checker with helpers on a module** (every profile, no determinism
assumed). -/
theorem checkClientArg_sound {m : Module} {ia iu if_ : (ifaceOf (instOf m)).Imp}
    {ps : List (Nat × Nat)} {hs : List Nat}
    (h : checkClientArg m ia.val iu.val if_.val ps hs = true) (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
      (progOf m) (clientSpec ia iu if_) := by
  simp only [checkClientArg, Bool.and_eq_true] at h
  obtain ⟨mt, hI⟩ := isInstance_instOf h.1
  exact argIn_sound (argIn_of_checkArgInst hI.ok h.2) P

end Silmaril.Wasm.Resource.ClientArg
