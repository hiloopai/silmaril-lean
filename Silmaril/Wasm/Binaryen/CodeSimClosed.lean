module

public import Silmaril.Wasm.Binaryen.CodeSimModule
public import Silmaril.Wasm.Binaryen.InlUnwrapClosed
public import Silmaril.Wasm.Binaryen.InlDet
public import Silmaril.Wasm.Binaryen.InlHost
public import Silmaril.Wasm.SingleThreaded.NoRedex

@[expose] public section

/-! # One code simulation is enough under the closed host

`exportRefines_of_bodiesRel` (`CodeSimModule.lean`) turns a `BaseSim` for a base
relation `BI` into export refinement in one direction: every observation of the left
module is one of the right module. Export equivalence needs the converse too, and some
rewrites only have a `BaseSim` in one direction (guard inversion,
`RemoveUnusedBrsGuardSim.lean`).

Under the closed host and the deterministic profile the converse follows from the one
simulation, as for block unwrapping (`InlUnwrapClosed.lean`):

* closed reduction is confluent (`Det.DStep.join'`), so normal forms are unique and a
  configuration with a normal form does not diverge (`nf_not_div_closed`);
* a typed left configuration terminates, diverges, or reaches a normal form stuck on a
  host call (progress);
* the simulation carries each case to the right side: a result to the same result,
  divergence to divergence, and a stuck host call to a stuck host call
  (`stuck_transport`, which needs that the left sides of the runtime base pairs hold
  no host-call redex, `NoRedexB`).

So the right side's result or divergence is the left side's
(`runs_back`), and the right module refines the left one (`exportRefines_back`).
-/

namespace Silmaril.Wasm.Binaryen.CodeSimClosed

open Execution.Core Execution.Core.Sim Validation Numerics
open SingleThreaded (Ctx decompose? decompHead topRedex)

variable {H : Type}

/-! ## Host-call redexes -/

/-- The redex search at a head does not look at the code after it. -/
theorem topRedex_rest {s : Store H} {vs : List Val} {r : List Admin} (r' : List Admin)
    {E : Ctx} {a : Nat} {hh : H} {args : List Val}
    (h : topRedex s vs r = some (E, a, hh, args)) :
    ∃ E', topRedex s vs r' = some (E', a, hh, args) := by
  unfold topRedex at h ⊢
  split at h
  · split at h
    · dsimp only at h ⊢
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        rename_i a' _ h' n _ _ _
        simp_all
      · cases h
    · cases h
  · cases h

theorem decompHead_rest {s : Store H} {vs : List Val} {d : Admin} {r : List Admin}
    (r' : List Admin) {E : Ctx} {a : Nat} {hh : H} {args : List Val}
    (h : decompHead s vs d r = some (E, a, hh, args)) :
    ∃ E', decompHead s vs d r' = some (E', a, hh, args) := by
  cases d with
  | label n cont body =>
    simp only [decompHead, Option.map_eq_some_iff] at h ⊢
    obtain ⟨⟨E₀, a₀, h₀, args₀⟩, hb, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
    exact ⟨_, _, hb, rfl⟩
  | handler n cs body =>
    simp only [decompHead, Option.map_eq_some_iff] at h ⊢
    obtain ⟨⟨E₀, a₀, h₀, args₀⟩, hb, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
    exact ⟨_, _, hb, rfl⟩
  | frame n f body =>
    simp only [decompHead, Option.map_eq_some_iff] at h ⊢
    obtain ⟨⟨E₀, a₀, h₀, args₀⟩, hb, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
    exact ⟨_, _, hb, rfl⟩
  | _ =>
    simp only [decompHead] at h ⊢
    split at h
    · rw [ite_eq_left (by assumption)]
      exact topRedex_rest r' h
    · cases h

/-- A host-call redex is one in every store with related functions. -/
theorem decompose?_storeRel {BI : List Instr → List Instr → Prop} {s t : Store H}
    (hst : StoreRel (FuncRel BI) s t) {code : List Admin} {E : Ctx} {a : Nat} {hh : H}
    {args : List Val} (hd : decompose? s code = some (E, a, hh, args)) :
    ∃ E', decompose? t code = some (E', a, hh, args) := by
  obtain ⟨fi, yy, ps, rs, hfi, hcode, hyy, he, hlen, rfl⟩ := SingleThreaded.decompose?_sound hd
  obtain ⟨gi, hgi, hfg⟩ := forall₂_getElem? hst.funcs hfi
  obtain ⟨hty, -, hc⟩ := hfg
  have hgc : gi.code = .host hh := by
    revert hc
    rw [hcode]
    cases gi.code with
    | wasm g => intro hc; exact hc.elim
    | host h' => intro hc; exact congrArg _ hc.symm
  have hred := SingleThreaded.decompose?_redex hyy hgi (hty ▸ he) hlen hgc
  exact Unwrap.redex_fill_closed hred E

/-! ## Runs lifted through contexts -/

section Lift

variable {P : Profile} {host : HostSemantics H}

theorem steps_ctx {c c' : Config H} (h : Steps P host c c') (vs : List Val) (rest : List Admin) :
    Steps P host ⟨c.store, c.frame, vals vs ++ c.code ++ rest⟩
      ⟨c'.store, c'.frame, vals vs ++ c'.code ++ rest⟩ := by
  induction h with
  | refl => exact .refl
  | @tail b d _ hs ih =>
    obtain ⟨_, _, _⟩ := b
    obtain ⟨_, _, _⟩ := d
    exact ih.tail (Step.append_right (Step.vals_left hs vs) rest)

theorem steps_label {c c' : Config H} (h : Steps P host c c') (n : Nat) (cont : List Instr) :
    Steps P host ⟨c.store, c.frame, [.label n cont c.code]⟩
      ⟨c'.store, c'.frame, [.label n cont c'.code]⟩ := by
  induction h with
  | refl => exact .refl
  | @tail b d _ hs ih =>
    obtain ⟨_, _, _⟩ := b
    obtain ⟨_, _, _⟩ := d
    exact ih.tail (Step.ctxtLabel hs)

theorem steps_handler {c c' : Config H} (h : Steps P host c c') (n : Nat) (cs : List Catch) :
    Steps P host ⟨c.store, c.frame, [.handler n cs c.code]⟩
      ⟨c'.store, c'.frame, [.handler n cs c'.code]⟩ := by
  induction h with
  | refl => exact .refl
  | @tail b d _ hs ih =>
    obtain ⟨_, _, _⟩ := b
    obtain ⟨_, _, _⟩ := d
    exact ih.tail (Step.ctxtHandler hs)

theorem steps_frame {c c' : Config H} (h : Steps P host c c') (n : Nat) (f : Frame) :
    Steps P host ⟨c.store, f, [.frame n c.frame c.code]⟩
      ⟨c'.store, f, [.frame n c'.frame c'.code]⟩ := by
  induction h with
  | refl => exact .refl
  | @tail b d _ hs ih =>
    obtain ⟨_, _, _⟩ := b
    obtain ⟨_, _, _⟩ := d
    exact ih.tail (Step.ctxtFrame hs)

end Lift

/-! ## Stuck host calls -/

/-- The left sides of the runtime base pairs hold no host-call redex. -/
def NoRedexB (H : Type) (B : List Admin → List Admin → Prop) : Prop :=
  ∀ x y, B x y → ∀ (s : Store H) (vs : List Val) (rest : List Admin),
    decompose? s (vals vs ++ x ++ rest) = none

theorem decompose?_head {s : Store H} {vs : List Val} {d : Admin} (hd : d.val? = none)
    (r : List Admin) : decompose? s (vals vs ++ d :: r) = decompHead s vs d r :=
  SingleThreaded.decompose?_of_split (SingleThreaded.splitVals_vals_cons hd r)

theorem sizeOf_body_lt {V : List Val} {a : Admin} {xr : List Admin} {b : List Admin}
    (hab : sizeOf b < sizeOf a) : sizeOf b < sizeOf (vals V ++ [a] ++ xr) := by
  have := List.sizeOf_lt_of_mem (show a ∈ vals V ++ [a] ++ xr by simp)
  omega

/-- **Stuck host calls transport along the closure.** If the left code is stuck on a
host call, the right code runs to code stuck on the same call. -/
theorem stuck_transport {P : Profile} {BI : List Instr → List Instr → Prop}
    {B : List Admin → List Admin → Prop}
    (hB : BaseSim P (closedHost (H := H)) (FuncRel (H := H) BI) BI B) (hnr : NoRedexB H B) :
    ∀ (n : Nat) {s t : Store H} {f : Frame} {x y : List Admin}, sizeOf x < n →
      StoreRel (FuncRel BI) s t → AdminsRel BI (WithCuts B) x y →
      ∀ {E : Ctx} {a : Nat} {hh : H} {args : List Val}, decompose? s x = some (E, a, hh, args) →
      ∃ (t' : Store H) (f' : Frame) (y' : List Admin), Steps P closedHost ⟨t, f, y⟩ ⟨t', f', y'⟩ ∧
        ∃ E', decompose? t' y' = some (E', a, hh, args) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
  intro s t f x y hn hst hxy E a hh args hd
  have hsegs := AdminsRel.segs (fun _ _ h => Or.inl (hB.src h)) hxy
  have hna : x.all Admin.isVal = false := by
    by_contra hall
    obtain ⟨u, rfl⟩ := exists_vals_of_all (by simpa using hall)
    rw [SingleThreaded.decompose?_vals_nil] at hd
    cases hd
  obtain ⟨V, xs, ys, xr, yr, t₁, rfl, hseg, hact, hr, hrun, hst₁⟩ :=
    Closure.split_active hB.toBaseFacts hsegs hna [] hst (f := f)
  have hrun' : Steps P closedHost ⟨t, f, y⟩ ⟨t₁, f, vals V ++ ys ++ yr⟩ :=
    Closure.steps_congr hrun (by simp) (by simp)
  have hsz : ∀ (a' : Admin) {b' : List Admin}, sizeOf b' < sizeOf a' → a' ∈ xs →
      sizeOf b' < n := by
    intro a' b' hlt hmem
    have := List.sizeOf_lt_of_mem (show a' ∈ vals V ++ xs ++ xr by simp [hmem])
    omega
  cases hseg with
  | @one a₀ b₀ hab =>
    have ha₀ : a₀.val? = none := by simpa [Admin.isVal] using hact
    rw [show vals V ++ [a₀] ++ xr = vals V ++ a₀ :: xr by simp, decompose?_head ha₀] at hd
    -- the same head on the right: the redex is found there too
    have same : b₀ = a₀ → ∃ (t' : Store H) (f' : Frame) (y' : List Admin),
        Steps P closedHost ⟨t, f, y⟩ ⟨t', f', y'⟩ ∧
          ∃ E', decompose? t' y' = some (E', a, hh, args) := by
      intro hba
      obtain ⟨E₁, hE₁⟩ := decompHead_rest yr hd
      have h₁ : decompose? s (vals V ++ b₀ :: yr) = some (E₁, a, hh, args) := by
        rw [hba, decompose?_head ha₀]; exact hE₁
      obtain ⟨E', hE'⟩ := decompose?_storeRel hst₁ h₁
      exact ⟨t₁, f, _, hrun', E', by simpa using hE'⟩
    cases hab with
    | refl => exact same rfl
    | plain hi =>
      cases hi with
      | refl => exact same rfl
      | _ => simp [decompHead, Admin.isCallRef] at hd
    | @label m cont cont' bd bd' hc hb =>
      simp only [decompHead, Option.map_eq_some_iff] at hd
      obtain ⟨⟨E₀, a₀', h₀, args₀⟩, hb₀, heq⟩ := hd
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl, rfl, rfl⟩ := heq
      obtain ⟨t₂, f₂, y₂, hs₂, E', hE'⟩ :=
        ih (hsz (.label m cont bd) (b' := bd) (by simp) (by simp)) hst₁ hb hb₀ (f := f)
      refine ⟨t₂, f₂, vals V ++ [.label m cont' y₂] ++ yr, hrun'.trans ?_, ?_⟩
      · exact steps_ctx (steps_label hs₂ m _) V yr
      · rw [show vals V ++ [Admin.label m cont' y₂] ++ yr = vals V ++ .label m cont' y₂ :: yr by simp,
          decompose?_head rfl]
        simp [decompHead, hE']
    | @handler m cs bd bd' hb =>
      simp only [decompHead, Option.map_eq_some_iff] at hd
      obtain ⟨⟨E₀, a₀', h₀, args₀⟩, hb₀, heq⟩ := hd
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl, rfl, rfl⟩ := heq
      obtain ⟨t₂, f₂, y₂, hs₂, E', hE'⟩ :=
        ih (hsz (.handler m cs bd) (b' := bd) (by simp) (by simp)) hst₁ hb hb₀ (f := f)
      refine ⟨t₂, f₂, vals V ++ [.handler m cs y₂] ++ yr, hrun'.trans ?_, ?_⟩
      · exact steps_ctx (steps_handler hs₂ m cs) V yr
      · rw [show vals V ++ [Admin.handler m cs y₂] ++ yr = vals V ++ .handler m cs y₂ :: yr by simp,
          decompose?_head rfl]
        simp [decompHead, hE']
    | @frame m fi bd bd' hb =>
      simp only [decompHead, Option.map_eq_some_iff] at hd
      obtain ⟨⟨E₀, a₀', h₀, args₀⟩, hb₀, heq⟩ := hd
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl, rfl, rfl⟩ := heq
      obtain ⟨t₂, f₂, y₂, hs₂, E', hE'⟩ :=
        ih (hsz (.frame m fi bd) (b' := bd) (by simp) (by simp)) hst₁ hb hb₀ (f := fi)
      refine ⟨t₂, f, vals V ++ [.frame m f₂ y₂] ++ yr, hrun'.trans ?_, ?_⟩
      · exact steps_ctx (steps_frame hs₂ m f) V yr
      · rw [show vals V ++ [Admin.frame m f₂ y₂] ++ yr = vals V ++ .frame m f₂ y₂ :: yr by simp,
          decompose?_head rfl]
        simp [decompHead, hE']
  | base hb =>
    exfalso
    rcases hb with hb | ⟨us, ws, k, x', y', hk, rfl, rfl⟩
    · rw [hnr _ _ hb s V xr] at hd
      cases hd
    · rcases hk with rfl | ⟨a', rfl⟩
      · rw [show vals V ++ (vals us ++ [Admin.trap] ++ x') ++ xr =
          vals (V ++ us) ++ .trap :: (x' ++ xr) by simp,
          SingleThreaded.decompose?_vals_cons_none rfl (fun _ _ => SingleThreaded.decompHead_trap)]
          at hd
        cases hd
      · rw [show vals V ++ (vals us ++ throwing a' ++ x') ++ xr =
          vals (V ++ us ++ [.ref (.exn a')]) ++ .plain .throwRef :: (x' ++ xr) by
            simp [throwing, vals, Val.toAdmin],
          SingleThreaded.decompose?_vals_cons_none rfl
            (fun _ _ => SingleThreaded.decompHead_plain rfl)] at hd
        cases hd

/-! ## Runs -/

section Runs

variable {o : GrowKind → Nat → Nat → Nat → Bool} {BI : List Instr → List Instr → Prop}
  {B : List Admin → List Admin → Prop}
local notation "PD" => Profile.deterministic o

/-- Closed normal forms are unique. -/
theorem nf_unique {c x y : Config H} (hx : Steps PD closedHost c x)
    (hy : Steps PD closedHost c y) (hnx : ∀ z, ¬ Step PD closedHost x z)
    (hny : ∀ z, ¬ Step PD closedHost y z) : x = y :=
  SingleThreaded.nf_unique_of_join (fun ha hb => SingleThreaded.Det.DStep.join' ha hb) hx hy hnx hny

/-- **Runs of the right side are runs of the left side**: a result of the right
configuration is one of the left (with related stores), and divergence of the right is
divergence of the left. -/
theorem runs_back (hB : BaseSim PD (closedHost (H := H)) (FuncRel BI) BI B)
    (hnr : NoRedexB H B) {c d : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    (hcd : CfgRel (FuncRel BI) (AdminsRel BI B) c d) :
    (∀ y, Steps PD closedHost d y → y.Terminal →
      ∃ x, Steps PD closedHost c x ∧ x.code = y.code ∧ StoreRel (FuncRel BI) x.store y.store) ∧
    (Diverges PD closedHost d → Diverges PD closedHost c) := by
  have hhost : HostRespects (FuncRel BI) (closedHost (H := H)) :=
    closedHost_codeParametric.respects (fun f => FuncRel.refl f)
  obtain ⟨sim, -⟩ := closure_configSim (fun _ _ h => h) hhost hB
  have hcd' : CfgRel (FuncRel BI) (AdminsRel BI (WithCuts B)) c d :=
    hcd.mono fun _ _ => AdminsRel.mono fun _ _ => Or.inl
  by_cases hdiv : Diverges PD closedHost c
  · refine ⟨fun y hy hyT => ?_, fun _ => hdiv⟩
    exact absurd (closure_diverges_transport (fun _ _ h => h) hhost hB hcd hdiv)
      (Unwrap.nf_not_div_closed hy (InlR.terminal_no_step hyT))
  obtain ⟨x, hx, hnf⟩ : ∃ x, Steps PD closedHost c x ∧ ∀ z, ¬ Step PD closedHost x z := by
    by_contra hne
    simp only [not_exists, not_and, not_forall, not_not] at hne
    exact hdiv (InfiniteTrace.coinduct (fun x => Steps PD closedHost c x)
      (fun x hx => let ⟨y, hy⟩ := hne x hx; ⟨y, hy, hx.tail hy⟩) .refl)
  -- the right side reaches a normal form: the same result, or stuck as well
  have key : ∃ w, Steps PD closedHost d w ∧ (∀ z, ¬ Step PD closedHost w z) ∧
      (x.Terminal → w.code = x.code ∧ StoreRel (FuncRel BI) x.store w.store) ∧
      (¬ x.Terminal → ¬ w.Terminal) := by
    by_cases ht : x.Terminal
    · obtain ⟨r, hr⟩ := ht
      obtain ⟨w, hw, hwc, hst⟩ := closure_run_transport (fun _ _ h => h) hhost hB hcd hx hr
      exact ⟨w, hw, InlR.terminal_no_step ⟨r, hwc⟩, fun _ => ⟨by rw [hwc, hr], hst⟩,
        fun h => (h ⟨r, hr⟩).elim⟩
    · have hxo := Unwrap.preserves_closed hc hx
      obtain ⟨E, a, hh, args, hd⟩ :
          ∃ E a hh args, decompose? x.store x.code = some (E, a, hh, args) := by
        obtain ht' | ⟨c₁, hs⟩ := Config.progress (P := PD) SingleThreaded.divHost_ok hxo
        · exact (ht ht').elim
        rcases SingleThreaded.Step.split_host hs with hn | ⟨E, a, hh, args, hd, hret | -⟩
        · exact (hnf _ hn).elim
        · obtain ⟨s', r, hret, -⟩ := hret
          cases hret
        · exact ⟨E, a, hh, args, hd⟩
      obtain ⟨x', hx', hxx'⟩ := sim.toForwardSim.steps hx hcd'
      obtain ⟨t', f', y', hs', E', hE'⟩ := stuck_transport hB hnr (sizeOf x.code + 1)
        (Nat.lt_succ_self _) hxx'.store hxx'.code hd (f := x'.frame)
      refine ⟨⟨t', f', y'⟩, hx'.trans hs', ?_, fun h => (ht h).elim, fun _ => ?_⟩
      · intro z hz
        rw [SingleThreaded.decompose?_none_of_noRedex (SingleThreaded.Step.noRedex hz)] at hE'
        cases hE'
      · intro hT
        rw [InlS.decompose?_terminal (s := t') hT] at hE'
        cases hE'
  obtain ⟨w, hw, hwnf, hT, hNT⟩ := key
  refine ⟨fun y hy hyT => ?_, fun hd => absurd hd (Unwrap.nf_not_div_closed hw hwnf)⟩
  obtain rfl : y = w := nf_unique hy hw (InlR.terminal_no_step hyT) hwnf
  by_cases ht : x.Terminal
  · obtain ⟨hcode, hst⟩ := hT ht
    exact ⟨x, hx, hcode.symm, hst⟩
  · exact absurd hyT (hNT ht)

end Runs

/-! ## Sessions and modules -/

section Modules

variable {o : GrowKind → Nat → Nat → Nat → Bool} {BI : List Instr → List Instr → Prop}
  {B : List Admin → List Admin → Prop}
local notation "PD" => Profile.deterministic o

theorem invoke_rel {s t : Store H} (hst : StoreRel (FuncRel BI) s t) (a : Nat) (vs : List Val) :
    CfgRel (FuncRel BI) (AdminsRel BI B) (invoke s a vs) (invoke t a vs) := by
  refine ⟨hst, rfl, ?_⟩
  have hcode : (invoke s a vs).code = (invoke t a vs).code := by
    simp only [invoke, ← List.getElem?_map, hst.types]
  rw [hcode]
  exact AdminsRel.refl _

/-- **Sessions of the right store are sessions of the left store.** -/
theorem session_back (hB : BaseSim PD (closedHost (H := H)) (FuncRel BI) BI B)
    (hnr : NoRedexB H B) {mi : ModuleInst} {t : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (h : Session PD closedHost mi t script bs) :
    ∀ {s : Store H}, StoreOk s → StoreRel (FuncRel BI) s t → Session PD closedHost mi s script bs := by
  induction h with
  | nil => exact fun _ _ => .nil
  | stop h => exact fun _ hst => .stop fun a ha hok => h a ha (invokeOk_of_storeRel hst hok)
  | @done t x vs rest a c r bs ha hok run hr tail ih =>
    intro s hs hst
    have hokS := invokeOk_of_storeRel hst.symm hok
    obtain ⟨_, _, _, _, _, hcS⟩ := invoke_ok hs hokS
    obtain ⟨R1, -⟩ := runs_back hB hnr hcS (invoke_rel (B := B) hst a vs)
    obtain ⟨x', hx', hcode, hst'⟩ := R1 c run ⟨r, hr⟩
    exact .done ha hokS hx' (by rw [hcode, hr])
      (ih (SingleThreaded.ConfigOk.storeOk (Unwrap.preserves_closed hcS hx')) hst')
  | @diverge t x vs rest a ha hok hd =>
    intro s hs hst
    have hokS := invokeOk_of_storeRel hst.symm hok
    obtain ⟨_, _, _, _, _, hcS⟩ := invoke_ok hs hokS
    obtain ⟨-, R2⟩ := runs_back hB hnr hcS (invoke_rel (B := B) hst a vs)
    exact .diverge ha hokS (R2 hd)

/-- **The right module refines the left one**, given a `BaseSim` with the left module
on the left. -/
theorem exportRefines_back (hB : BaseSim PD (closedHost (H := H)) (FuncRel BI) BI B)
    (hnr : NoRedexB H B) {m m' : Module} (hrel : ModuleBodiesRel BI m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportRefines (fun b b' => b' = b) PD (closedHost (H := H)) m' m := by
  refine ⟨fun s xas c hs hI => ?_, fun s xas script hs bs hbs => ?_⟩
  · obtain ⟨c', hc', -⟩ := instantiate_bodiesRel hrel hm' hI
    exact ⟨c', hc'⟩
  · obtain ⟨c', hI', hcase⟩ := hbs
    obtain ⟨c, hI, hfr, hco, hst⟩ := instantiate_bodiesRel hrel.flip hm hI'
    have hst' : StoreRel (FuncRel BI) c.store c'.store := hst.symm.mono fun _ _ h => h.flip
    have hcd : CfgRel (FuncRel BI) (AdminsRel BI B) c c' :=
      ⟨hst', hfr, by rw [hco]; exact AdminsRel.refl _⟩
    have hc : ConfigOk c [] :=
      Instantiate.ok SingleThreaded.divHost_ok hs
        (Unwrap.instantiate_of_closed_unwrap SingleThreaded.divHost hI)
    obtain ⟨R1, R2⟩ := runs_back hB hnr hc hcd
    refine ⟨bs, ⟨c, hI, ?_⟩, SessionRel.refl (R := fun b b' => b' = b) (fun _ => rfl) bs⟩
    rcases hcase with ⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩
    · obtain ⟨x, hx, hxc, hstx⟩ := R1 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [hfr]
      exact session_back hB hnr h₃
        (SingleThreaded.ConfigOk.storeOk (Unwrap.preserves_closed hc hx)) hstx
    · obtain ⟨x, hx, hxc, -⟩ := R1 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R2 h₁, rfl⟩)

/-- **Export equivalence from one code simulation**, under the closed host: modules
with related bodies are export equivalent when the base relation has a `BaseSim` whose
runtime base pairs hold no host-call redex on the left. -/
theorem exportEquiv_of_baseSim (hB : BaseSim PD (closedHost (H := H)) (FuncRel BI) BI B)
    (hnr : NoRedexB H B) {m m' : Module} (hrel : ModuleBodiesRel BI m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportEquiv (· = ·) PD (closedHost (H := H)) m m' :=
  ⟨exportRefines_of_bodiesRel hB (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
    hrel hm hm', exportRefines_back hB hnr hrel hm hm'⟩

end Modules

end Silmaril.Wasm.Binaryen.CodeSimClosed
