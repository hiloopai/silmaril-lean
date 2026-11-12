module

public import Silmaril.Proofs.Wasm.Game.Linking.Split.GameSup

/-!
# Static linking, separation: typing along the split

Original module documentation:

# Typing facts for the split world (M3 step B, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3, step (B).

The direction `shared ⊆ interact` needs the split world to make progress whenever the shared
world does: a typed thread is never stuck (`statusP_ne_stuck`). This file collects what the
joint machine needs on top of `SingleThreaded.Soundness`:

* `fill_trap_reach`: a trap in a callout context bubbles to the top (no typing needed);
* `callout_args_typed`: the arguments of a typed callout are typed by the host function's
  parameters (from Core progress against a host that only diverges, on typed arguments);
* `vals_typed`: the values of a typed finished configuration are typed by its result types;
* `statusP_running_inv`, `statusP_returned_trap_inv` (now in
  `Silmaril.Proofs.Wasm.Game.Machine.Profile`): inversions of `statusP`;
* `ScalarInstance.WellFormed.of_funcs`, `ScalarInstance.WellFormed.init_typed`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Game.Linking.Split

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Proofs.Wasm.Game.Linking Silmaril.Wasm.Numerics

/-! ### Runs under contexts -/

theorem step_lift_instrs {P : Profile} {host : HostSemantics Nat} {s s' : Store Nat}
    {g g' : Frame} {pre : List Val} {is is' rest : List Admin}
    (h : Step P host ⟨s, g, is⟩ ⟨s', g', is'⟩) :
    Step P host ⟨s, g, vals pre ++ is ++ rest⟩ ⟨s', g', vals pre ++ is' ++ rest⟩ := by
  by_cases hne : pre ≠ [] ∨ rest ≠ []
  · exact Step.ctxtInstrs h hne
  · simp only [ne_eq, not_or, not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    simpa [vals] using h

/-- Host-free runs of active threads can be mapped along a step-preserving map of frames and
code. -/
theorem reach_map {P : Profile} (φ : Frame → List Admin → Frame × List Admin)
    (hφ : ∀ (s s' : Store Nat) F F' X X', Step P noHost ⟨s, F, X⟩ ⟨s', F', X'⟩ →
      Step P noHost ⟨s, (φ F X).1, (φ F X).2⟩ ⟨s', (φ F' X').1, (φ F' X').2⟩)
    {s s' : Store Nat} {F F' : Frame} {X X' : List Admin}
    (h : Reach P (s, .active F X) (s', .active F' X')) :
    Reach P (s, .active (φ F X).1 (φ F X).2) (s', .active (φ F' X').1 (φ F' X').2) := by
  let Φ : Store Nat × Thread → Store Nat × Thread := fun x =>
    match x.2 with
    | .active F X => (x.1, .active (φ F X).1 (φ F X).2)
    | t => (x.1, t)
  have hact : ∀ y, Reach P (s, .active F X) y → ∃ F X, y.2 = .active F X := by
    intro y hy
    induction hy with
    | refl => exact ⟨F, X, rfl⟩
    | tail _ hst _ =>
      obtain ⟨f', c', h1, -⟩ := hst
      exact ⟨f', c', h1⟩
  have key : ∀ x y, InternalP P x y → (∃ F X, x.2 = .active F X) → InternalP P (Φ x) (Φ y) := by
    rintro ⟨s₁, t₁⟩ ⟨s₂, t₂⟩ ⟨f', c', rfl, hst⟩ ⟨F₁, X₁, hx⟩
    simp only at hx
    subst hx
    exact ⟨_, _, rfl, hφ _ _ _ _ _ _ hst⟩
  have hgen : ∀ b, Reach P (s, .active F X) b → Reach P (Φ (s, .active F X)) (Φ b) := by
    intro b hb
    induction hb with
    | refl => exact .refl
    | tail hxy hyz ih => exact Relation.ReflTransGen.tail ih (key _ _ hyz (hact _ hxy))
  simpa [Φ] using hgen _ h

/-- **Trap bubbling.** A trap in a callout context reaches the top, with store and frame
unchanged. -/
theorem fill_trap_reach (P : Profile) (s : Store Nat) :
    ∀ (E : Ctx) (F : Frame), Reach P (s, .active F (E.fill [.trap])) (s, .active F [.trap]) := by
  have top : ∀ (F : Frame) (pre : List Val) (rest : List Admin),
      Reach P (s, .active F (vals pre ++ [.trap] ++ rest)) (s, .active F [.trap]) := by
    intro F pre rest
    by_cases hne : pre ≠ [] ∨ rest ≠ []
    · exact .single ⟨F, [.trap], rfl, Step.trapInstrs hne⟩
    · have hnil : pre = [] ∧ rest = [] := by simpa only [ne_eq, not_or, not_not] using hne
      rw [hnil.1, hnil.2]
      simpa [vals] using (Relation.ReflTransGen.refl : Reach P (s, .active F [.trap]) _)
  intro E
  induction E with
  | top pre rest => intro F; exact top F pre rest
  | label pre n cont E rest ih =>
    show ∀ F, Reach P (s, .active F ((Ctx.label pre n cont E rest).fill [.trap]))
      (s, .active F [.trap])
    intro F
    have h1 : Reach P (s, .active F (vals pre ++ [.label n cont (E.fill [.trap])] ++ rest))
        (s, .active F (vals pre ++ [.label n cont [.trap]] ++ rest)) :=
      reach_map (P := P) (fun g X => (g, vals pre ++ [.label n cont X] ++ rest))
      (fun _ _ _ _ _ _ h => step_lift_instrs (Step.ctxtLabel h)) (ih F)
    have h2 : InternalP P (s, .active F (vals pre ++ [.label n cont [.trap]] ++ rest))
        (s, .active F (vals pre ++ [.trap] ++ rest)) :=
      ⟨_, _, rfl, step_lift_instrs Step.trapLabel⟩
    exact (h1.tail h2).trans (top F pre rest)
  | handler pre n cs E rest ih =>
    show ∀ F, Reach P (s, .active F ((Ctx.handler pre n cs E rest).fill [.trap]))
      (s, .active F [.trap])
    intro F
    have h1 : Reach P (s, .active F (vals pre ++ [.handler n cs (E.fill [.trap])] ++ rest))
        (s, .active F (vals pre ++ [.handler n cs [.trap]] ++ rest)) :=
      reach_map (P := P) (fun g X => (g, vals pre ++ [.handler n cs X] ++ rest))
      (fun _ _ _ _ _ _ h => step_lift_instrs (Step.ctxtHandler h)) (ih F)
    have h2 : InternalP P (s, .active F (vals pre ++ [.handler n cs [.trap]] ++ rest))
        (s, .active F (vals pre ++ [.trap] ++ rest)) :=
      ⟨_, _, rfl, step_lift_instrs Step.trapHandler⟩
    exact (h1.tail h2).trans (top F pre rest)
  | frame pre n fi E rest ih =>
    show ∀ F, Reach P (s, .active F ((Ctx.frame pre n fi E rest).fill [.trap]))
      (s, .active F [.trap])
    intro F
    have h1 : Reach P (s, .active F (vals pre ++ [.frame n fi (E.fill [.trap])] ++ rest))
        (s, .active F (vals pre ++ [.frame n fi [.trap]] ++ rest)) :=
      reach_map (P := P) (fun g X => (F, vals pre ++ [.frame n g X] ++ rest))
      (fun _ _ _ _ _ _ h => step_lift_instrs (Step.ctxtFrame h)) (ih fi)
    have h2 : InternalP P (s, .active F (vals pre ++ [.frame n fi [.trap]] ++ rest))
        (s, .active F (vals pre ++ [.trap] ++ rest)) :=
      ⟨_, _, rfl, step_lift_instrs Step.trapFrame⟩
    exact (h1.tail h2).trans (top F pre rest)

/-! ### Typed callouts and results -/

/-- **Typed callouts.** The arguments of a callout of a typed thread are typed by the
parameters of some host function with the same code. -/
theorem callout_args_typed {P : Profile} {s : Store Nat} {t : Thread} {ts : List CValType}
    (ht : ThreadOk s t ts) {h : Nat} {args : List Val} (hco : CalloutAt s t h args) :
    ∃ (a : Nat) (fi : FuncInst Nat) (ps rs : Ty (.list .val)), s.funcs[a]? = some fi ∧
      fi.code = .host h ∧ Expand fi.type (.func ps rs) ∧ List.Forall₂ (ValOk s) args ps.toList := by
  let H₀ : HostSemantics Nat := fun h' s' vs out => out = .diverged ∧
    ∃ (a : Nat) (fi : FuncInst Nat) (ps rs : Ty (.list .val)), s'.funcs[a]? = some fi ∧
      fi.code = .host h' ∧ Expand fi.type (.func ps rs) ∧ List.Forall₂ (ValOk s') vs ps.toList
  have hok : HostOk H₀ := by
    intro s' fi h' vs ps rs _ hmem hcode hexp hvs
    obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hmem
    refine ⟨⟨.diverged, rfl, a, fi, ps, rs, ha, hcode, hexp, hvs⟩, fun out hout => ?_⟩
    rw [hout.1]
    trivial
  rcases Config.progress (P := P) hok ht with ⟨r, hr⟩ | ⟨c', hst⟩
  · exact absurd hco (resultAt_not_calloutAt (r := r) hr)
  obtain ⟨E, a, hd⟩ := hco
  rcases Step.split_host hst with hfree | ⟨E', a', hh, args', hd', hret⟩
  · have hnone : decompose? s (t.config s).code = none := by
      simpa only [Thread.config_store] using decompose?_none_of_noRedex (Step.noRedex hfree)
    exact absurd (hnone.symm.trans hd) (by simp)
  have hd'' : decompose? s (t.config s).code = some (E', a', hh, args') := by
    simpa only [Thread.config_store] using hd'
  obtain ⟨-, -, hhh, hargs⟩ : E' = E ∧ a' = a ∧ hh = h ∧ args' = args := by
    simpa only [Option.some.injEq, Prod.mk.injEq] using hd''.symm.trans hd
  rcases hret with ⟨s', r, ⟨hout, -⟩, -⟩ | ⟨⟨-, hw⟩, -⟩
  · cases hout
  have hw' : ∃ (a : Nat) (fi : FuncInst Nat) (ps rs : Ty (.list .val)),
      s.funcs[a]? = some fi ∧ fi.code = .host hh ∧ Expand fi.type (.func ps rs) ∧
        List.Forall₂ (ValOk s) args' ps.toList := by
    simpa only [Thread.config_store] using hw
  rw [← hhh, ← hargs]
  exact hw'

theorem forall₂_valOk_sub {s : Store Nat} {Δ : TypeCtx} :
    ∀ {vs : List Val} {ts' ts : List CValType}, List.Forall₂ (ValOk s) vs ts' →
      List.Forall₂ (Sub Δ) ts' ts →
      List.Forall₂ (fun v t => ∃ t₀, ValOk s v t₀ ∧ Relation.ReflTransGen (Sub Δ) t₀ t) vs ts
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h hs, .cons h' hs' =>
    .cons ⟨_, h, .single h'⟩ (forall₂_valOk_sub hs hs')

/-- The values of a typed finished configuration are typed by its (closed) result types. -/
theorem vals_typed {s : Store Nat} {f : Frame} {vs : List Val} {ts : List CValType}
    (h : ConfigOk ⟨s, f, vals vs⟩ ts) (hts : ∀ t ∈ ts, TyOk {} t) :
    List.Forall₂ (ValOk s) vs ts := by
  obtain ⟨C, hst, had⟩ := h
  have hΔ := CallRefDef.ok_of_emptyOk (StateOk.emptyOk hst)
  obtain ⟨ts', hv, hsub⟩ := AdminsOk.vals_inv hΔ had
  simp only [List.nil_append] at hsub
  have hcomb : List.Forall₂ (fun v t => ∃ t₀, ValOk s v t₀ ∧
      Relation.ReflTransGen (Sub C.toTypeCtx) t₀ t) vs ts :=
    forall₂_valOk_sub hv hsub
  exact StateOk.valsTo_valOk hst hcomb hts

/-! ### Well-formed instances -/

theorem _root_.Silmaril.Wasm.Game.ScalarInstance.WellFormed.of_funcs {I : ScalarInstance} {s s' : Store Nat}
    (hw : I.WellFormed s) (hs : StoreOk s') (hf : s'.funcs = s.funcs) : I.WellFormed s' where
  storeOk := hs
  addrs_length := hw.addrs_length
  export_type j := by rw [hf]; exact hw.export_type j
  host_type a fi h ha hc := hw.host_type a fi h (by rw [← hf]; exact ha) hc

theorem toList_toC (ts : List ScalarType) :
    (Ty.ofList (ts.map ScalarType.toC) : Ty (.list .val)).toList = ts.map ScalarType.toC :=
  Ty.toList_ofList _

theorem forall₂_valOk_of_hasVal {s : Store Nat} {ts : List ScalarType} {vs : List Val}
    (h : List.Forall₂ ScalarType.HasVal ts vs) :
    List.Forall₂ (ValOk s) vs (ts.map ScalarType.toC) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons ((ScalarType.hasVal_iff_valOk s _ _).mp h) ih

theorem forall₂_hasVal_of_valOk {s : Store Nat} {ts : List ScalarType} {vs : List Val}
    (h : List.Forall₂ (ValOk s) vs (ts.map ScalarType.toC)) :
    List.Forall₂ ScalarType.HasVal ts vs := by
  induction ts generalizing vs with
  | nil => cases h; exact .nil
  | cons t ts ih =>
    cases h with
    | cons hv hvs => exact .cons ((ScalarType.hasVal_iff_valOk s _ _).mpr hv) (ih hvs)

theorem scalar_tyOk (t : ScalarType) : TyOk {} t.toC := by
  cases t with
  | num n => exact .num n
  | v128 => exact .vec _
  | i31 n => exact .refv (ScalarType.i31_tyOk n)

/-- The initial thread of an export call of a well-formed instance is typed by the export's
results. -/
theorem _root_.Silmaril.Wasm.Game.ScalarInstance.WellFormed.init_typed {I : ScalarInstance} {s : Store Nat}
    (hw : I.WellFormed s) (f : I.F.Op) :
    ThreadOk s (I.initThread f) ((I.exports.get f.1).results.map ScalarType.toC) := by
  obtain ⟨fi, hfi, hexp⟩ := hw.export_type f.1
  have hinv : InvokeOk s (I.addr f.1) f.2.1 := by
    refine ⟨fi, _, _, hfi, hexp, ?_⟩
    rw [toList_toC]
    exact forall₂_valOk_of_hasVal f.2.2
  obtain ⟨fi', ps, rs, hfi', hexp', hok⟩ := invoke_ok hw.storeOk hinv
  rw [hfi] at hfi'
  cases hfi'
  have := Expand.func_eq hexp hexp'
  simp only [FnType.toComp, Ty.func.injEq] at this
  obtain ⟨-, hrs⟩ := this
  rw [← hrs, toList_toC] at hok
  exact hok

end Silmaril.Proofs.Wasm.Game.Linking.Split
