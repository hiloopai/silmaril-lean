module

public import Silmaril.Proofs.Wasm.Component.Reference.CalloutCore
public import Silmaril.Proofs.Wasm.Component.Reference.SEnvTyping
public import Silmaril.Proofs.Wasm.Component.Reference.FloatSound
public import Silmaril.Proofs.Wasm.Component.Reference.ImpIR
public import Silmaril.Wasm.Game.Adequacy.Thms
public import Silmaril.Wasm.Game.Machine.Thms
public import Silmaril.Wasm.SingleThreaded.Locality

/-!
# Segmented runs of the reference machine as plays of the core instance

The core instance `I` of a `SimpleI` component, from the reference engine's core store `cs`
with `Store.mapH trampIdx cs = I.store`. A segmented run answered by `g` (`ASeg`) is a path of the
instance's transition system (`SegRun.path'`), each callout an import question whose answer is
the lowered answer of `g` in the recorded host state, related to component import calls by
`ImpRel` and answered by `g` with the host state threaded (`HostRun`).

* `senvG c I g`: the stateful environment (`Silmaril.Wasm.Game.SEnv`, states those of `g`)
  answering each import question in state `s` as `g s` does after the lower adapter's argument
  lift, moving to the next state (`RespG`); every answered callout is one of its answers, and a
  segmented run is a product run against it (`aseg_rounds`, `SSteps`);
* `callout_typed`, `path_returnedAt`: by typing of the instance against `senvG`
  (`SEnvTyping.sstep_callout_typed`, `sanswer_of_run`), the callouts of a segmented run are
  typed import questions, and returned results typed answers;
* `fill_trap_reach'`: a trap resumed into a callout context reaches the top (trap bubbling,
  adapted from `Silmaril.Proofs.Wasm.Game.Linking.Split.Typed.fill_trap_reach`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload sigN)

variable {P : Profile} {σ : Type} {g : σ → Silmaril.Wasm.Component.Runtime.HostFuncId →
  List Silmaril.Wasm.Component.Value.Val → Option (List Silmaril.Wasm.Component.Value.Val × σ)}
  {c : SimpleI} {I : Silmaril.Wasm.Game.ScalarInstance}

/-! ## Typed questions -/

/-- **The export question** of the core instance of `m` for its export `k` on flat values of
the parameter types. -/
theorem typedCallI {m : ImpModule} (hI : m.IsInst I) {k : Nat} (hk : k < m.exports.length)
    {xs : List Flat} (hxs : xs.map (·.type) = m.exports[k].2.params) :
    ∃ f : I.F.Op, f.1.val = k ∧ f.2.1 = xs.map ofFlat ∧ I.exports.get f.1 = fnOf m.exports[k].2 := by
  have hlen : k < I.exports.length := by rw [hI.2.2, List.length_map]; exact hk
  have hj : I.exports.get ⟨k, hlen⟩ = fnOf m.exports[k].2 := by
    simp only [List.get_eq_getElem, hI.2.2, List.getElem_map]
  have hparams : (I.exports.get ⟨k, hlen⟩).params = xs.map fun x => .num x.type := by
    rw [hj]
    show m.exports[k].2.params.map _ = _
    rw [← hxs, List.map_map]
    rfl
  exact ⟨⟨⟨k, hlen⟩, ⟨xs.map ofFlat, hparams ▸ forall₂_hasVal_ofFlat xs⟩⟩, rfl, rfl, hj⟩

theorem ifaceOp?_some {ts : List Silmaril.Wasm.Game.FnType} {h : Nat} {args : List Execution.Core.Val}
    {e : (Silmaril.Wasm.Game.ifaceSig ts).Op} (he : Silmaril.Wasm.Game.ifaceOp? ts h args = some e) :
    e.1.val = h ∧ e.2.1 = args := by
  unfold Silmaril.Wasm.Game.ifaceOp? at he
  split_ifs at he with hlt ht
  cases he
  exact ⟨rfl, rfl⟩

/-! ## The stateful environment of `g` -/

/-- The core answer `w` to the import question `e` in host state `s` is the lowered answer of
`g` to the lifted arguments, moving to host state `s'`. -/
def RespG (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance)
    (g : σ → Silmaril.Wasm.Component.Runtime.HostFuncId →
      List Silmaril.Wasm.Component.Value.Val → Option (List Silmaril.Wasm.Component.Value.Val × σ))
    (s : σ) (e : I.E.Op) (w : I.E.Ar e) (s' : σ) : Prop :=
  ∃ (p : String × FuncTy) (ws us : List Silmaril.Wasm.Component.Val), c.imports[e.1.val]? = some p ∧
    liftArgs p.2.params (e.2.1.filterMap toFlat?) = some ws ∧
    g s ⟨e.1.val⟩ (ws.map toRefVal) = some (us.map toRefVal, s') ∧
    ValTy.checkList p.2.results us = true ∧
    Silmaril.Wasm.Game.Answer.toResult w = .values ((lowerArgs p.2.results us).map ofFlat)

/-- **The stateful environment of `g`**: in host state `s`, each import question is answered as
`g` answers the lifted arguments in `s`, lowered, moving to the next state (`RespG`); it never
diverges by choice (a question with no answer is silent). -/
def senvG (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance)
    (g : σ → Silmaril.Wasm.Component.Runtime.HostFuncId →
      List Silmaril.Wasm.Component.Value.Val → Option (List Silmaril.Wasm.Component.Value.Val × σ)) :
    Silmaril.Wasm.Game.SEnv I.E where
  S := σ
  Ans := RespG c I g
  Div _ _ := False

/-- The environment of `g` throws nothing. -/
theorem senvG_throwsBelow (n : Nat) : (senvG c I g).ThrowsBelow n := by
  intro q e w q' hw
  have hr : Silmaril.Wasm.Game.Answer.toResult w = _ :=
    (show RespG c I g q e w q' from hw).choose_spec.choose_spec.choose_spec.2.2.2.2
  cases w with
  | values _ => trivial
  | trap => cases hr
  | throw _ => cases hr

/-! ## Trap bubbling

Adapted from `Silmaril.Proofs.Wasm.Game.Linking.Split.Typed` (`step_lift_instrs`, `reach_map`,
`fill_trap_reach`), which this topic does not import; Core-level proofs unchanged. -/

theorem step_lift_instrs' {host : HostSemantics Nat} {s s' : Store Nat}
    {g g' : Frame} {pre : List Execution.Core.Val} {is is' rest : List Admin}
    (h : Execution.Core.Step P host ⟨s, g, is⟩ ⟨s', g', is'⟩) :
    Execution.Core.Step P host ⟨s, g, vals pre ++ is ++ rest⟩ ⟨s', g', vals pre ++ is' ++ rest⟩ := by
  by_cases hne : pre ≠ [] ∨ rest ≠ []
  · exact Silmaril.Games.Step.ctxtInstrs h hne
  · have hnil : pre = [] ∧ rest = [] := by simpa only [ne_eq, not_or, not_not] using hne
    rw [hnil.1, hnil.2]
    simpa [vals] using h

/-- Host-free runs of active threads can be mapped along a step-preserving map of frames and
code. -/
theorem reach_map' (φ : Frame → List Admin → Frame × List Admin)
    (hφ : ∀ (s s' : Store Nat) F F' X X',
      Execution.Core.Step P (fun _ _ _ _ => False) ⟨s, F, X⟩ ⟨s', F', X'⟩ →
      Execution.Core.Step P (fun _ _ _ _ => False) ⟨s, (φ F X).1, (φ F X).2⟩
        ⟨s', (φ F' X').1, (φ F' X').2⟩)
    {s s' : Store Nat} {F F' : Frame} {X X' : List Admin}
    (h : Silmaril.Wasm.Game.Reach P (s, .active F X) (s', .active F' X')) :
    Silmaril.Wasm.Game.Reach P (s, .active (φ F X).1 (φ F X).2) (s', .active (φ F' X').1 (φ F' X').2) := by
  let Φ : Store Nat × Thread → Store Nat × Thread := fun x =>
    match x.2 with
    | .active F X => (x.1, .active (φ F X).1 (φ F X).2)
    | t => (x.1, t)
  have hact : ∀ y, Silmaril.Wasm.Game.Reach P (s, .active F X) y → ∃ F X, y.2 = .active F X := by
    intro y hy
    induction hy with
    | refl => exact ⟨F, X, rfl⟩
    | tail _ hst _ =>
      obtain ⟨f', c', h1, -⟩ := hst
      exact ⟨f', c', h1⟩
  have key : ∀ x y, Silmaril.Wasm.Game.InternalP P x y → (∃ F X, x.2 = .active F X) →
      Silmaril.Wasm.Game.InternalP P (Φ x) (Φ y) := by
    rintro ⟨s₁, t₁⟩ ⟨s₂, t₂⟩ ⟨f', c', rfl, hst⟩ ⟨F₁, X₁, hx⟩
    have hx' : t₁ = .active F₁ X₁ := hx
    rw [hx'] at hst ⊢
    exact ⟨_, _, rfl, hφ _ _ _ _ _ _ hst⟩
  have hgen : ∀ b, Silmaril.Wasm.Game.Reach P (s, .active F X) b →
      Silmaril.Wasm.Game.Reach P (Φ (s, .active F X)) (Φ b) := by
    intro b hb
    induction hb with
    | refl => exact .refl
    | tail hxy hyz ih => exact Relation.ReflTransGen.tail ih (key _ _ hyz (hact _ hxy))
  simpa [Φ] using hgen _ h

/-- A trap at the top of the code with values before and code after reaches `[trap]`. -/
theorem trap_top_reach (s : Store Nat) (F : Frame) (pre : List Execution.Core.Val)
    (rest : List Admin) :
    Silmaril.Wasm.Game.Reach P (s, .active F (vals pre ++ [.trap] ++ rest)) (s, .active F [.trap]) := by
  by_cases hne : pre ≠ [] ∨ rest ≠ []
  · exact .single ⟨F, [.trap], rfl, Silmaril.Games.Step.trapInstrs hne⟩
  · have hnil : pre = [] ∧ rest = [] := by simpa only [ne_eq, not_or, not_not] using hne
    rw [hnil.1, hnil.2]
    simpa [vals] using (Relation.ReflTransGen.refl : Silmaril.Wasm.Game.Reach P (s, .active F [.trap]) _)

/-- **Trap bubbling**: a trap in a callout context reaches the top, with store and frame
unchanged. -/
theorem fill_trap_reach' (s : Store Nat) :
    ∀ (E : Ctx) (F : Frame),
      Silmaril.Wasm.Game.Reach P (s, .active F (E.fill [.trap])) (s, .active F [.trap]) := by
  intro E
  induction E with
  | top pre rest => intro F; exact trap_top_reach s F pre rest
  | label pre n cont E rest ih =>
    show ∀ F, Silmaril.Wasm.Game.Reach P (s, .active F ((Ctx.label pre n cont E rest).fill [.trap]))
      (s, .active F [.trap])
    intro F
    have h1 : Silmaril.Wasm.Game.Reach P (s, .active F (vals pre ++ [.label n cont (E.fill [.trap])] ++ rest))
        (s, .active F (vals pre ++ [.label n cont [.trap]] ++ rest)) :=
      reach_map' (fun g X => (g, vals pre ++ [.label n cont X] ++ rest))
        (fun _ _ _ _ _ _ h => step_lift_instrs' (Silmaril.Games.Step.ctxtLabel h)) (ih F)
    have h2 : Silmaril.Wasm.Game.InternalP P (s, .active F (vals pre ++ [.label n cont [.trap]] ++ rest))
        (s, .active F (vals pre ++ [.trap] ++ rest)) :=
      ⟨_, _, rfl, step_lift_instrs' Silmaril.Games.Step.trapLabel⟩
    exact (h1.tail h2).trans (trap_top_reach s F pre rest)
  | handler pre n cs E rest ih =>
    show ∀ F, Silmaril.Wasm.Game.Reach P (s, .active F ((Ctx.handler pre n cs E rest).fill [.trap]))
      (s, .active F [.trap])
    intro F
    have h1 : Silmaril.Wasm.Game.Reach P (s, .active F (vals pre ++ [.handler n cs (E.fill [.trap])] ++ rest))
        (s, .active F (vals pre ++ [.handler n cs [.trap]] ++ rest)) :=
      reach_map' (fun g X => (g, vals pre ++ [.handler n cs X] ++ rest))
        (fun _ _ _ _ _ _ h => step_lift_instrs' (Silmaril.Games.Step.ctxtHandler h)) (ih F)
    have h2 : Silmaril.Wasm.Game.InternalP P (s, .active F (vals pre ++ [.handler n cs [.trap]] ++ rest))
        (s, .active F (vals pre ++ [.trap] ++ rest)) :=
      ⟨_, _, rfl, step_lift_instrs' Silmaril.Games.Step.trapHandler⟩
    exact (h1.tail h2).trans (trap_top_reach s F pre rest)
  | frame pre n fi E rest ih =>
    show ∀ F, Silmaril.Wasm.Game.Reach P (s, .active F ((Ctx.frame pre n fi E rest).fill [.trap]))
      (s, .active F [.trap])
    intro F
    have h1 : Silmaril.Wasm.Game.Reach P (s, .active F (vals pre ++ [.frame n fi (E.fill [.trap])] ++ rest))
        (s, .active F (vals pre ++ [.frame n fi [.trap]] ++ rest)) :=
      reach_map' (fun g X => (F, vals pre ++ [.frame n g X] ++ rest))
        (fun _ _ _ _ _ _ h => step_lift_instrs' (Silmaril.Games.Step.ctxtFrame h)) (ih fi)
    have h2 : Silmaril.Wasm.Game.InternalP P (s, .active F (vals pre ++ [.frame n fi [.trap]] ++ rest))
        (s, .active F (vals pre ++ [.trap] ++ rest)) :=
      ⟨_, _, rfl, step_lift_instrs' Silmaril.Games.Step.trapFrame⟩
    exact (h1.tail h2).trans (trap_top_reach s F pre rest)

/-! ## Typing under the stateful environment of `g` -/

/-- **Typed callouts**: a callout reached by a product run of an export call against the
stateful environment of `g` is a typed import question (`SEnvTyping.sstep_callout_typed`). -/
theorem callout_typed {s : Store Nat} (hw : I.WellFormed s) {f : I.F.Op} {c' : Config Nat}
    {q q' : σ}
    (run : Silmaril.Wasm.Game.SSteps P (senvG c I g) (invoke s (I.addr f.1) f.2.1, q) (c', q'))
    {E : Ctx} {a h : Nat} {args : List Execution.Core.Val}
    (hd : decompose? c'.store c'.code = some (E, a, h, args)) :
    ∃ e, I.importOp? h args = some e :=
  SEnvTyping.sstep_callout_typed hw (senvG_throwsBelow _) run hd

theorem filterMap_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l.filterMap f = l'
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    exact h ▸ rfl
  | x :: xs, l', h => by
    rcases hx : f x with _ | y
    · simp [List.mapM_cons, hx] at h
    rcases hxs : xs.mapM f with _ | ys
    · simp [List.mapM_cons, hx, hxs] at h
    have hl' : l' = y :: ys := by
      simp only [List.mapM_cons, hx, hxs, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Option.some.injEq] at h
      exact h.symm
    rw [List.filterMap_cons, hx, hl', filterMap_of_mapM hxs]

/-- The sites of the `canon lower` trampolines of `c`: trampoline `k` lowers component
function `k`, the host function `k`, at the type of import `k`. -/
def SiteI (c : SimpleI) (L : LowerSite P) : Prop :=
  ∃ (k : Nat) (hk : k < c.imports.length), L.f = ⟨k⟩ ∧ L.fn = ⟨k⟩ ∧ L.p = c.imports[k].2

/-- A recorded callout of the reference run (with the host states around it) and a round of the
instance: the import question of the callout, answered with the core result of its resumption,
as `g` answers in the recorded state. -/
def RoundOf (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance)
    (g : σ → Silmaril.Wasm.Component.Runtime.HostFuncId →
      List Silmaril.Wasm.Component.Value.Val → Option (List Silmaril.Wasm.Component.Value.Val × σ))
    (cl : σ × CallRec × σ) (r : Round I.E) : Prop :=
  I.importOp? cl.2.1.1 cl.2.1.2.1 = some r.1 ∧ Silmaril.Wasm.Game.Answer.toResult r.2 = cl.2.1.2.2 ∧
    RespG c I g cl.1 r.1 r.2 cl.2.2

/-- The import types of the core instance are the flattened component import types. -/
theorem imports_get (hc : c.Good) (hI : c.mod.IsInst I) (e : I.E.Op) (k : Nat)
    (hk : k < c.imports.length) (he : e.1.val = k) :
    I.imports.get e.1 = fnOf c.imports[k].2.flat := by
  have h₁ : I.imports = c.imports.map fun p => fnOf p.2.flat := by
    rw [hI.2.1, hc.imports, List.map_map]
    rfl
  have h₂ : I.imports[e.1.val]'e.1.isLt = (c.imports.map fun p => fnOf p.2.flat)[k]'(by
      rw [List.length_map]; exact hk) := by
    simp only [h₁, he]
  rw [List.get_eq_getElem, h₂, List.getElem_map]

/-- Host-free runs of the machine are product runs, the host state unchanged. -/
theorem reach_ssteps {L : Silmaril.Wasm.Game.SEnv I.E} {s s' : Store Nat} {t t' : Thread} {q : L.S}
    (h : Silmaril.Wasm.Game.Reach P (s, t) (s', t')) :
    Silmaril.Wasm.Game.SSteps P L (t.config s, q) (t'.config s', q) := by
  have key : ∀ {c c' : Config Nat}, Execution.Core.Steps P (fun _ _ _ _ => False) c c' →
      Silmaril.Wasm.Game.SSteps P L (c, q) (c', q) := by
    intro c c' hs
    induction hs with
    | refl => exact .refl
    | tail _ hst ih => exact ih.tail (.internal hst)
  exact key (Silmaril.Wasm.Game.Reach.steps h)

/-- The resumption of a callout with a Core result is the callout context filled with it. -/
theorem resumeResult_config {s : Store Nat} {t : Thread} {E : Ctx} {a h : Nat}
    {args : List Execution.Core.Val}
    (hd : decompose? (t.config s).store (t.config s).code = some (E, a, h, args)) (r : Result) :
    (resumeResult s t r).config s =
      ⟨(t.config s).store, (t.config s).frame, E.fill r.toAdmin⟩ := by
  have hd' : decompose? s (t.config s).code = some (E, a, h, args) := by
    rw [Thread.config_store] at hd
    exact hd
  simp only [resumeResult, hd', Thread.config_store]
  rfl

/-- **One answered callout** of the reference run is a round of the instance: the typed import
question of the callout, answered by the stateful environment of `g` with the lowered answer,
one product step. -/
theorem round_of_callout (hc : c.Good) (hI : c.mod.IsInst I) {s₀ : Store Nat} (hw : I.WellFormed s₀)
    {f : I.F.Op} {s : Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P))} {t : Thread}
    {L : LowerSite P} {ys flat : List Flat} {E : Ctx} {a : Nat} {q q₀ q' : σ}
    {args : List Execution.Core.Val}
    (pre : Silmaril.Wasm.Game.SSteps P (senvG c I g) (invoke s₀ (I.addr f.1) f.2.1, q₀)
      (t.config (Store.mapH trampIdx s), q))
    (hs : (E3 P).status s t = .callout L.host ys) (hq : SiteI c L) (ha : L.Answers g q ys flat q')
    (hd : decompose? s (t.config s).code = some (E, a, L.host, args)) :
    ∃ r : Round I.E, RoundOf c I g (q, (L.f.idx, args, .values (flat.map ofFlat)), q') r ∧
      Silmaril.Wasm.Game.SStep P (senvG c I g) (t.config (Store.mapH trampIdx s), q)
        (((E3 P).resume s t (.values flat)).config (Store.mapH trampIdx s), q') := by
  have hdm : decompose? (Store.mapH trampIdx s) (t.config (Store.mapH trampIdx s)).code =
      some (E, a, L.f.idx, args) := by
    rw [decompose?_config_mapH, hd]
    rfl
  have hdm' : decompose? (t.config (Store.mapH trampIdx s)).store
      (t.config (Store.mapH trampIdx s)).code = some (E, a, L.f.idx, args) := by
    rw [Thread.config_store]
    exact hdm
  obtain ⟨e, he⟩ := callout_typed hw pre hdm'
  obtain ⟨k, hk, hf, hfn, hp⟩ := hq
  have hek : e.1.val = k ∧ e.2.1 = args := by
    have h' := ifaceOp?_some he
    rw [hf] at h'
    exact h'
  have hys : args.filterMap toFlat? = ys := by
    obtain ⟨E', a', args', hd', hm⟩ := status_callout_redex hs
    have hargs : args' = args := by
      have e' := hd'.symm.trans hd
      simp only [Option.some.injEq, Prod.mk.injEq] at e'
      exact e'.2.2.2
    exact filterMap_of_mapM (hargs ▸ hm)
  obtain ⟨ws, us, hws, hg, hus, rfl⟩ := ha
  have hty : (lowerArgs L.p.results us).map (·.type) = ValTy.flatList c.imports[k].2.results := by
    rw [← hp]
    exact lowerList_types _ _ hus
  have hres : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (I.imports.get e.1).results
      ((lowerArgs L.p.results us).map ofFlat) := by
    have heq : (fnOf c.imports[k].2.flat).results =
        (lowerArgs L.p.results us).map (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) := by
      show (ValTy.flatList c.imports[k].2.results).map _ = _
      rw [← hty, List.map_map]
      rfl
    rw [imports_get hc hI e k hk hek.1, heq]
    exact forall₂_hasVal_ofFlat _
  let w : I.E.Ar e := .values ⟨(lowerArgs L.p.results us).map ofFlat, hres⟩
  have hresp : RespG c I g q e w q' := by
    refine ⟨c.imports[k], ws, us, by rw [hek.1]; exact List.getElem?_eq_getElem hk, ?_, ?_,
      hp ▸ hus, ?_⟩
    · rw [hek.2, hys, ← hp]
      exact hws
    · rw [hek.1, ← hfn]
      exact hg
    · rw [← hp]
      rfl
  have hstep := Silmaril.Wasm.Game.SStep.answer (P := P) (L := senvG c I g) (q := q) (q' := q') hdm' he
    hresp
  have hrv : (E3 P).resume s t (.values (lowerArgs L.p.results us)) =
      resumeResult s t (Silmaril.Wasm.Game.Answer.toResult w) := resume_values s t _
  rw [hrv, ← resumeResult_mapH, resumeResult_config hdm']
  exact ⟨⟨e, w⟩, ⟨he, rfl, hresp⟩, hstep⟩

/-- **A segmented run answered by `g` is a product run against the stateful environment of
`g`**, and its callouts are rounds of the instance. -/
theorem aseg_rounds (hc : c.Good) (hI : c.mod.IsInst I) {s₀ : Store Nat} (hw : I.WellFormed s₀)
    {f : I.F.Op} {B : Silmaril.Wasm.Component.Runtime.CStore (E3 P)}
    {th : Option Silmaril.Wasm.Component.Runtime.ThreadId} {q q' q₀ : σ}
    {x z : CoreSt (E3 P)} {calls : List (σ × CallRec × σ)}
    (hs : ASeg g (SiteI c) B th q x calls q' z) :
    Silmaril.Wasm.Game.SSteps P (senvG c I g) (invoke s₀ (I.addr f.1) f.2.1, q₀)
        (x.2.config (Store.mapH trampIdx x.1), q) →
      ∃ rounds : List (Round I.E), List.Forall₂ (RoundOf c I g) calls rounds ∧
        Silmaril.Wasm.Game.SSteps P (senvG c I g) (invoke s₀ (I.addr f.1) f.2.1, q₀)
          (z.2.config (Store.mapH trampIdx z.1), q') := by
  induction hs with
  | done hy =>
    intro pre
    exact ⟨[], .nil, pre.trans (reach_ssteps (reach_mapH trampIdx (coreSteps_internalP hy)))⟩
  | call hy hst hq _ ha hd _ ih =>
    intro pre
    have pre' := pre.trans (reach_ssteps (reach_mapH trampIdx (coreSteps_internalP hy)))
    obtain ⟨r, hr, hstep⟩ := round_of_callout hc hI hw pre' hst hq ha hd
    obtain ⟨rounds, hrs, post⟩ := ih (pre'.tail hstep)
    exact ⟨r :: rounds, .cons hr hrs, post⟩

/-- **A segmented run is a path of the instance** before any continuation that starts with a
host-free run from its end. -/
theorem SegRun.path' {H : Type} (gh : H → Nat) {f : I.F.Op} {s s' : Store H} {t t' : Thread}
    {calls : List (Nat × List Execution.Core.Val × Result)} (hrun : SegRun gh P s t calls s' t') :
    ∀ {cs : List (Round I.E)}, List.Forall₂ (fun (c : Nat × List Execution.Core.Val × Result) x =>
        I.importOp? c.1 c.2.1 = some x.1 ∧ Silmaril.Wasm.Game.Answer.toResult x.2 = c.2.2) calls cs →
      ∀ {rest : List (Move I.E I.F)} {q : I.HState},
        (∀ s₀ t₀, Silmaril.Wasm.Game.Reach P (s₀, t₀) (Store.mapH gh s', t') →
          I.Path P (.running f s₀ t₀) rest q) →
        I.Path P (.running f (Store.mapH gh s) t) (callMoves cs ++ rest) q := by
  induction hrun with
  | done run =>
    intro cs hcs rest q hk
    cases hcs
    exact hk _ _ (reach_mapH gh run)
  | @call s₀ s₁ s' t₀ t₁ t' E a h args r rest₀ run hd _ ih =>
    intro cs hcs rest q hk
    cases hcs with
    | @cons _ x _ cs' hx hcs' =>
      have hco : Silmaril.Wasm.Game.CalloutAt (Store.mapH gh s₁) t₁ (gh h) args :=
        ⟨E, a, by rw [decompose?_config_mapH, hd]; rfl⟩
      have ih' : I.Path P (.running f (Store.mapH gh s₁)
          (resumeResult (Store.mapH gh s₁) t₁ (Silmaril.Wasm.Game.Answer.toResult x.2)))
          (callMoves cs' ++ rest) q := by
        rw [resumeResult_mapH, hx.2]
        exact ih hcs' hk
      exact .cons (.ucall (reach_mapH gh run) hco hx.1) (.cons (.uret _) ih')

/-- `callMoves` of an appended round. -/
theorem callMoves_append {E F : Silmaril.Games.Sig.{0}} (l : List (Σ m : E.Op, E.Ar m))
    (x : Σ m : E.Op, E.Ar m) :
    (callMoves (F := F) (l ++ [x])) = callMoves l ++ [.inl (.ask x.1), .inl (.ans x.1 x.2)] := by
  induction l with
  | nil => rfl
  | cons y l ih => simp only [List.cons_append, callMoves, ih]

/-! ## Plays of the instance -/

/-- The data of an export call of the core instance: the reference engine's core store `cs`
renames to the instance's, and the export question `f` invokes address `a` on the lowered
arguments `xs`. -/
structure CallStart (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (E3 P).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P))) (f : I.F.Op) (a : Nat)
    (xs : List Flat) : Prop where
  good : c.Good
  inst : c.mod.IsInst I
  store : Store.mapH trampIdx cs = I.store
  addr : I.addr f.1 = a
  args : f.2.1 = xs.map ofFlat

theorem CallStart.wf {cs : (E3 P).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P))}
    {f : I.F.Op} {a : Nat} {xs : List Flat} (C : CallStart c I cs f a xs) : I.WellFormed I.store :=
  C.inst.1.choose_spec.ok

/-- The start of the run against the stateful environment of `g`. -/
theorem CallStart.pre {cs : (E3 P).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P))}
    {f : I.F.Op} {a : Nat} {xs : List Flat} (C : CallStart c I cs f a xs) (q : σ) :
    Silmaril.Wasm.Game.SSteps P (senvG c I g) (invoke I.store (I.addr f.1) f.2.1, q)
      ((Thread.invokeFlat a xs).config (Store.mapH trampIdx cs), q) := by
  rw [C.store, C.addr, C.args]
  exact .refl

/-- The export question, then a path from the invocation. -/
theorem CallStart.path {cs : (E3 P).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P))}
    {f : I.F.Op} {a : Nat} {xs : List Flat} (C : CallStart c I cs f a xs)
    {rest : List (Move I.E I.F)} {q : I.HState}
    (h : I.Path P (.running f (Store.mapH trampIdx cs) (Thread.invokeFlat a xs)) rest q) :
    I.Path P (.idle I.store) (.inr (.ask f) :: rest) q := by
  have hi : I.initThread f = Thread.invokeFlat a xs := by
    show Thread.pending (I.addr f.1) f.2.1 = _
    rw [C.addr, C.args]
    rfl
  rw [C.store] at h
  exact .cons (.call I.store f) (hi ▸ h)

/-- The data of an export call of the core instance at a later store `s`: the reference
engine's core store `cs` renames to `s`, which is well formed, and the export question `f`
invokes address `a` on the lowered arguments `xs`. -/
structure CallStartAt (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance) (s : Store Nat)
    (cs : (E3 P).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P))) (f : I.F.Op) (a : Nat)
    (xs : List Flat) : Prop where
  good : c.Good
  inst : c.mod.IsInst I
  store : Store.mapH trampIdx cs = s
  wf : I.WellFormed s
  addr : I.addr f.1 = a
  args : f.2.1 = xs.map ofFlat

theorem CallStart.toAt {cs : (E3 P).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P))}
    {f : I.F.Op} {a : Nat} {xs : List Flat} (C : CallStart c I cs f a xs) :
    CallStartAt c I I.store cs f a xs :=
  ⟨C.good, C.inst, C.store, C.wf, C.addr, C.args⟩

/-- The start of the run against the stateful environment of `g`, at a later store. -/
theorem CallStartAt.pre {s : Store Nat}
    {cs : (E3 P).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P))}
    {f : I.F.Op} {a : Nat} {xs : List Flat} (C : CallStartAt c I s cs f a xs) (q : σ) :
    Silmaril.Wasm.Game.SSteps P (senvG c I g) (invoke s (I.addr f.1) f.2.1, q)
      ((Thread.invokeFlat a xs).config (Store.mapH trampIdx cs), q) := by
  rw [C.store, C.addr, C.args]
  exact .refl

/-- The export question at a later store, then a path from the invocation. -/
theorem CallStartAt.path {s : Store Nat}
    {cs : (E3 P).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P))}
    {f : I.F.Op} {a : Nat} {xs : List Flat} (C : CallStartAt c I s cs f a xs)
    {rest : List (Move I.E I.F)} {q : I.HState}
    (h : I.Path P (.running f (Store.mapH trampIdx cs) (Thread.invokeFlat a xs)) rest q) :
    I.Path P (.idle s) (.inr (.ask f) :: rest) q := by
  have hi : I.initThread f = Thread.invokeFlat a xs := by
    show Thread.pending (I.addr f.1) f.2.1 = _
    rw [C.addr, C.args]
    rfl
  rw [C.store] at h
  exact .cons (.call s f) (hi ▸ h)

/-- The rounds of a segmented run as the hypothesis of `SegRun.path'`. -/
theorem rounds_forall₂ {calls : List (σ × CallRec × σ)}
    {rounds : List (Round I.E)} (h : List.Forall₂ (RoundOf c I g) calls rounds) :
    List.Forall₂ (fun (c : Nat × List Execution.Core.Val × Result) x =>
      I.importOp? c.1 c.2.1 = some x.1 ∧ Silmaril.Wasm.Game.Answer.toResult x.2 = c.2.2)
      (calls.map (·.2.1)) rounds :=
  List.forall₂_map_left_iff.mpr (h.imp fun _ _ h => ⟨h.1, h.2.1⟩)

/-- **A returned activation is a play** at a later store: the export question, the rounds of the callouts, and
the typed answer of the returned values. -/
theorem path_returnedAt {s : Store Nat} {cs : (E3 P).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P))}
    {f : I.F.Op} {a : Nat} {xs : List Flat} (C : CallStartAt c I s cs f a xs)
    {B : Silmaril.Wasm.Component.Runtime.CStore (E3 P)}
    {th : Option Silmaril.Wasm.Component.Runtime.ThreadId}
    {ys' : Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P))} {yt : Thread}
    {calls : List (σ × CallRec × σ)} {q q' : σ}
    (hs : ASeg g (SiteI c) B th q (cs, Thread.invokeFlat a xs) calls q' (ys', yt)) (r : Result)
    (hr : (yt.config ys').code = r.toAdmin) :
    ∃ (rounds : List (Round I.E)) (w : I.F.Ar f),
      List.Forall₂ (RoundOf c I g) calls rounds ∧
      I.Path P (.idle s) (.inr (.ask f) :: callMoves rounds ++ [.inr (.ans f w)])
        (.idle (Store.mapH trampIdx ys')) ∧
      Silmaril.Wasm.Game.Answer.ofResult? (I.exports.get f.1) r = some w := by
  obtain ⟨rounds, hrs, post⟩ := aseg_rounds C.good C.inst C.wf (f := f) hs (C.pre q)
  have final : (yt.config (Store.mapH trampIdx ys')).code = r.toAdmin := by
    rw [config_mapH]
    exact hr
  obtain ⟨w, hw, -⟩ := Silmaril.Wasm.Game.ScalarInstance.sanswer_of_run C.wf (senvG_throwsBelow _)
    post final
  have hpath : I.Path P (.running f (Store.mapH trampIdx cs) (Thread.invokeFlat a xs))
      (callMoves rounds ++ [.inr (.ans f w)]) (.idle (Store.mapH trampIdx ys')) :=
    SegRun.path' trampIdx hs.segRun (rounds_forall₂ hrs)
      (fun _ _ hr' => .cons (.oret hr' final hw) (.nil _))
  exact ⟨rounds, w, hrs, C.path hpath, hw⟩

/-- **A returned activation is a play**: the export question, the rounds of the callouts, and
the typed answer of the returned values. -/
theorem path_returned {cs : (E3 P).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P))}
    {f : I.F.Op} {a : Nat} {xs : List Flat} (C : CallStart c I cs f a xs)
    {B : Silmaril.Wasm.Component.Runtime.CStore (E3 P)}
    {th : Option Silmaril.Wasm.Component.Runtime.ThreadId}
    {ys' : Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P))} {yt : Thread}
    {calls : List (σ × CallRec × σ)} {q q' : σ}
    (hs : ASeg g (SiteI c) B th q (cs, Thread.invokeFlat a xs) calls q' (ys', yt)) (r : Result)
    (hr : (yt.config ys').code = r.toAdmin) :
    ∃ (rounds : List (Round I.E)) (w : I.F.Ar f) (q : I.HState),
      List.Forall₂ (RoundOf c I g) calls rounds ∧
      I.Path P (.idle I.store) (.inr (.ask f) :: callMoves rounds ++ [.inr (.ans f w)]) q ∧
      Silmaril.Wasm.Game.Answer.ofResult? (I.exports.get f.1) r = some w := by
  obtain ⟨rounds, w, hrs, hpath, hw⟩ := path_returnedAt C.toAt hs r hr
  exact ⟨rounds, w, _, hrs, hpath, hw⟩

/-- **A failing callout is a play** at a later store: the export question, the rounds of the earlier callouts,
the typed import question of the failing callout answered with a trap, and the trap. -/
theorem path_callout_trapAt {s : Store Nat} {cs : (E3 P).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P))}
    {f : I.F.Op} {a : Nat} {xs : List Flat} (C : CallStartAt c I s cs f a xs)
    {B : Silmaril.Wasm.Component.Runtime.CStore (E3 P)}
    {th : Option Silmaril.Wasm.Component.Runtime.ThreadId}
    {ys' : Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P))} {yt : Thread}
    {calls : List (σ × CallRec × σ)} {q q' : σ}
    (hs : ASeg g (SiteI c) B th q (cs, Thread.invokeFlat a xs) calls q' (ys', yt)) {E : Ctx} {a' h : Nat}
    {args : List Execution.Core.Val}
    (hd' : decompose? (yt.config (Store.mapH trampIdx ys')).store (yt.config (Store.mapH trampIdx ys')).code =
      some (E, a', h, args)) :
    ∃ (rounds : List (Round I.E)) (e : I.E.Op) (q : I.HState),
      List.Forall₂ (RoundOf c I g) calls rounds ∧ I.importOp? h args = some e ∧
      I.Path P (.idle s) (.inr (.ask f) :: callMoves (rounds ++ [⟨e, .trap⟩]) ++
        [.inr (.ans f .trap)]) q := by
  obtain ⟨rounds, hrs, post⟩ := aseg_rounds C.good C.inst C.wf (f := f) hs (C.pre q)
  have hd : decompose? (Store.mapH trampIdx ys') (yt.config (Store.mapH trampIdx ys')).code =
      some (E, a', h, args) := by
    rw [Thread.config_store] at hd'
    exact hd'
  obtain ⟨e, he⟩ := callout_typed C.wf post hd'
  have hres : resumeResult (Store.mapH trampIdx ys') yt (Silmaril.Wasm.Game.Answer.toResult
      (ft := I.imports.get e.1) .trap) =
      .active (yt.config (Store.mapH trampIdx ys')).frame (E.fill [.trap]) := by
    simp only [resumeResult, hd, Silmaril.Wasm.Game.Answer.toResult, Result.toAdmin]
  have htrap : ∀ s₁ t₀, Silmaril.Wasm.Game.Reach P (s₁, t₀) (Store.mapH trampIdx ys', yt) →
      I.Path P (.running f s₁ t₀) [.inl (.ask e), .inl (.ans e .trap), .inr (.ans f .trap)]
        (.idle (Store.mapH trampIdx ys')) := by
    intro s₁ t₀ hr
    have hb := fill_trap_reach' (P := P) (Store.mapH trampIdx ys') E
      (yt.config (Store.mapH trampIdx ys')).frame
    refine .cons (.ucall hr ⟨E, a', hd⟩ he) (.cons (.uret _) ?_)
    rw [hres]
    have hfin : Silmaril.Wasm.Game.ResultAt (Store.mapH trampIdx ys')
        (.active (yt.config (Store.mapH trampIdx ys')).frame [.trap]) .trap := rfl
    exact .cons (.oret hb hfin rfl) (.nil _)
  have hpath := SegRun.path' trampIdx hs.segRun (rounds_forall₂ hrs) htrap
  have hmoves : (.inr (.ask f) :: callMoves (rounds ++ [⟨e, .trap⟩]) ++ [.inr (.ans f .trap)] :
      List (Move I.E I.F)) = .inr (.ask f) :: (callMoves rounds ++
        [.inl (.ask e), .inl (.ans e .trap), .inr (.ans f .trap)]) := by
    rw [callMoves_append, List.cons_append, List.append_assoc]
    rfl
  exact ⟨rounds, e, _, hrs, he, hmoves ▸ C.path hpath⟩

/-- **A failing callout is a play**: the export question, the rounds of the earlier callouts,
the typed import question of the failing callout answered with a trap, and the trap. -/
theorem path_callout_trap {cs : (E3 P).Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P))}
    {f : I.F.Op} {a : Nat} {xs : List Flat} (C : CallStart c I cs f a xs)
    {B : Silmaril.Wasm.Component.Runtime.CStore (E3 P)}
    {th : Option Silmaril.Wasm.Component.Runtime.ThreadId}
    {ys' : Store (Silmaril.Wasm.Component.Runtime.CanonHost (E3 P))} {yt : Thread}
    {calls : List (σ × CallRec × σ)} {q q' : σ}
    (hs : ASeg g (SiteI c) B th q (cs, Thread.invokeFlat a xs) calls q' (ys', yt)) {E : Ctx} {a' h : Nat}
    {args : List Execution.Core.Val}
    (hd' : decompose? (yt.config (Store.mapH trampIdx ys')).store (yt.config (Store.mapH trampIdx ys')).code =
      some (E, a', h, args)) :
    ∃ (rounds : List (Round I.E)) (e : I.E.Op) (q : I.HState),
      List.Forall₂ (RoundOf c I g) calls rounds ∧ I.importOp? h args = some e ∧
      I.Path P (.idle I.store) (.inr (.ask f) :: callMoves (rounds ++ [⟨e, .trap⟩]) ++
        [.inr (.ans f .trap)]) q :=
  path_callout_trapAt C.toAt hs hd'

/-! ## Component import calls -/

/-- The answer of a typed lowering is the payload answer of its flat values. -/
theorem payloadAnswer_flat {ft : Silmaril.Wasm.Game.FnType} {w : Silmaril.Wasm.Game.Answer ft}
    {ys : List Flat} (hw : Silmaril.Wasm.Game.Answer.toResult w = .values (ys.map ofFlat)) :
    payloadAnswer ft (some (.flat ys)) = w := by
  cases w with
  | values v =>
    have hv : v.1 = ys.map ofFlat := by
      simpa only [Silmaril.Wasm.Game.Answer.toResult, Result.values.injEq] using hw
    have ht : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal ft.results (ys.map ofFlat) := hv ▸ v.2
    have htyped : typed? ft.results (ys.map ofFlat) = some ⟨ys.map ofFlat, ht⟩ := by
      simp only [typed?, ht, dite_true]
    simp only [payloadAnswer, htyped]
    exact congrArg _ (Subtype.ext hv.symm)
  | trap => cases hw
  | throw _ => cases hw

/-- **An answered callout is a component import call answered by `g`** in the recorded host
state, related to its round by `ImpRel`. -/
theorem impRel_of_round {cl : σ × CallRec × σ} {r : Round I.E}
    (h : RoundOf c I g cl r) :
    ∃ ds, ImpRel c I r ds ∧ HostRun g cl.1 ds cl.2.2 := by
  obtain ⟨p, ws, us, hp, hws, hg, hus, hw⟩ := h.2.2
  have hk : r.1.1.val < c.imports.length := (List.getElem?_eq_some_iff.mp hp).1
  have hup : (some (Payload.vals us)).bind (Silmaril.Wasm.Component.Adapter.lower p.2).up =
      some (.flat (lowerArgs p.2.results us)) := by
    simp only [Option.bind_some, Silmaril.Wasm.Component.Adapter.up, Silmaril.Wasm.Component.checkLower,
      hus, ite_true, Option.map_some]
  refine ⟨[⟨(⟨r.1.1.val, hk⟩, .vals ws), some (.vals us)⟩], ⟨p.1, p.2, _, hp, payloadAnswer_flat hw,
    ?_⟩, .cons ⟨⟨r.1.1.val, hk⟩, ws, rfl, hg⟩ (.nil _)⟩
  show match liftArgs p.2.params (r.1.2.1.filterMap toFlat?) with
    | none => _ | some ws => _
  rw [hws]
  exact ⟨hk, some (.vals us), rfl, hup.symm⟩

/-- **A failing callout is a component import call answered by `g` with a trap** in host
state `s`, or no call when the arguments do not lift, related to its trap round by `ImpRel`. -/
theorem impRel_fail {e : I.E.Op} {L : LowerSite P} {ys : List Flat} {s : σ} (hq : SiteI c L)
    (hk : e.1.val = L.f.idx) (hys : e.2.1.filterMap toFlat? = ys) (hf : L.Fails g s ys) :
    ∃ ds, ImpRel c I ⟨e, .trap⟩ ds ∧ HostRun g s ds s := by
  obtain ⟨k, hkl, hfk, hfn, hp⟩ := hq
  have hk' : e.1.val = k := by rw [hk, hfk]
  have hip : c.imports[e.1.val]? = some (c.imports[k].1, c.imports[k].2) := by
    rw [hk']
    exact List.getElem?_eq_getElem hkl
  have hpa : payloadAnswer (I.imports.get e.1) none = .trap := rfl
  rcases hf with hl | ⟨ws, hws, hg⟩
  · refine ⟨[], ⟨_, _, none, hip, hpa, ?_⟩, .nil _⟩
    show match liftArgs c.imports[k].2.params (e.2.1.filterMap toFlat?) with
      | none => _ | some ws => _
    rw [hys, ← hp, hl]
    exact ⟨rfl, rfl⟩
  · show ∃ ds, ImpRel c I ⟨e, .trap⟩ ds ∧ HostRun g s ds s
    have hkl' : e.1.val < c.imports.length := hk' ▸ hkl
    refine ⟨[⟨(⟨e.1.val, hkl'⟩, .vals ws), none⟩], ⟨_, _, none, hip, hpa, ?_⟩,
      .cons ⟨⟨e.1.val, hkl'⟩, ws, rfl, ?_, rfl⟩ (.nil _)⟩
    · show match liftArgs c.imports[k].2.params (e.2.1.filterMap toFlat?) with
        | none => _ | some ws => _
      rw [hys, ← hp, hws]
      exact ⟨hkl', none, rfl, rfl⟩
    · show g s ⟨e.1.val⟩ (ws.map toRefVal) = none
      rw [hk', ← hfn]
      exact hg

end Silmaril.Proofs.Wasm.Component.Reference
