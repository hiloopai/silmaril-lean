module

public import Silmaril.Wasm.Unified.Component.Res.Defs
public import Silmaril.Wasm.Unified.Component.Inst.Thms
public import Silmaril.Wasm.Resource.Link.Thms
public import Silmaril.Wasm.Resource.Protocol.Thms
public import Silmaril.Games.Handler.Thms

/-!
# Resource sentences of specific components

Proved, in every model `M` of every core signature (the sentences are about wiring, so the
interpretation of the opcodes does not matter):

* `quiet_bind`, `quiet_interp`, `quiet_runChain`, `quiet_target`, `quiet_exportsH`: quiet
  programs are closed under the handler combinators of the component IR; the exports of a
  component without core instances whose export targets are quiet run quiet programs
  (`exportsH` below the import mask `maskH`).
* `quietInv`: a protocol invariant (`Silmaril.Wasm.Resource.LTSInv`) of a handler whose programs
  are quiet, for the client handle protocol read through `resEv d`: every move is accepted
  (lower answers are `alloc` or `skip`, and an `alloc` of a live handle is an environment
  fault in the client role). `handler_res_client`: every play of such a handler is accepted.
* `denU_nodeless`: a component without nodes is the handler `maskH ⋙ exportsH`.
* **`sat_res_client`**: a component without core instances whose exports never forward to
  `d.drop` or `d.rep` satisfies the client resource sentence `res x d client` in every model.
  **`sat_makeFwd`**: the re-export of the toy's `make` satisfies the client sentence of the toy's
  resource type `toyDecl`.
* **Refuted**: `not_sat_dropFwd`, `not_sat_getFwd`: re-exporting the toy's `drop` (resp. `get`)
  violates the client sentence in every model: the environment calls the re-export with a
  handle `0` that was never allocated, and the component passes it on (`free 0`, resp.
  `use 0`, of a dead handle). A forwarder trusts its caller, so the handle discipline is the
  caller's obligation, which a client sentence about the forwarder cannot assume.
* **Linking with a correct provider** (`client_provider_run`, `client_provider_accepts`): on a
  word of handle events accepted by the client protocol (the program, here a component of
  `cinst`) and by the provider protocol (its environment, e.g. the toy component, a correct
  provider by `Silmaril.Wasm.Resource.CompToy.toy_compProvider`), both protocols run in lock-step
  through the same live-handle lists and never reach the environment-fault state: no handle is
  allocated twice or used after being freed, by either side. This is the protocol half of
  linking; the toy's strategy is a silmaril reference program (`refMultiSem`), not a strategy of
  `Silmaril.Wasm.Component`, so the composite of the toy with a component of `cinst` is not formed
  here.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open Silmaril.Wasm.Component Silmaril.Wasm.Unified Silmaril.Wasm.Resource
open Silmaril.Games (Prog Strategy Reduction Move LTS)

variable {d : ResDecl}

/-! ## Quiet programs -/

theorem quiet_bind {P : Prog sigU (Option Payload)} (hP : Quiet d P)
    {f : Option Payload → Prog sigU (Option Payload)} (hf : ∀ a, Quiet d (f a)) :
    Quiet d (P.bind f) := by
  induction hP with
  | pure r => exact hf r
  | call m k hd hr _ ih => exact .call m (fun n => (k n).bind f) hd hr ih

theorem quiet_interp {h : Silmaril.Games.Handler sigU sigU}
    (hh : ∀ m : Nat × Payload, m.1 ≠ d.drop → m.1 ≠ d.rep → Quiet d (h m))
    {P : Prog sigU (Option Payload)} (hP : Quiet d P) : Quiet d (P.interp h) := by
  induction hP with
  | pure r => exact .pure r
  | call m k hd hr _ ih => exact quiet_bind (hh m hd hr) ih

theorem quiet_runChain {k : Payload → Prog sigU (Option Payload)} (hk : ∀ a, Quiet d (k a)) :
    ∀ (c : List Adapter) (a : Payload), Quiet d (runChain c k a)
  | [], a => hk a
  | ad :: c, a => by
    unfold runChain
    split
    · exact .pure none
    · exact quiet_bind (quiet_runChain hk c _) fun r => .pure _

theorem quiet_target (e : Nat) {t : Target} (ht : Impl.QuietFor d ⟨[], t⟩) (a : Payload) :
    Quiet d (t.prog e a) := by
  cases t with
  | call r =>
    have hr : r ≠ d.drop ∧ r ≠ d.rep := ht
    show Quiet d (if r < e then .call (r, a) (fun n => .pure n) else .pure none)
    split
    · exact .call (r, a) (fun n => .pure n) hr.1 hr.2 fun n => .pure n
    · exact .pure none
  | const res => exact .pure res

theorem quiet_maskH (e : Nat) (m : Nat × Payload) (hd : m.1 ≠ d.drop) (hr : m.1 ≠ d.rep) :
    Quiet d (maskH e m) :=
  quiet_target (t := .call m.1) e ⟨hd, hr⟩ m.2

theorem quiet_impl (e : Nat) {im : Impl} (him : im.QuietFor d) (a : Payload) :
    Quiet d (im.prog e a) :=
  quiet_runChain (quiet_target e (t := im.target) him) im.chain a

/-- The exports of a component without core instances, below its import mask, are quiet. -/
theorem quiet_exportsH (e : Nat) (xs : List Silmaril.Wasm.Component.Export) (hx : ∀ x ∈ xs, x.impl.QuietFor d)
    (q : Nat × Payload) : Quiet d ((maskH e).comp (exportsH e xs) q) := by
  show Quiet d ((implsH e (xs.map Silmaril.Wasm.Component.Export.impl) q).interp (maskH e))
  refine quiet_interp (quiet_maskH e) ?_
  unfold implsH
  split
  · next im him =>
    have hmem : im ∈ xs.map Silmaril.Wasm.Component.Export.impl := List.mem_of_getElem? him
    obtain ⟨x, hx', hxi⟩ := List.mem_map.1 hmem
    exact hxi ▸ quiet_impl e (hx x hx') q.2
  · exact .pure none

/-! ## The client protocol on quiet handlers -/

theorem HEv.quiet_step {Hd : Type} [DecidableEq Hd] (q : Option (List Hd)) {e : HEv Hd}
    (he : e.Quiet) : ∃ q', handleStep .client q e = some q' := by
  cases q with
  | none => exact ⟨none, rfl⟩
  | some L =>
    cases e with
    | alloc h =>
      by_cases hh : h ∈ L
      · exact ⟨none, by simp [handleStep, hh, fault]⟩
      · exact ⟨some (h :: L), by simp [handleStep, hh]⟩
    | skip => exact ⟨some L, rfl⟩
    | use h => exact he.elim
    | free h => exact he.elim

theorem resEv_quiet_inr (e : Silmaril.Games.Ev sigU) : (resEv d (.inr e)).Quiet := by
  cases e <;> trivial

theorem resEv_quiet_ans (m : Nat × Payload) (n : Option Payload) :
    (resEv d (.inl (.ans m n))).Quiet := by
  unfold resEv
  split
  · next _ _ _ heq => cases heq
  · split <;> trivial
  · trivial

theorem resEv_quiet_ask (m : Nat × Payload) (hd : m.1 ≠ d.drop) (hr : m.1 ≠ d.rep) :
    (resEv d (.inl (.ask m))).Quiet := by
  unfold resEv
  split
  · next _ i h heq =>
    have hi : i = m.1 := by cases heq; rfl
    have hd' : i ≠ d.drop := hi ▸ hd
    have hr' : i ≠ d.rep := hi ▸ hr
    simp only [hd', hr', ↓reduceIte]
    trivial
  · next _ _ _ _ heq => cases heq
  · trivial

/-- The protocol invariant of a quiet handler: the program it is running is quiet. -/
def quietJ (d : ResDecl) (H : Silmaril.Games.Handler sigU sigU) :
    Option (List Flat) → H.toReduction.State → Prop
  | _, .idle => True
  | _, .run _ P => Quiet d P
  | _, .wait _ _ k => ∀ n, Quiet d (k n)

theorem quietJ_vis {H : Silmaril.Games.Handler sigU sigU} (hH : ∀ q, Quiet d (H q)) {q : Option (List Flat)}
    {x y : H.toReduction.State} {o : Move sigU sigU} (hs : Reduction.Step H.toReduction x (some o) y)
    (hJ : quietJ d H q x) :
    ∃ q', ((handleProto Flat .client).comap (resEv d)).step q o = some q' ∧ quietJ d H q' y := by
  cases hs with
  | ask q₀ =>
    obtain ⟨q', hq'⟩ := HEv.quiet_step q (resEv_quiet_inr (d := d) (.ask q₀))
    exact ⟨q', hq', hH q₀⟩
  | @call _ c m k hc =>
    have hq : Quiet d (Prog.call m k) := (hc : c = .call m k) ▸ hJ
    cases hq with
    | call _ _ hd hr hk =>
      obtain ⟨q', hq'⟩ := HEv.quiet_step q (resEv_quiet_ask m hd hr)
      exact ⟨q', hq', hk⟩
  | resume q₀ m k n =>
    obtain ⟨q', hq'⟩ := HEv.quiet_step q (resEv_quiet_ans (d := d) m n)
    exact ⟨q', hq', hJ n⟩
  | ret _ =>
    obtain ⟨q', hq'⟩ := HEv.quiet_step q (resEv_quiet_inr (d := d) (.ans _ _))
    exact ⟨q', hq', trivial⟩

/-- **The protocol invariant of a quiet handler** for the client handle protocol. -/
def quietInv (d : ResDecl) (H : Silmaril.Games.Handler sigU sigU) (hH : ∀ q, Quiet d (H q)) :
    LTSInv H.toReduction.toLTS ((handleProto Flat .client).comap (resEv d)) where
  J := quietJ d H
  init := trivial
  tau := fun hs _ => by
    cases hs with
    | tau h => exact (h : False).elim
  vis := fun hs hJ => quietJ_vis hH hs hJ

/-- Every play of a quiet handler is accepted by the client handle protocol. -/
theorem handler_res_client (H : Silmaril.Games.Handler sigU sigU) (hH : ∀ q, Quiet d (H q))
    (s : List (Move sigU sigU)) (hs : s ∈ Strategy.ofHandler H) :
    (handleProto Flat .client).Accepts (s.map (resEv d)) :=
  (Protocol.accepts_comap _ _ _).1 ((quietInv d H hH).accepts_traces (Strategy.mem_ofHandler.1 hs))

/-! ## Components without core instances -/

variable {S : FSig}

/-- A component without nodes is a handler: its exports below the import mask. -/
theorem denU_nodeless (C : CoreSem (UMod S)) (I : Iface) (xs : List Silmaril.Wasm.Component.Export) :
    (Comp.mk I [] xs).denU C =
      Strategy.ofHandler ((maskH I.length).comp (exportsH I.length xs)) := by
  rw [Comp.denU, denNodes, envAfter, Strategy.ofHandler_comp]

/-- A component without nodes whose wiring has no adapters uses only adapters in any `K`. -/
theorem uses_nodeless (K : CMSig) (I : Iface) (xs : List Silmaril.Wasm.Component.Export)
    (hc : ∀ x ∈ xs, x.impl.chain = []) : (CProg.comp (S := S) (.mk I [] xs)).Uses K := by
  intro im him a ha
  have him' : im ∈ xs.map Silmaril.Wasm.Component.Export.impl := by
    simpa only [CProg.impls, compImpls, nodesImpls, List.nil_append] using him
  obtain ⟨x, hx, hxi⟩ := List.mem_map.1 him'
  have hnil : im.chain = [] := hxi ▸ hc x hx
  exact absurd (hnil ▸ ha) List.not_mem_nil

/-- **Client resource sentences of components without core instances**: if no export forwards
to `d.drop` or `d.rep`, the component follows the client handle protocol of `d` in every
model. -/
theorem sat_res_client (M : PModel S) {K : CMSig} (I : Iface) (xs : List Silmaril.Wasm.Component.Export)
    (hu : (CProg.comp (S := S) (.mk I [] xs)).Uses K) (hd : CMFeature.resource d ∈ K)
    (hx : ∀ x ∈ xs, x.impl.QuietFor d) :
    CSat (T := (S, K)) M (.res ⟨.comp (.mk I [] xs), hu⟩ d hd .client) := fun s hs =>
  handler_res_client _ (quiet_exportsH I.length xs hx) s
    (denU_nodeless (coreSem M) I xs ▸ hs)

/-! ## Clients of the toy's resource -/

theorem toyDecl_mem : CMFeature.resource toyDecl ∈ toySig :=
  Or.inr ⟨toyDecl, rfl, rfl⟩

/-- The interface of the toy's client side is the toy's export interface, in order. -/
theorem toyIface_names : toyIface.map Prod.fst = ["make", "get", "drop"] := rfl

theorem makeFwd_uses : (CProg.comp (makeFwd (S := S))).Uses toySig :=
  uses_nodeless _ _ _ fun x hx => by rw [List.mem_singleton.1 hx]

theorem dropFwd_uses : (CProg.comp (dropFwd (S := S))).Uses toySig :=
  uses_nodeless _ _ _ fun x hx => by rw [List.mem_singleton.1 hx]

theorem getFwd_uses : (CProg.comp (getFwd (S := S))).Uses toySig :=
  uses_nodeless _ _ _ fun x hx => by rw [List.mem_singleton.1 hx]

/-- **The re-export of the toy's `make` follows the client protocol** of the toy's resource
type, in every model. -/
theorem sat_makeFwd (M : PModel S) :
    CSat (T := (S, toySig)) M (.res ⟨.comp makeFwd, makeFwd_uses⟩ toyDecl toyDecl_mem .client) :=
  sat_res_client M toyIface _ makeFwd_uses toyDecl_mem fun x hx => by
    rw [List.mem_singleton.1 hx]
    exact ⟨by decide, by decide⟩

/-- The handle `0`. -/
abbrev h0 : Flat := Flat.i32 0

/-- The play "call export `0` with `[h0]`; the component calls import `r` with `[h0]`" of a
re-export of import `r` of `toyIface`. -/
theorem fwd_play (M : PModel S) (n : String) (ft : FuncTy) (r : Nat) (hr : r < 3) :
    [.inr (.ask (0, .flat [h0])), .inl (.ask (r, .flat [h0]))] ∈
      den M (.comp (.mk toyIface [] [⟨n, ft, .fwd r⟩])) := by
  show _ ∈ (Comp.mk toyIface [] [⟨n, ft, .fwd r⟩]).denU (coreSem M)
  rw [denU_nodeless, Strategy.mem_ofHandler]
  refine ⟨_, .vis (.ask _) (.vis (.call (k := fun a => Prog.pure a) ?_) (.nil _))⟩
  show (maskH 3).comp (exportsH 3 [⟨n, ft, .fwd r⟩]) (0, .flat [h0]) = .call (r, .flat [h0]) _
  simp [Silmaril.Games.Handler.comp, exportsH, implsH, Impl.prog, runChain, Target.prog, hr, maskH,
    Prog.interp]

/-- **Re-exporting the toy's `drop` violates the client protocol**, in every model: the
environment drops the never-allocated handle `0` through it. -/
theorem not_sat_dropFwd (M : PModel S) :
    ¬ CSat (T := (S, toySig)) M (.res ⟨.comp dropFwd, dropFwd_uses⟩ toyDecl toyDecl_mem .client) :=
  fun h => absurd (h _ (fwd_play M "drop" ⟨[.u32], []⟩ 2 (by decide))) (by unfold Protocol.Accepts; decide)

/-- **Re-exporting the toy's `get` violates the client protocol**, in every model: the
environment uses the never-allocated handle `0` through it. -/
theorem not_sat_getFwd (M : PModel S) :
    ¬ CSat (T := (S, toySig)) M (.res ⟨.comp getFwd, getFwd_uses⟩ toyDecl toyDecl_mem .client) :=
  fun h => absurd (h _ (fwd_play M "get" ⟨[.u32], [.u32]⟩ 1 (by decide))) (by unfold Protocol.Accepts; decide)

/-! ## Linking a client with a correct provider -/

section Link

variable {Hd : Type} [DecidableEq Hd]

/-- One handle event from a live list: client and provider agree, or one of them rejects. -/
theorem link_step (L : List Hd) (e : HEv Hd) :
    (∃ L', handleStep .client (some L) e = some (some L') ∧
        handleStep .provider (some L) e = some (some L')) ∨
      handleStep .client (some L) e = none ∨ handleStep .provider (some L) e = none := by
  cases e with
  | alloc h =>
    by_cases hh : h ∈ L
    · exact .inr (.inr (by simp [handleStep, hh, fault]))
    · exact .inl ⟨h :: L, by simp [handleStep, hh], by simp [handleStep, hh]⟩
  | use h =>
    by_cases hh : h ∈ L
    · exact .inl ⟨L, by simp [handleStep, hh], by simp [handleStep, hh]⟩
    · exact .inr (.inl (by simp [handleStep, hh, fault]))
  | free h =>
    by_cases hh : h ∈ L
    · exact .inl ⟨L.erase h, by simp [handleStep, hh], by simp [handleStep, hh]⟩
    · exact .inr (.inl (by simp [handleStep, hh, fault]))
  | skip => exact .inl ⟨L, rfl, rfl⟩

theorem run_cons_of_step (r : Role) {q q' : Option (List Hd)} {e : HEv Hd} (w : List (HEv Hd))
    (h : handleStep r q e = some q') :
    (handleProto Hd r).run q (e :: w) = (handleProto Hd r).run q' w := by
  show (handleStep r q e).bind _ = _
  rw [h]
  rfl

theorem run_cons_of_reject (r : Role) {q : Option (List Hd)} {e : HEv Hd} (w : List (HEv Hd))
    (h : handleStep r q e = none) : (handleProto Hd r).run q (e :: w) = none := by
  show (handleStep r q e).bind _ = _
  rw [h]
  rfl

/-- **Client and provider in lock-step**: on a word both accept, from the same live handles,
the two protocols visit the same live-handle lists and never reach the environment-fault
state. -/
theorem client_provider_run :
    ∀ (w : List (HEv Hd)) (L : List Hd),
      ((handleProto Hd .client).run (some L) w).isSome →
      ((handleProto Hd .provider).run (some L) w).isSome →
      ∃ L', (handleProto Hd .client).run (some L) w = some (some L') ∧
        (handleProto Hd .provider).run (some L) w = some (some L')
  | [], L, _, _ => ⟨L, rfl, rfl⟩
  | e :: w, L, hc, hp => by
    rcases link_step L e with ⟨L', h1, h2⟩ | h1 | h1
    · rw [run_cons_of_step .client w h1] at hc ⊢
      rw [run_cons_of_step .provider w h2] at hp ⊢
      exact client_provider_run w L' hc hp
    · exact absurd (run_cons_of_reject .client w h1 ▸ hc) (by simp)
    · exact absurd (run_cons_of_reject .provider w h1 ▸ hp) (by simp)

/-- **Linking with a correct provider**: a word of handle events accepted by the client
protocol (a program using handles) and by the provider protocol (its environment handing them
out, e.g. the toy component, `Silmaril.Wasm.Resource.CompToy.toy_compProvider`) never reaches the
environment-fault state: both sides keep the handle discipline. -/
theorem client_provider_accepts (w : List (HEv Hd)) (hc : (handleProto Hd .client).Accepts w)
    (hp : (handleProto Hd .provider).Accepts w) :
    ∃ L, (handleProto Hd .client).run (some []) w = some (some L) ∧
      (handleProto Hd .provider).run (some []) w = some (some L) :=
  client_provider_run w [] hc hp

end Link

end Silmaril.Wasm.Unified.Component
