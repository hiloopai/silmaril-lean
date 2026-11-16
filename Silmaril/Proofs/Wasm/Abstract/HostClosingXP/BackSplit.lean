module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackDet

/-!
# Splitting labelled runs in a handler, and host calls in any `call_ref` form (proofs)

* `evRunN_handler_seq_split`: a labelled run of a handler in a sequence context runs its body
  alone, then the handler goes on (as `evRunN_label_seq_split` for a label);
* `evRunN_host_callRef`: a labelled run at a host call in any `call_ref` form ends there, or
  its next event answers the call;
* `decompose?_wrap_label`, `decompose?_wrap_handler`, `decompose?_wrap_frame`: a context around
  code at a host call is at that host call.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Contexts at a host call -/

theorem decompose?_wrap_label {s : Store H} {ws : List Val} {n : Nat} {cont : List Instr}
    {b rest : List Admin} (hd : (decompose? s b).isSome) :
    (decompose? s (vals ws ++ [.label n cont b] ++ rest)).isSome := by
  obtain ⟨⟨E, a, hh, us⟩, hd⟩ := Option.isSome_iff_exists.mp hd
  rw [decompose?_wrap ws rest (decompose?_label_some hd)]
  rfl

theorem decompose?_wrap_handler {s : Store H} {ws : List Val} {n : Nat} {cs : List Catch}
    {b rest : List Admin} (hd : (decompose? s b).isSome) :
    (decompose? s (vals ws ++ [.handler n cs b] ++ rest)).isSome := by
  obtain ⟨⟨E, a, hh, us⟩, hd⟩ := Option.isSome_iff_exists.mp hd
  rw [decompose?_wrap ws rest (decompose?_handler_some hd)]
  rfl

theorem decompose?_wrap_frame {s : Store H} {ws : List Val} {n : Nat} {F : Frame}
    {b rest : List Admin} (hd : (decompose? s b).isSome) :
    (decompose? s (vals ws ++ [.frame n F b] ++ rest)).isSome := by
  obtain ⟨⟨E, a, hh, us⟩, hd⟩ := Option.isSome_iff_exists.mp hd
  rw [decompose?_wrap ws rest (decompose?_frame_some hd)]
  rfl

theorem decompose?_wrap_seq {s : Store H} {ws : List Val} {b rest : List Admin}
    (hd : (decompose? s b).isSome) : (decompose? s (vals ws ++ b ++ rest)).isSome := by
  obtain ⟨⟨E, a, hh, us⟩, hd⟩ := Option.isSome_iff_exists.mp hd
  rw [decompose?_wrap ws rest hd]
  rfl

/-! ## Handlers -/

/-- A handler exit form is a label exit form. -/
theorem handlerExit_labelExit {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}
    {b out : List Admin} (h : HandlerExit s f n cs b out) : ∃ out', LabelExit 0 [] b out' := by
  cases h with
  | vals vs => exact ⟨_, .vals vs⟩
  | @br _ vs l rest => exact ends_labelExit (o := .br l.toNat vs) ⟨l, rest, rfl, by simp⟩
  | ret => exact ⟨_, .ret⟩
  | returnCall hc => exact ⟨_, .returnCall hc⟩
  | trap => exact ⟨_, .trap⟩
  | throwEmpty a => exact ⟨_, .throw a⟩
  | @catch_ _ _ _ a _ _ _ => exact ⟨_, .throw a⟩
  | @catchRef _ _ _ a _ _ _ => exact ⟨_, .throw a⟩
  | catchAll a => exact ⟨_, .throw a⟩
  | catchAllRef a => exact ⟨_, .throw a⟩
  | @next _ _ a _ => exact ⟨_, .throw a⟩

/-- A run from a handler whose body has no step and is at a host call is empty. -/
theorem evRunN_handler_stuck {N : Nat} {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cs₀ : List Catch} {b rest : List Admin} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hb : ¬ ∃ c', Step P host ⟨s, f, b⟩ c') (hd : (decompose? s b).isSome)
    (h : EvRunN P host N ⟨s, f, vals ws ++ [.handler n cs₀ b] ++ rest⟩ cs c) :
    cs = [] ∧ c = ⟨s, f, vals ws ++ [.handler n cs₀ b] ++ rest⟩ := by
  suffices hX : ∀ c', ¬ Step P host ⟨s, f, vals ws ++ [.handler n cs₀ b] ++ rest⟩ c' by
    obtain ⟨h₁, h₂⟩ := evRunN_of_stuck hX h
    exact ⟨h₂, h₁⟩
  intro c' hc'
  obtain ⟨c₀, h₀, -⟩ := Step.ctx_in_seq (X := .handler n cs₀ b) trivial (by simpa using hc')
  rcases Step.handler_inv h₀ with ⟨s', f', b', hin, -⟩ | ⟨out, hex, -⟩
  · exact hb ⟨_, hin⟩
  · obtain ⟨out', hx⟩ := handlerExit_labelExit hex
    rw [decompose?_labelExit hx] at hd
    cases hd

/-- The conclusion of `evRunN_handler_seq_split`. -/
def HandlerSeqSplitL (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (N : Nat)
    (s : Store H) (f : Frame) (ws : List Val) (n : Nat) (cs₀ : List Catch) (b rest : List Admin)
    (cs : List (Call (wasmHostSig H))) (c : Config H) : Prop :=
  ∃ (cb : Config H) (N₁ : Nat) (cs₁ cs₂ : List (Call (wasmHostSig H))), cs = cs₁ ++ cs₂ ∧
    N₁ ≤ N ∧ EvRunN P host N₁ ⟨s, f, b⟩ cs₁ cb ∧ (∀ c', ¬ Step P Det.noHost cb c') ∧
    EvRunN P host (N - N₁) ⟨cb.store, cb.frame, vals ws ++ [.handler n cs₀ cb.code] ++ rest⟩
      cs₂ c ∧
    ((decompose? cb.store cb.code).isSome →
      cs₂ = [] ∧ c = ⟨cb.store, cb.frame, vals ws ++ [.handler n cs₀ cb.code] ++ rest⟩)

/-- **Label transfer** (`hEvStep_unique`). -/
theorem hEvStep_transfer' {I I' O O' : Config H} {l : Option (Call (wasmHostSig H))}
    (hO : HEvStep P host O l O') (hI : Step P host I I')
    (hlift : ∀ l', HEvStep P host I l' I' → HEvStep P host O l' O') : HEvStep P host I l I' := by
  obtain ⟨l', h'⟩ := step_hEvStep hI
  obtain rfl := hEvStep_unique (hlift l' h') hO
  exact h'

/-- **A labelled run in a handler**: the body runs alone; then the handler around it goes
on. If the body ends at a host call, so does the whole run. -/
theorem evRunN_handler_seq_split {N : Nat} {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cs₀ : List Catch} {b rest : List Admin} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN P host N ⟨s, f, vals ws ++ [.handler n cs₀ b] ++ rest⟩ cs c)
    (hend : ∀ c', ¬ Step P Det.noHost c c') :
    HandlerSeqSplitL P host N s f ws n cs₀ b rest cs c := by
  suffices key : ∀ N y cs, EvRunN P host N y cs c → ∀ s f b,
      y = ⟨s, f, vals ws ++ [.handler n cs₀ b] ++ rest⟩ →
      HandlerSeqSplitL P host N s f ws n cs₀ b rest cs c
    from key _ _ _ hrun s f b rfl
  clear hrun
  have hstop : ∀ N s f b cs, ¬ (∃ c', Step P host ⟨s, f, b⟩ c') →
      EvRunN P host N ⟨s, f, vals ws ++ [.handler n cs₀ b] ++ rest⟩ cs c →
      HandlerSeqSplitL P host N s f ws n cs₀ b rest cs c := by
    intro N s f b cs hb h
    refine ⟨⟨s, f, b⟩, 0, [], cs, rfl, by omega, .refl _,
      fun c' h' => hb ⟨c', Step.of_noHost host h'⟩, h, fun hd => ?_⟩
    exact evRunN_handler_stuck hb hd h
  intro N y cs hy
  induction hy with
  | refl =>
    intro s f b hy
    subst hy
    refine ⟨⟨s, f, b⟩, 0, [], [], rfl, le_refl _, .refl _, fun c' h => ?_, .refl _,
      fun _ => ⟨rfl, rfl⟩⟩
    rcases c' with ⟨s', f', b'⟩
    exact hend _ (Silmaril.Wasm.Logic.Core.Step.ctx ws rest (Step.ctxtHandler h))
  | @silent N y z c₃ cs hstep hrest ih =>
    intro s f b hy
    subst hy
    by_cases hb : ∃ c', Step P host ⟨s, f, b⟩ c'
    · obtain ⟨c₀, h₀, hz⟩ := Step.ctx_in_seq (X := .handler n cs₀ b) trivial
        (by simpa using hEvStep_step hstep)
      rcases Step.handler_inv h₀ with ⟨s', f', b', hin, rfl⟩ | ⟨out, hex, -⟩
      · have hin' : HEvStep P host ⟨s, f, b⟩ none ⟨s', f', b'⟩ :=
          hEvStep_transfer' hstep hin fun l' h' => by
            simpa [hz] using hEvStep_ctx ws rest (hEvStep_handler n cs₀ h')
        obtain ⟨cb, N₁, cs₁, cs₂, rfl, hN₁, h₁, hs₁, hk, hx⟩ := ih hend hstop s' f' b' (by simp [hz])
        refine ⟨cb, N₁ + 1, cs₁, cs₂, rfl, by omega, .silent hin' h₁, hs₁, ?_, hx⟩
        rwa [show N + 1 - (N₁ + 1) = N - N₁ by omega]
      · obtain ⟨c', hc'⟩ := hb
        obtain ⟨out', hx⟩ := handlerExit_labelExit hex
        exact (labelExit_stuck (P := P) (host := host) (s := s) (f := f) hx c' hc').elim
    · exact hstop _ s f b cs hb (.silent hstep hrest)
  | @event N y z c₃ e cs hstep hrest ih =>
    intro s f b hy
    subst hy
    by_cases hb : ∃ c', Step P host ⟨s, f, b⟩ c'
    · obtain ⟨c₀, h₀, hz⟩ := Step.ctx_in_seq (X := .handler n cs₀ b) trivial
        (by simpa using hEvStep_step hstep)
      rcases Step.handler_inv h₀ with ⟨s', f', b', hin, rfl⟩ | ⟨out, hex, -⟩
      · have hin' : HEvStep P host ⟨s, f, b⟩ (some e) ⟨s', f', b'⟩ :=
          hEvStep_transfer' hstep hin fun l' h' => by
            simpa [hz] using hEvStep_ctx ws rest (hEvStep_handler n cs₀ h')
        obtain ⟨cb, N₁, cs₁, cs₂, rfl, hN₁, h₁, hs₁, hk, hx⟩ := ih hend hstop s' f' b' (by simp [hz])
        refine ⟨cb, N₁ + 1, e :: cs₁, cs₂, rfl, by omega, .event hin' h₁, hs₁, ?_, hx⟩
        rwa [show N + 1 - (N₁ + 1) = N - N₁ by omega]
      · obtain ⟨c', hc'⟩ := hb
        obtain ⟨out', hx⟩ := handlerExit_labelExit hex
        exact (labelExit_stuck (P := P) (host := host) (s := s) (f := f) hx c' hc').elim
    · exact hstop _ s f b _ hb (.event hstep hrest)

/-! ## Host calls in any `call_ref` form -/

/-- **A labelled run at a host call**, in any `call_ref` form: it ends there with no event, or
its next event answers the call. -/
theorem evRunN_host_callRef {n : Nat} {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H}
    {hh : H} {ps rs : Validation.Ty (.list .val)} {ws us : List Val} {cr : Admin}
    {rest : List Admin} {c : Config H} {cs : List (Call (wasmHostSig H))} (hcr : cr.IsCallRef)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (he : Validation.Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (hrun : EvRunN P host n ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: cr :: rest⟩ cs c) :
    (c = ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: cr :: rest⟩ ∧ cs = []) ∨
      ∃ s' r m cs', m < n ∧ cs = ⟨(hh, s, us), (s', r)⟩ :: cs' ∧
        host hh s us (.returned s' r) ∧
        EvRunN P host m ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩ cs' c := by
  have hd : decompose? s (vals ws ++ vals us ++ .ref (.func a) :: cr :: rest) =
      some (.top ws rest, a, hh, us) := by
    have := decompose?_wrap (s := s) ws rest (decompose?_redex hcr hf he hn hcode)
    simpa [Ctx.wrap] using this
  suffices key : ∀ n y cs, EvRunN P host n y cs c →
      y = ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: cr :: rest⟩ →
      (c = y ∧ cs = []) ∨ ∃ s' r m cs', m < n ∧ cs = ⟨(hh, s, us), (s', r)⟩ :: cs' ∧
        host hh s us (.returned s' r) ∧
        EvRunN P host m ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩ cs' c by
    rcases key _ _ _ hrun rfl with ⟨h₁, h₂⟩ | h
    · exact .inl ⟨h₁, h₂⟩
    · exact .inr h
  clear hrun
  intro n y cs hy
  induction hy with
  | refl => exact fun _ => .inl ⟨rfl, rfl⟩
  | @silent m y z c₃ cs hs hrest ih =>
    intro hy
    subst hy
    rcases hs with h | ⟨rfl, -⟩
    · exact (noFree_of_decompose hd h).elim
    · rcases ih rfl with ⟨rfl, rfl⟩ | ⟨s', r, m', cs', hm', rfl, hans, hk⟩
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨s', r, m', cs', by omega, rfl, hans, hk⟩
  | @event m y z c₃ e cs hs hrest _ =>
    intro hy
    subst hy
    obtain ⟨⟨hh', s₀, us'⟩, ⟨s', r⟩⟩ := e
    obtain ⟨E, a', hd', hs₀, hans, rfl⟩ := hs
    dsimp only at hd' hs₀ hans
    rw [hd] at hd'
    simp only [Option.some.injEq, Prod.mk.injEq] at hd'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hd'
    subst hs₀
    exact .inr ⟨s', r, m, cs, by omega, rfl, hans, by simpa [Ctx.fill] using hrest⟩

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
