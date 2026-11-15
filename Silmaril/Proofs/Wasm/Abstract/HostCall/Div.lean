module

public import Silmaril.Proofs.Wasm.Abstract.HostCall.Split
public import Silmaril.Proofs.Wasm.Abstract.HostCall.Ctx
public import Silmaril.Proofs.Wasm.Abstract.HostCall.Through
public import Silmaril.Wasm.Execution.Core.InversionHost.Thms
public import Silmaril.Wasm.Execution.Core.Sim.TypedContext
public import Silmaril.Wasm.SingleThreaded.Exec.InterpTyped
import Silmaril.Wasm.Interp.Thms

/-!
# Splitting a divergent Core run (proofs)

The divergent analogues of `steps_seq_split`, any profile and host:

* `trap_not_diverges`, `throw_not_diverges`: a head trap or `throwing x` only bubbles,
  so it does not diverge;
* `diverges_seq_split`: an infinite run of `es ++ rest` diverges in `es` itself, or `es`
  first runs to values `ws` and the run of `vals ws ++ rest` diverges;
* `diverges_label_split`, `diverges_frame_split`: an infinite run of a `LABEL` or `FRAME`
  diverges inside it, or its body first runs to an exit form (`LabelExit`, `FrameExit`)
  and the run of what it exits to diverges;
* `diverges_host_call`: an infinite run at a host call under a continuation: the host may
  diverge on the call, or it answers and the continuation diverges;
* `diverges_wasm_call`: an infinite run at a Wasm call enters the callee's frame, and the
  run from there diverges;
* `diverges_label_seq_split`, `diverges_frame_seq_split`: the same splits for a label or a
  call frame in place, under values and before a continuation: the body diverges, or it runs
  to a stuck end and the context around that end diverges.

Deterministic profile, typed configurations (`Sim.ContextTyped`):

* `diverges_through`, `diverges_through_steps`: a divergent run passes through every
  host-free step (run). Every step from a configuration with a host-free step is host-free
  (`dstep_of_step`); the interpreter step `stepI` is reached from every host-free successor
  in at most one step (`stepI_maximal`), and every successor other than it shrinks the code
  (`Interp.step?_lag_at`). So the divergent trace can be redirected through any host-free
  successor, by well-founded induction on the size of the code inside a coinduction.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostCall

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- A head trap does not diverge. -/
theorem trap_not_diverges {s : Store H} {f : Frame} {ws : List Val} {r : List Admin} :
    ¬ Diverges P host ⟨s, f, vals ws ++ .trap :: r⟩ := by
  suffices key : ∀ n (ws : List Val) (r : List Admin), ws.length + r.length = n →
      ¬ Diverges P host ⟨s, f, vals ws ++ .trap :: r⟩ from key _ ws r rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ws r hn hd
    obtain ⟨b, hb, hd'⟩ := hd.unfold
    obtain ⟨ws', r', rfl, hlt⟩ := trap_step hb
    exact ih _ (hn ▸ hlt) ws' r' rfl hd'

/-- A head exception does not diverge. -/
theorem throw_not_diverges {s : Store H} {f : Frame} {ws : List Val} {x : Nat}
    {r : List Admin} : ¬ Diverges P host ⟨s, f, vals ws ++ throwing x ++ r⟩ := by
  suffices key : ∀ n (ws : List Val) (r : List Admin), ws.length + r.length = n →
      ¬ Diverges P host ⟨s, f, vals ws ++ throwing x ++ r⟩ from key _ ws r rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ws r hn hd
    obtain ⟨b, hb, hd'⟩ := hd.unfold
    obtain ⟨ws', r', rfl, hlt⟩ := throw_step hb
    exact ih _ (hn ▸ hlt) ws' r' rfl hd'

/-- `es` finishes as values and the continuation diverges. -/
def DivAfter (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (f : Frame) (es rest : List Admin) : Prop :=
  ∃ (c₁ : Config H) (ws : List Val), Steps P host ⟨s, f, es⟩ c₁ ∧ c₁.code = vals ws ∧
    Diverges P host ⟨c₁.store, c₁.frame, vals ws ++ rest⟩

/-- **Splitting a divergent run of a sequence.** -/
theorem diverges_seq_split {s : Store H} {f : Frame} {es rest : List Admin}
    (h : Diverges P host ⟨s, f, es ++ rest⟩) :
    Diverges P host ⟨s, f, es⟩ ∨ DivAfter P host s f es rest := by
  classical
  by_cases hA : DivAfter P host s f es rest
  · exact .inr hA
  left
  refine Silmaril.InfiniteTrace.coinduct
    (fun c : Config H => Diverges P host ⟨c.store, c.frame, c.code ++ rest⟩ ∧
      ¬ DivAfter P host c.store c.frame c.code rest) ?_ (a := ⟨s, f, es⟩) ⟨h, hA⟩
  rintro ⟨s, f, es⟩ ⟨hd, hna⟩
  dsimp only at hd hna
  obtain ⟨⟨s', f', es'⟩, hb, hd'⟩ := hd.unfold
  rcases head_cases es with ⟨ws, rfl⟩ | ⟨ws, r, rfl⟩ | ⟨ws, x, r, rfl⟩ |
      ⟨vs, a, r, rfl, ha, hat, hax⟩
  · exact (hna ⟨_, ws, .refl, rfl, hd⟩).elim
  · exact (trap_not_diverges (P := P) (host := host) (r := r ++ rest) (by simpa using hd)).elim
  · exact (throw_not_diverges (P := P) (host := host) (r := r ++ rest) (by simpa using hd)).elim
  have hstep' : Step P host ⟨s, f, vals vs ++ a :: (r ++ rest)⟩ ⟨s', f', es'⟩ := by
    simpa using hb
  rcases Sim.Step.split_head ha hstep' with ⟨ws, us, is', rfl, hst, rfl⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -, -, ws, us, x, r₁, r₂, rfl, -, -, -⟩
  · have hst' := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) ws r hst
    refine ⟨⟨s', f', vals ws ++ is' ++ r⟩, by simpa using hst', ?_, ?_⟩
    · show Diverges P host ⟨s', f', vals ws ++ is' ++ r ++ rest⟩
      simpa [Diverges] using hd'
    · dsimp only
      rintro ⟨c₁, w, h₁, hc₁, hk⟩
      exact hna ⟨c₁, w, .head (by simpa using hst') h₁, hc₁, hk⟩
  · exact absurd rfl hat
  · exact absurd ⟨rfl, by simp⟩ (hax (ws ++ us) x)

/-- The label's body runs to an exit, and what it exits to diverges. -/
def DivLabelAfter (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (f : Frame) (k : Nat) (cont : List Instr) (is : List Admin) : Prop :=
  ∃ (c₁ : Config H) (out : List Admin), Steps P host ⟨s, f, is⟩ c₁ ∧
    LabelExit k cont c₁.code out ∧ Diverges P host ⟨c₁.store, c₁.frame, out⟩

/-- **Splitting a divergent run of a label.** -/
theorem diverges_label_split {s : Store H} {f : Frame} {k : Nat} {cont : List Instr}
    {is : List Admin} (h : Diverges P host ⟨s, f, [.label k cont is]⟩) :
    Diverges P host ⟨s, f, is⟩ ∨ DivLabelAfter P host s f k cont is := by
  classical
  by_cases hA : DivLabelAfter P host s f k cont is
  · exact .inr hA
  left
  refine Silmaril.InfiniteTrace.coinduct
    (fun c : Config H => Diverges P host ⟨c.store, c.frame, [.label k cont c.code]⟩ ∧
      ¬ DivLabelAfter P host c.store c.frame k cont c.code) ?_ (a := ⟨s, f, is⟩) ⟨h, hA⟩
  rintro ⟨s, f, is⟩ ⟨hd, hna⟩
  dsimp only at hd hna
  obtain ⟨b, hb, hd'⟩ := hd.unfold
  rcases Step.label_inv hb with ⟨s', f', is', hin, rfl⟩ | ⟨out, hex, rfl⟩
  · refine ⟨⟨s', f', is'⟩, hin, hd', ?_⟩
    dsimp only
    rintro ⟨c₁, out, h₁, hex, hk⟩
    exact hna ⟨c₁, out, .head hin h₁, hex, hk⟩
  · exact (hna ⟨⟨s, f, is⟩, out, .refl, hex, hd'⟩).elim

/-- The frame's body runs to an exit, and what it exits to diverges (in the outer frame). -/
def DivFrameAfter (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (f F : Frame) (n : Nat) (is : List Admin) : Prop :=
  ∃ (c₁ : Config H) (out : List Admin), Steps P host ⟨s, F, is⟩ c₁ ∧
    FrameExit c₁.store c₁.frame n c₁.code out ∧ Diverges P host ⟨c₁.store, f, out⟩

/-- **Splitting a divergent run of a frame.** -/
theorem diverges_frame_split {s : Store H} {f F : Frame} {n : Nat} {is : List Admin}
    (h : Diverges P host ⟨s, f, [.frame n F is]⟩) :
    Diverges P host ⟨s, F, is⟩ ∨ DivFrameAfter P host s f F n is := by
  classical
  by_cases hA : DivFrameAfter P host s f F n is
  · exact .inr hA
  left
  refine Silmaril.InfiniteTrace.coinduct
    (fun c : Config H => Diverges P host ⟨c.store, f, [.frame n c.frame c.code]⟩ ∧
      ¬ DivFrameAfter P host c.store f c.frame n c.code) ?_ (a := ⟨s, F, is⟩) ⟨h, hA⟩
  rintro ⟨s, F, is⟩ ⟨hd, hna⟩
  dsimp only at hd hna
  obtain ⟨b, hb, hd'⟩ := hd.unfold
  rcases Step.frame_inv hb with ⟨s', F', is', hin, rfl⟩ | ⟨out, hex, rfl⟩
  · refine ⟨⟨s', F', is'⟩, hin, hd', ?_⟩
    dsimp only
    rintro ⟨c₁, out, h₁, hex, hk⟩
    exact hna ⟨c₁, out, .head hin h₁, hex, hk⟩
  · exact (hna ⟨⟨s, F, is⟩, out, .refl, hex, hd'⟩).elim

/-- **A divergent run at a host call**: the host may diverge on the call (the run
stutters), or it answers and the run of the continuation diverges. -/
theorem diverges_host_call {s : Store H} {f : Frame} {vs : List Val} {a : Nat} {r : Admin}
    {fi : FuncInst H} {hh : H} {rest : List Admin} (hr : r.IsCallRef)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (h : Diverges P host ⟨s, f, vals vs ++ .ref (.func a) :: r :: rest⟩) :
    ∃ vs₁ vs₂ ps rs, vs = vs₁ ++ vs₂ ∧ Validation.Expand fi.type (.func ps rs) ∧
      vs₂.length = ps.length ∧
      (host hh s vs₂ .diverged ∨
        ∃ s' res, host hh s vs₂ (.returned s' res) ∧
          Diverges P host ⟨s', f, vals vs₁ ++ res.toAdmin ++ rest⟩) := by
  obtain ⟨b, hb, hd⟩ := h.unfold
  obtain ⟨vs₁, vs₂, ps, rs, hvs, he, hn, ⟨s', res, hh', rfl⟩ | ⟨hdiv, -⟩⟩ :=
    Step.callRef_host_inv_seq hr hf hcode hb
  · exact ⟨vs₁, vs₂, ps, rs, hvs, he, hn, .inr ⟨s', res, hh', hd⟩⟩
  · exact ⟨vs₁, vs₂, ps, rs, hvs, he, hn, .inl hdiv⟩

/-- **A divergent run at a Wasm call** enters the callee's frame, and the run from there
diverges. -/
theorem diverges_wasm_call {s : Store H} {f : Frame} {vs : List Val} {a : Nat} {r : Admin}
    {fi : FuncInst H} {code : Func} (hr : r.IsCallRef) (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (h : Diverges P host ⟨s, f, vals vs ++ [.ref (.func a), r]⟩) :
    ∃ vs₁ vs₂ ps rs, vs = vs₁ ++ vs₂ ∧ Validation.Expand fi.type (.func ps rs) ∧
      vs₂.length = ps.length ∧
      Diverges P host ⟨s, f, vals vs₁ ++ [.frame rs.length (Frame.forCall fi.module vs₂ code.locals)
        [.label rs.length [] (expression code.body)]]⟩ := by
  obtain ⟨b, hb, hd⟩ := h.unfold
  obtain ⟨vs₁, vs₂, ps, rs, hvs, he, hn, rfl⟩ := Step.callRef_wasm_inv hr hf hcode hb
  exact ⟨vs₁, vs₂, ps, rs, hvs, he, hn, hd⟩


/-! ## Divergence in a label or a call frame, under values and before a continuation -/

/-- The label's body runs to a stuck end, and the label around it, in place, diverges. -/
def DivLabelSeqAfter (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (f : Frame) (ws : List Val) (n : Nat) (cont : List Instr) (b rest : List Admin) : Prop :=
  ∃ cb : Config H, Steps P host ⟨s, f, b⟩ cb ∧ (∀ c', ¬ Step P host cb c') ∧
    Diverges P host ⟨cb.store, cb.frame, vals ws ++ [.label n cont cb.code] ++ rest⟩

/-- **Splitting a divergent run of a label in place**: the body diverges, or it runs to a
stuck end and the label around that end diverges. -/
theorem diverges_label_seq_split {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cont : List Instr} {b rest : List Admin}
    (h : Diverges P host ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩) :
    Diverges P host ⟨s, f, b⟩ ∨ DivLabelSeqAfter P host s f ws n cont b rest := by
  classical
  by_cases hA : DivLabelSeqAfter P host s f ws n cont b rest
  · exact .inr hA
  left
  refine Silmaril.InfiniteTrace.coinduct
    (fun c : Config H =>
      Diverges P host ⟨c.store, c.frame, vals ws ++ [.label n cont c.code] ++ rest⟩ ∧
      ¬ DivLabelSeqAfter P host c.store c.frame ws n cont c.code rest) ?_ (a := ⟨s, f, b⟩) ⟨h, hA⟩
  rintro ⟨s, f, b⟩ ⟨hd, hna⟩
  dsimp only at hd hna
  by_cases hb : ∃ c', Step P host ⟨s, f, b⟩ c'
  · obtain ⟨c', hc', hd'⟩ := hd.unfold
    obtain ⟨c₀, h₀, rfl⟩ := Step.ctx_in_seq (X := .label n cont b) trivial (by simpa using hc')
    rcases Step.label_inv h₀ with ⟨s', f', b', hin, rfl⟩ | ⟨out, hex, -⟩
    · refine ⟨⟨s', f', b'⟩, hin, by simpa [Diverges] using hd', ?_⟩
      rintro ⟨cb, h₁, hs₁, hk⟩
      exact hna ⟨cb, .head hin h₁, hs₁, hk⟩
    · obtain ⟨c', hc'⟩ := hb
      exact (labelExit_stuck hex c' hc').elim
  · exact (hna ⟨⟨s, f, b⟩, .refl, fun c' h => hb ⟨c', h⟩, hd⟩).elim

/-- The callee body runs to a stuck end, and the frame and label around it, in place,
diverge. -/
def DivFrameSeqAfter (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (f F : Frame) (ws : List Val) (n : Nat) (b rest : List Admin) : Prop :=
  ∃ cb : Config H, Steps P host ⟨s, F, b⟩ cb ∧ (∀ c', ¬ Step P host cb c') ∧
    Diverges P host ⟨cb.store, f, vals ws ++ [.frame n cb.frame [.label n [] cb.code]] ++ rest⟩

/-- **Splitting a divergent run of a call frame in place**: the body diverges in its frame,
or it runs to a stuck end and the frame and label around that end diverge. -/
theorem diverges_frame_seq_split {s : Store H} {f F : Frame} {ws : List Val} {n : Nat}
    {b rest : List Admin}
    (h : Diverges P host ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩) :
    Diverges P host ⟨s, F, b⟩ ∨ DivFrameSeqAfter P host s f F ws n b rest := by
  classical
  by_cases hA : DivFrameSeqAfter P host s f F ws n b rest
  · exact .inr hA
  left
  refine Silmaril.InfiniteTrace.coinduct
    (fun c : Config H =>
      Diverges P host ⟨c.store, f, vals ws ++ [.frame n c.frame [.label n [] c.code]] ++ rest⟩ ∧
      ¬ DivFrameSeqAfter P host c.store f c.frame ws n c.code rest) ?_ (a := ⟨s, F, b⟩) ⟨h, hA⟩
  rintro ⟨s, F, b⟩ ⟨hd, hna⟩
  dsimp only at hd hna
  by_cases hb : ∃ c', Step P host ⟨s, F, b⟩ c'
  · obtain ⟨c', hc', hd'⟩ := hd.unfold
    obtain ⟨c₀, h₀, rfl⟩ := Step.ctx_in_seq (X := .frame n F [.label n [] b]) trivial
      (by simpa using hc')
    rcases Step.frame_inv h₀ with ⟨s', F', is', hin, rfl⟩ | ⟨out, hex, -⟩
    · rcases Step.label_inv hin with ⟨s'', F'', b', hin', he⟩ | ⟨out, hex, -⟩
      · simp only [Config.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        refine ⟨⟨s', F', b'⟩, hin', by simpa [Diverges] using hd', ?_⟩
        rintro ⟨cb, h₁, hs₁, hk⟩
        exact hna ⟨cb, .head hin' h₁, hs₁, hk⟩
      · obtain ⟨c', hc'⟩ := hb
        exact (labelExit_stuck hex c' hc').elim
    · exact (frameExit_label hex rfl).elim
  · exact (hna ⟨⟨s, F, b⟩, .refl, fun c' h => hb ⟨c', h⟩, hd⟩).elim

/-! ## Divergent runs pass through host-free steps -/

section Through

open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Exec

variable {o : GrowOracle}

/-- The interpreter's deep invariant of a plugged configuration holds of the fragment. -/
theorem deepAll_of_plug {Inv : Frame → Admin → Prop} (E : Sim.ActiveCtx) (c : Config H)
    (h : DeepAll Inv (E.plug c).frame (E.plug c).code) : DeepAll Inv c.frame c.code := by
  induction E generalizing c with
  | hole => exact h
  | suffix rest E ih => exact (Drv.deepAll_append.mp (ih _ h)).1
  | label n cont vs rest E ih =>
    have h1 := ih _ h
    simp only [Drv.deepAll_append, DeepAll, Drv.DeepAt] at h1
    exact h1.1.2.1.2
  | handler n cs vs rest E ih =>
    have h1 := ih _ h
    simp only [Drv.deepAll_append, DeepAll, Drv.DeepAt] at h1
    exact h1.1.2.1.2
  | frame n f vs rest E ih =>
    have h1 := ih _ h
    simp only [Drv.deepAll_append, DeepAll, Drv.DeepAt] at h1
    exact h1.1.2.1.2

theorem plug_store' (E : Sim.ActiveCtx) (c : Config H) : (E.plug c).store = c.store := by
  induction E generalizing c with
  | hole => rfl
  | suffix _ _ ih => exact ih _
  | label _ _ _ _ _ ih => exact ih _
  | handler _ _ _ _ _ ih => exact ih _
  | frame _ _ _ _ _ ih => exact ih _

theorem contextTyped_storeOk {c : Config H} (h : Sim.ContextTyped c) : StoreOk c.store := by
  obtain ⟨E, ts, h⟩ := h
  have hs := ConfigOk.storeOk h
  rwa [plug_store'] at hs

theorem contextTyped_deepAll {c : Config H} (h : Sim.ContextTyped c) :
    DeepAll IHeadInv c.frame c.code := by
  obtain ⟨E, ts, h⟩ := h
  exact deepAll_of_plug E c (ConfigOk.deepAll_iHeadInv h)

/-- A divergent configuration, or a host-free successor of a typed divergent one. -/
def ThroughQ (o : GrowOracle) (host : HostSemantics H) (d : Config H) : Prop :=
  Diverges (profile o) host d ∨
    ∃ K, Sim.ContextTyped K ∧ Diverges (profile o) host K ∧ Det.DStep o K d

theorem through_aux : ∀ (n : Nat) (K : Config H), sizeOf K.code = n → Sim.ContextTyped K →
    Diverges (profile o) host K → ∀ d, Det.DStep o K d →
      ∃ d', Step (profile o) host d d' ∧ ThroughQ o host d' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K hn ht hK d hd
  obtain ⟨b, hb, hdb⟩ := hK.unfold
  have hb' := dstep_of_step hd hb
  have hs := contextTyped_storeOk ht
  have hi := contextTyped_deepAll ht
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (stepI_complete hs hi hd)
  have hlb := Interp.step?_lag_at (interpHead_exact hs) _ K b x rfl rfl hi hb' hx
  have htb : Sim.ContextTyped b := ht.step hb'
  rcases stepI_maximal hs hi hd hx with _ | hdx
  · rcases stepI_maximal hs hi hb' hx with _ | hbx
    · obtain ⟨d', h', hd'⟩ := hdb.unfold
      exact ⟨d', h', .inl hd'⟩
    · rcases hlb with rfl | ⟨hlt, -⟩
      · obtain ⟨d', h', hd'⟩ := hdb.unfold
        exact ⟨d', h', .inl hd'⟩
      · exact ih _ (hn ▸ hlt) b rfl htb hdb _ hbx
  · refine ⟨x, Step.of_noHost host hdx, ?_⟩
    rcases stepI_maximal hs hi hb' hx with _ | hbx
    · exact .inl hdb
    · exact .inr ⟨b, htb, hdb, hbx⟩

/-- **A divergent run passes through every host-free step** of a typed configuration, in
the deterministic profile: host-free steps join within one step, and every other
successor than the interpreter's shrinks the code (`Interp.step?_lag_at`). -/
theorem diverges_through {K d : Config H} (ht : Sim.ContextTyped K)
    (hK : Diverges (profile o) host K) (hd : Det.DStep o K d) : Diverges (profile o) host d := by
  refine Silmaril.InfiniteTrace.coinduct (ThroughQ o host) ?_ (.inr ⟨K, ht, hK, hd⟩)
  rintro c (hc | ⟨K, ht, hK, hd⟩)
  · obtain ⟨d', h', hd'⟩ := hc.unfold
    exact ⟨d', h', .inl hd'⟩
  · exact through_aux _ K rfl ht hK c hd

/-- **A divergent run passes through every host-free run** of a typed configuration. -/
theorem diverges_through_steps {K T : Config H} (hpred : Relation.ReflTransGen (Det.DStep o) K T)
    (ht : Sim.ContextTyped K) (hK : Diverges (profile o) host K) : Diverges (profile o) host T := by
  induction hpred with
  | refl => exact hK
  | tail hst h ih =>
    exact diverges_through (ht.steps hst) ih h

end Through

end Silmaril.Proofs.Wasm.Abstract.HostCall
