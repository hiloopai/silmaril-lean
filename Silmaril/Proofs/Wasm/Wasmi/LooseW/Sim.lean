module

public import Silmaril.Proofs.Wasm.Wasmi.LooseW.SimCtx
public import Silmaril.Proofs.Wasm.Wasmi.LooseW.Stutter

@[expose] public section

/-!
# `fuseW`'s translated code is simulated by `LooseW`, with stuttering

The one-step simulation (`sim_main`) is by strong induction on the size of the left code, as
in `Silmaril.Proofs.Wasm.Wasmi.Sim`. The left code is `val* a es`, with `a` its first non-value:

* a `trap` or `THROW_REF` head (`kernel_case`): the same redex on the right, or a discard of
  values and following instructions (`trap-instrs`, `throw_ref-instrs`). The right discards
  its values and **one** instruction while the left keeps a non-empty rest, all of them when
  the left keeps none. When the right has a single instruction left and the left keeps a
  non-empty rest, the right **stutters**: the left code is smaller (`kernel_trap`,
  `kernel_throw`). This is where the `eqz` shape, three instructions against four, needs it;
* a translated shape (`group_case`): the left reads the local (`Step.localGet_inv`), the right
  takes `selectEitherW` at the same shape with the constant of the translation;
* a pointwise head (`pointwise_case`): `head_case`, lifted through the context.

`behaviours_subset`: every Core behaviour of an invocation of the translated store is a
`LooseW` behaviour of the same invocation of the source store, divergence included, by
`behavioursR_subset_of_stutter` with the size of the code as measure.

New proofs.
-/

namespace Silmaril.Proofs.Wasm.Wasmi.LooseW

open Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Wasmi Silmaril.Wasm.Wasmi.Fusion Silmaril.Wasm.Wasmi.LooseW Silmaril.Wasm.Atlas.Variant

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Kernel heads -/

/-- The redex results of a `trap` or `THROW_REF` head end in a kernel. -/
theorem kernel_shape {sL sL' : Store H} {f f' : Frame} {us : List Val} {k : Admin}
    {is' : List Admin} (hk : k = .trap ∨ k = .plain .throwRef)
    (hs : Execution.Core.Step P host ⟨sL, f, vals us ++ [k]⟩ ⟨sL', f', is'⟩) :
    ∃ Q k', (k' = .trap ∨ k' = .plain .throwRef) ∧ is' = vals Q ++ [k'] := by
  rcases hk with rfl | rfl
  · obtain ⟨-, -, p, -, q, -, -, he⟩ := Sim.Step.trap_redex_aux hs us rfl
    exact ⟨p ++ q, .trap, Or.inl rfl, he⟩
  · obtain ⟨-, -, ⟨p, -, q, a, -, -, he⟩ | ⟨-, u', -, he⟩⟩ :=
      Sim.Step.throwRef_redex_aux hs us rfl
    · dsimp only at he
      exact ⟨p ++ q ++ [.ref (.exn a)], .plain .throwRef, Or.inr rfl,
        by rw [he]; simp [vals, throwing, Val.toAdmin]⟩
    · exact ⟨u', .trap, Or.inl rfl, he⟩

/-- The redex of a `trap` or `THROW_REF` head: the same redex on the right. -/
theorem kernel_redex {sL sL' sR : Store H} {f f' : Frame} {ws us : List Val} {k : Admin}
    {es r is' wL : List Admin} (hst : StoreRel FR sL sR) (hk : k = .trap ∨ k = .plain .throwRef)
    (hlen : es = [] ↔ r = [])
    (hs : Execution.Core.Step P host ⟨sL, f, vals us ++ [k]⟩ ⟨sL', f', is'⟩) :
    Goal P host sL' sR f f' (vals (ws ++ us) ++ k :: r) wL (vals ws ++ is' ++ es) := by
  have hctx : ¬ k.IsCtx := by rcases hk with rfl | rfl <;> exact id
  have hcall : ¬ k.IsCallRef := by rcases hk with rfl | rfl <;> exact id
  obtain ⟨sR', hsR, hst'⟩ : ∃ sR', Execution.Core.Step P host ⟨sR, f, vals us ++ [k]⟩
      ⟨sR', f', is'⟩ ∧ StoreRel FR sL' sR' := Sim.Step.transport_storeRel hst hctx hcall hs
  obtain ⟨Q, k', hk', hQ⟩ : ∃ Q k', (k' = .trap ∨ k' = .plain .throwRef) ∧
      is' = vals Q ++ [k'] := kernel_shape hk hs
  have hl : LooseW.Step P host ⟨sR, f, vals ws ++ (vals us ++ [k]) ++ r⟩
      ⟨sR', f', vals ws ++ is' ++ r⟩ := loose_ctx (core hsR) ws r
  have hr : LRel (vals (ws ++ Q) ++ k' :: es) (vals (ws ++ Q) ++ k' :: r) :=
    LRel.vals_append _ (LRel.cut hk' hlen)
  refine ⟨sR', _, Or.inl (by simpa using hl), hst', ?_⟩
  rw [hQ]; simpa using hr

/-- The size of the code after a discard is smaller. -/
theorem sizeOf_discard (A : List Admin) {r₁ r₂ : List Admin} (hne : r₁ ≠ []) :
    sizeOf (A ++ r₂) < sizeOf (A ++ (r₁ ++ r₂)) := by
  have h₁ := sizeOf_append r₁ r₂
  obtain ⟨x, r₁, rfl⟩ := List.exists_cons_of_ne_nil hne
  have h₂ : sizeOf r₁ + 1 ≤ sizeOf (x :: r₁) := by simp only [List.cons.sizeOf_spec]; omega
  have h₃ : 1 ≤ sizeOf r₁ := by
    cases r₁ <;> simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec] <;> omega
  simpa using sizeOf_mid A [] (X := r₂) (Y := (x :: r₁) ++ r₂) (by omega)

/-! ### Discards

`trap-instrs` and `throw_ref-instrs` discard the values before a kernel `K` (`[trap]` or
`throwing x`) and some instructions after it. The right side matches with its values and one
instruction, or all of them, or stutters. The four cases are stated for any kernel with a
discard rule `hD` and a relation `hK` for the codes after it. -/

section Discard

variable {sL sR : Store H} {f : Frame} {K : List Admin} {ws us : List Val}
  {r₁ r₂ r : List Admin}

/-- The code with the right side's discarded part in the middle. -/
theorem discard_code (u rest : List Admin) (h : r = u ++ rest) :
    vals (ws ++ us) ++ K ++ r = vals ws ++ (vals us ++ K ++ u) ++ rest := by
  rw [h]; simp

/-- Everything after the kernel is discarded on the left: the right discards all. -/
theorem discard_all (hst : StoreRel FR sL sR)
    (hD : ∀ (vs : List Val) (rest : List Admin), vs ≠ [] ∨ rest ≠ [] →
      Execution.Core.Step P host ⟨sR, f, vals vs ++ K ++ rest⟩ ⟨sR, f, K⟩)
    (hK : ∀ {l r' : List Admin}, (l = [] ↔ r' = []) →
      LRel (vals ws ++ K ++ l) (vals ws ++ K ++ r'))
    (hne : us ≠ [] ∨ r ≠ []) :
    Goal P host sL sR f f (vals (ws ++ us) ++ K ++ r) (vals (ws ++ us) ++ K ++ r₁)
      (vals ws ++ K ++ []) := by
  have hs : LooseW.Step P host ⟨sR, f, vals ws ++ (vals us ++ K ++ r) ++ []⟩
      ⟨sR, f, vals ws ++ K ++ []⟩ := loose_ctx (core (hD us r hne)) ws []
  have hc : vals (ws ++ us) ++ K ++ r = vals ws ++ (vals us ++ K ++ r) ++ [] :=
    discard_code r [] (by simp)
  exact ⟨sR, vals ws ++ K ++ [], Or.inl (hc ▸ hs), hst, hK Iff.rfl⟩

/-- Values before the kernel: the right discards them and nothing after. -/
theorem discard_vals (hst : StoreRel FR sL sR)
    (hD : ∀ (vs : List Val) (rest : List Admin), vs ≠ [] ∨ rest ≠ [] →
      Execution.Core.Step P host ⟨sR, f, vals vs ++ K ++ rest⟩ ⟨sR, f, K⟩)
    (hK : ∀ {l r' : List Admin}, (l = [] ↔ r' = []) →
      LRel (vals ws ++ K ++ l) (vals ws ++ K ++ r'))
    (hus : us ≠ []) (hlen : r₂ = [] ↔ r = []) :
    Goal P host sL sR f f (vals (ws ++ us) ++ K ++ r) (vals (ws ++ us) ++ K ++ r₁)
      (vals ws ++ K ++ r₂) := by
  have hs : LooseW.Step P host ⟨sR, f, vals ws ++ (vals us ++ K ++ []) ++ r⟩
      ⟨sR, f, vals ws ++ K ++ r⟩ := loose_ctx (core (hD us [] (Or.inl hus))) ws r
  have hc : vals (ws ++ us) ++ K ++ r = vals ws ++ (vals us ++ K ++ []) ++ r :=
    discard_code [] r (by simp)
  exact ⟨sR, vals ws ++ K ++ r, Or.inl (hc ▸ hs), hst, hK hlen⟩

/-- No values, two or more instructions on the right: it discards one. -/
theorem discard_one (hst : StoreRel FR sL sR)
    (hD : ∀ (vs : List Val) (rest : List Admin), vs ≠ [] ∨ rest ≠ [] →
      Execution.Core.Step P host ⟨sR, f, vals vs ++ K ++ rest⟩ ⟨sR, f, K⟩)
    (hK : ∀ {l r' : List Admin}, (l = [] ↔ r' = []) →
      LRel (vals ws ++ K ++ l) (vals ws ++ K ++ r'))
    {y : Admin} {r' : List Admin} (hlen : r₂ = [] ↔ r' = []) :
    Goal P host sL sR f f (vals (ws ++ []) ++ K ++ (y :: r')) (vals (ws ++ []) ++ K ++ r₁)
      (vals ws ++ K ++ r₂) := by
  have hs : LooseW.Step P host ⟨sR, f, vals ws ++ (vals [] ++ K ++ [y]) ++ r'⟩
      ⟨sR, f, vals ws ++ K ++ r'⟩ := loose_ctx (core (hD [] [y] (Or.inr (by simp)))) ws r'
  have hc : vals (ws ++ []) ++ K ++ (y :: r') = vals ws ++ (vals [] ++ K ++ [y]) ++ r' :=
    discard_code [y] r' rfl
  exact ⟨sR, vals ws ++ K ++ r', Or.inl (hc ▸ hs), hst, hK hlen⟩

/-- No values, one instruction on the right, a non-empty rest on the left: the right
stutters, and the left code is smaller. -/
theorem discard_stutter (hst : StoreRel FR sL sR)
    (hK : ∀ {l r' : List Admin}, (l = [] ↔ r' = []) →
      LRel (vals ws ++ K ++ l) (vals ws ++ K ++ r'))
    {y : Admin} (hr₁ : r₁ ≠ []) (h₂ : r₂ ≠ []) :
    Goal P host sL sR f f (vals (ws ++ []) ++ K ++ [y]) (vals (ws ++ []) ++ K ++ (r₁ ++ r₂))
      (vals ws ++ K ++ r₂) := by
  have hlt : sizeOf (vals ws ++ K ++ r₂) < sizeOf (vals (ws ++ []) ++ K ++ (r₁ ++ r₂)) := by
    simpa using sizeOf_discard (vals ws ++ K) (r₂ := r₂) hr₁
  have hr : LRel (vals ws ++ K ++ r₂) (vals (ws ++ []) ++ K ++ [y]) := by
    simpa using hK (l := r₂) (r' := [y]) (by simp [h₂])
  exact ⟨sR, _, Or.inr ⟨rfl, rfl, rfl, hlt⟩, hst, hr⟩

/-- **A discard after a kernel**, in all four cases. -/
theorem kernel_discard (hst : StoreRel FR sL sR)
    (hD : ∀ (vs : List Val) (rest : List Admin), vs ≠ [] ∨ rest ≠ [] →
      Execution.Core.Step P host ⟨sR, f, vals vs ++ K ++ rest⟩ ⟨sR, f, K⟩)
    (hK : ∀ {l r' : List Admin}, (l = [] ↔ r' = []) →
      LRel (vals ws ++ K ++ l) (vals ws ++ K ++ r'))
    (hlen : r₁ ++ r₂ = [] ↔ r = []) (hne : us ≠ [] ∨ r₁ ≠ []) :
    Goal P host sL sR f f (vals (ws ++ us) ++ K ++ r) (vals (ws ++ us) ++ K ++ (r₁ ++ r₂))
      (vals ws ++ K ++ r₂) := by
  by_cases h₂ : r₂ = []
  · show Goal P host sL sR f f _ _ (vals ws ++ K ++ r₂)
    have hne' : us ≠ [] ∨ r ≠ [] := hne.imp id fun h h' => h (by simpa [h₂] using hlen.mpr h')
    rw [h₂]
    exact discard_all hst hD hK hne'
  · have hr : r ≠ [] := fun h => h₂ (List.append_eq_nil_iff.mp (hlen.mpr h)).2
    by_cases hus : us = []
    · subst hus
      obtain ⟨y, r', rfl⟩ := List.exists_cons_of_ne_nil hr
      by_cases hr' : r' = []
      · show Goal P host sL sR f f _ _ (vals ws ++ K ++ r₂)
        rw [hr']
        exact discard_stutter hst hK (hne.resolve_left (by simp)) h₂
      · exact discard_one hst hD hK (by simp [h₂, hr'])
    · exact discard_vals hst hD hK hus (by simp [h₂, hr])

end Discard

/-- **`trap-instrs`**: a discard after `[trap]`. -/
theorem kernel_trap {sL sR : Store H} {f : Frame} {ws us : List Val} {r₁ r₂ r : List Admin}
    (hst : StoreRel FR sL sR) (hlen : r₁ ++ r₂ = [] ↔ r = []) (hne : us ≠ [] ∨ r₁ ≠ []) :
    Goal P host sL sR f f (vals (ws ++ us) ++ .trap :: r)
      (vals (ws ++ us) ++ .trap :: (r₁ ++ r₂)) (vals ws ++ [.trap] ++ r₂) := by
  have hK : ∀ {l r' : List Admin}, (l = [] ↔ r' = []) →
      LRel (vals ws ++ [.trap] ++ l) (vals ws ++ [.trap] ++ r') := fun h => by
    simpa using LRel.vals_append ws (LRel.cut (Or.inl rfl) h)
  have h := kernel_discard (P := P) (host := host) (sL := sL) (f := f) (us := us) hst
    (fun vs rest hne => Step.trapInstrs hne) hK hlen hne
  simpa using h

/-- **`throw_ref-instrs`**: a discard after `throwing x`. -/
theorem kernel_throw {sL sR : Store H} {f : Frame} {ws us : List Val} {x : Nat}
    {r₁ r₂ r : List Admin} (hst : StoreRel FR sL sR) (hlen : r₁ ++ r₂ = [] ↔ r = [])
    (hne : us ≠ [] ∨ r₁ ≠ []) :
    Goal P host sL sR f f (vals (ws ++ us ++ [.ref (.exn x)]) ++ .plain .throwRef :: r)
      (vals (ws ++ us ++ [.ref (.exn x)]) ++ .plain .throwRef :: (r₁ ++ r₂))
      (vals ws ++ throwing x ++ r₂) := by
  have hK : ∀ {l r' : List Admin}, (l = [] ↔ r' = []) →
      LRel (vals ws ++ throwing x ++ l) (vals ws ++ throwing x ++ r') := fun h => by
    have h' := LRel.vals_append (ws ++ [.ref (.exn x)]) (LRel.cut (Or.inr rfl) h)
    simpa only [vals, throwing, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.cons_append, List.nil_append, Val.toAdmin] using h'
  have h := kernel_discard (P := P) (host := host) (sL := sL) (f := f) (us := us) hst
    (fun vs rest hne => Step.throwRefInstrs hne) hK hlen hne
  simpa [vals, throwing, Val.toAdmin] using h

/-- **A `trap` or `THROW_REF` head.** -/
theorem kernel_case {sL sL' sR : Store H} {f f' : Frame} {V : List Val} {k : Admin}
    {es r wL' : List Admin} (hst : StoreRel FR sL sR) (hk : k = .trap ∨ k = .plain .throwRef)
    (hlen : es = [] ↔ r = [])
    (h : Execution.Core.Step P host ⟨sL, f, vals V ++ k :: es⟩ ⟨sL', f', wL'⟩) :
    Goal P host sL' sR f f' (vals V ++ k :: r) (vals V ++ k :: es) wL' := by
  have hka : k.val? = none := by rcases hk with rfl | rfl <;> rfl
  rcases Sim.Step.split_head hka h with ⟨ws, us, is', rfl, hs, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, r₁, r₂, rfl, rfl, hne, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, x, r₁, r₂, rfl, rfl, hne, rfl⟩
  · exact kernel_redex hst hk hlen hs
  · exact kernel_trap hst hlen hne
  · exact kernel_throw hst hlen hne

/-! ## Translated shapes -/

/-- The constant of a shape is `if b then 1 else 0` for some `b`. -/
theorem cond_eq (g : FuseShape) : ∃ b : Bool, (if b then 1 else 0 : BitVec 32) = g.cond := by
  cases g
  · exact ⟨false, rfl⟩
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩
  · exact ⟨true, rfl⟩
  · exact ⟨true, rfl⟩

/-- **A translated shape**: the left reads the local, the right takes `selectEitherW`. -/
theorem group_case {sL sL' sR : Store H} {f f' : Frame} {V : List Val} {g : FuseShape}
    {x : LocalIdx} {t : Option (List ValType)} {l r wL wL' : List Admin}
    (hst : StoreRel FR sL sR) (hl : LRel l r)
    (h : Execution.Core.Step P host
      ⟨sL, f, vals V ++ .plain (.localGet x) ::
        ([.plain .drop, .plain (.intConst .i32 g.cond), .plain (.select t)] ++ l)⟩
      ⟨sL', f', wL'⟩) :
    Goal P host sL' sR f f' (vals V ++ (expression (g.src x t) ++ r)) wL wL' := by
  rcases Sim.Step.split_head rfl h with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨hk, -⟩ | ⟨hk, -⟩
  · obtain ⟨rfl, rfl, v, hv, rfl⟩ := Silmaril.Proofs.Wasm.Wasmi.Step.localGet_inv hs
    obtain ⟨b, hb⟩ := cond_eq g
    have hq : Quirk ⟨sR, f', expression (g.src x t)⟩
        ⟨sR, f', [v.toAdmin, .plain .drop, .plain (.intConst .i32 g.cond), .plain (.select t)]⟩ :=
      hb ▸ Quirk.selectEither g b hv
    refine ⟨sR, vals (ws ++ us) ++ [v.toAdmin, .plain .drop, .plain (.intConst .i32 g.cond),
      .plain (.select t)] ++ r, Or.inl ?_, hst, ?_⟩
    · have := Ctx.instrs (vs := ws ++ us) (rest := r) (Ctx.base hq)
      exact Or.inr (by simpa using this)
    · have := LRel.vals_append (ws ++ us)
        ((LRel.refl [v.toAdmin, .plain .drop, .plain (.intConst .i32 g.cond),
          .plain (.select t)]).append hl)
      simpa using this
  · cases hk
  · cases hk

/-! ## The simulation -/

/-- A pointwise head that is not a kernel. -/
theorem pointwise_case (hhost : HostRespects FR host) {m : Nat}
    (ihm : ∀ k < m, SimIH P host k) {sL sL' sR : Store H} {f f' : Frame} {V : List Val}
    {a b : Admin} {es r wL' : List Admin} (hm : sizeOf (vals V ++ a :: es) < m)
    (ha : a.val? = none) (hk : ¬ (a = .trap ∨ a = .plain .throwRef)) (hst : StoreRel FR sL sR)
    (hab : ARel a b) (hl : LRel es r)
    (h : Execution.Core.Step P host ⟨sL, f, vals V ++ a :: es⟩ ⟨sL', f', wL'⟩) :
    Goal P host sL' sR f f' (vals V ++ b :: r) (vals V ++ a :: es) wL' := by
  rcases Sim.Step.split_head ha h with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · have hlt : sizeOf a < m :=
      Nat.lt_trans (List.sizeOf_lt_of_mem (by simp : a ∈ vals (ws ++ us) ++ a :: es)) hm
    obtain ⟨sR', isR, hstep | ⟨rfl, rfl, rfl, hsz⟩, hst', hrel⟩ :=
      head_case hhost (ihm _ hlt) hst hab hs
    · have hl' : LooseW.Step P host ⟨sR, f, vals ws ++ (vals us ++ [b]) ++ r⟩
          ⟨sR', f', vals ws ++ isR ++ r⟩ := loose_ctx hstep ws r
      exact ⟨sR', _, Or.inl (by simpa using hl'), hst', (LRel.vals_append ws hrel).append hl⟩
    · refine ⟨sR', _, Or.inr ⟨rfl, rfl, by simp, ?_⟩, hst',
        (LRel.vals_append ws hrel).append hl⟩
      simpa using sizeOf_mid (vals ws) es hsz
  · exact absurd (Or.inl rfl) hk
  · exact absurd (Or.inr rfl) hk

/-- **The one-step simulation**, by strong induction on the size of the left code. -/
theorem sim_main (hhost : HostRespects FR host) : ∀ m, SimIH P host m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro sL sL' sR f f' wL wL' R hm h hst hw
  obtain ⟨V, a, es, ha, rfl⟩ := exists_head_of_not_all h.not_all_isVal
  obtain ⟨R₀, rfl, h₀⟩ := LRel.peel V hw
  by_cases hk : a = .trap ∨ a = .plain .throwRef
  · obtain ⟨r, rfl, hlen⟩ := h₀.kernel_inv hk
    exact kernel_case hst hk hlen h
  · rcases h₀.cons_inv with ⟨b, r, rfl, hab, hl⟩ | ⟨g, x, t, l, r, rfl, rfl, rfl, hl⟩ |
        ⟨hk', -⟩
    · exact pointwise_case hhost ihm hm ha hk hst hab hl h
    · exact group_case hst hl h
    · exact absurd hk' hk

/-! ## Behaviours -/

/-- The simulation relation on configurations. -/
def SimR (c d : Config H) : Prop :=
  c.frame = d.frame ∧ StoreRel FR c.store d.store ∧ LRel c.code d.code

/-- The simulation is a stuttering simulation, with the size of the code as measure. -/
theorem stutterStep (hhost : HostRespects FR host) :
    StutterStep (Execution.Core.Step P host) (LooseW.Step P host) SimR
      (fun c => sizeOf c.code) := by
  intro c c' d hs hr
  obtain ⟨sL, f, wL⟩ := c
  obtain ⟨sL', f', wL'⟩ := c'
  obtain ⟨sR, g, R⟩ := d
  obtain ⟨hfg, hst, hw⟩ := hr
  dsimp only at hfg hst hw
  subst hfg
  obtain ⟨sR', R', hl | ⟨hs₁, hf₁, hR₁, hlt⟩, hst', hr'⟩ :=
    sim_main hhost _ (Nat.lt_succ_self _) hs hst hw
  · exact ⟨⟨sR', f', R'⟩, ⟨rfl, hst', hr'⟩, Or.inl hl⟩
  · refine ⟨⟨sR', f', R'⟩, ⟨rfl, hst', hr'⟩, Or.inr ⟨?_, hlt⟩⟩
    subst hs₁ hf₁ hR₁; rfl

/-- **The wider fusion's behaviours are `LooseW` behaviours**: every Core behaviour of an
invocation of the translated store is a `LooseW` behaviour of the same invocation of the source
store. -/
theorem behaviours_subset (hhost : HostRespects FR host) (s : Store H) (a : Nat)
    (vs : List Val) :
    behaviours P host (fuseStoreW s) a vs ⊆ behavioursR (LooseW.Step P host) (invoke s a vs) := by
  refine behavioursR_subset_of_stutter (stutterStep hhost) ?_ ?_
  · intro c d r hr hc
    have h := hr.2.2
    rw [hc] at h
    exact h.result_inv
  · refine ⟨?_, ?_, ?_⟩
    · rw [invoke_fuseStoreW]
    · rw [invoke_fuseStoreW]; exact storeRel_fuseStoreW s
    · rw [invoke_fuseStoreW]; exact LRel.refl _

end Silmaril.Proofs.Wasm.Wasmi.LooseW
