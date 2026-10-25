module

public import Silmaril.Wasm.Binaryen.Pass.RUMESim.HeadSim
public import Silmaril.Wasm.SingleThreaded.Determinism.Join

@[expose] public section

/-! # Simulation under address maps: lockstep simulation

Every step of side `A` from related configurations has a matching step of side
`B` (`sim1`), hence every run (`sim_steps`) and every divergence
(`sim_diverges`), and related results are equal (`ConfRel.result`).
-/

namespace Silmaril.Wasm.Binaryen.RUMESim

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P : Profile}

theorem nonempty_of_length {α β : Type} {u : List α} {u' : List β} (hl : u'.length = u.length)
    (h : u ≠ []) : u' ≠ [] := by
  intro h'
  apply h
  rw [← List.length_eq_zero_iff, ← hl, h']
  rfl

/-- **One step**, by induction on the size of the code. -/
theorem sim {X : SimCtx} (hX : X.WF) : ∀ (n : Nat) (S : Store H) (f : Frame) (code : List Admin)
    (c : Config H), sizeOf code < n → Step P noHost ⟨S, f, code⟩ c →
    ∀ (T : Store H) (f' : Frame) (code' : List Admin) (m : Mode),
    StoreRel X S T → FrameRel X m f f' → CodeR X m code code' →
    ∃ c', Step P noHost ⟨T, f', code'⟩ c' ∧ ConfRel X m c c'
  | 0, _, _, _, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, S, f, code, c, hn, hst => by
    intro T f' code' m hS hf hc
    have ih : ∀ (S₁ : Store H) (fi : Frame) (body : List Admin) (c₁ : Config H),
        sizeOf body < sizeOf code → Step P noHost ⟨S₁, fi, body⟩ c₁ →
        ∀ (T₁ : Store H) (fi' : Frame) (body' : List Admin) (m' : Mode),
        StoreRel X S₁ T₁ → FrameRel X m' fi fi' → CodeR X m' body body' →
        ∃ c', Step P noHost ⟨T₁, fi', body'⟩ c' ∧ ConfRel X m' c₁ c' :=
      fun S₁ fi body c₁ hlt => sim hX n S₁ fi body c₁ (by omega)
    rcases Step.decomp hst with hd | hb
    · have hd' : HeadDec P S f code c := hd
      obtain ⟨vs, args, e, rest, c₀, -, hcode, hh, rfl⟩ := fnv_headDec hd'
      subst hcode
      have he0 : e.val? = none := hh.good.val_none
      have hc' : CodeR X m (vals (vs ++ args) ++ e :: rest) code' := by simpa using hc
      rcases CodeR.split_fnv he0 hc' with ⟨e', rest', rfl, hV, he, hrest⟩ |
          ⟨V₀, a, b, d, rest', hV0, rfl, rfl, hV, hab, hrest⟩
      · obtain ⟨c₀', hst', hrel⟩ := head_sim hX
          (fun S₁ fi body c₁ hlt => ih S₁ fi body c₁ (lt_trans hlt sizeOf_lt_code)) hh
          (fun v hv => hV v (by simp [hv])) he hS hf
        refine ⟨⟨c₀'.store, c₀'.frame, vals vs ++ c₀'.code ++ rest'⟩, ?_, hrel.1, hrel.2.1, ?_⟩
        · have := lift_instrs vs rest' ⟨T, f', vals args ++ [e']⟩ c₀' hst'
          simpa using this
        · exact CodeR.append (CodeR.append (CodeR.ofVals (fun v hv => hV v (by simp [hv])))
            hrel.2.2) hrest
      · obtain ⟨vs₂, r, rfl⟩ := head_callRefType_args hh
        have h12 : vs ++ vs₂ = V₀ ∧ Val.ref r = Val.ref (.func a) := by
          rw [← List.append_assoc] at hV0
          exact append_singleton_inj.1 hV0
        obtain ⟨h1, h2⟩ := h12
        cases h2
        subst h1
        obtain ⟨c₀', hst', hrel⟩ :=
          head_sim_pair hX hh (fun v hv => hV v (by simp [hv])) hab hS hf
        refine ⟨⟨c₀'.store, c₀'.frame, vals vs ++ c₀'.code ++ rest'⟩, ?_, hrel.1, hrel.2.1, ?_⟩
        · have := lift_instrs vs rest' ⟨T, f', vals vs₂ ++ [.ref (.func b), .callRefType d]⟩ c₀' hst'
          simpa using this
        · exact CodeR.append (CodeR.append (CodeR.ofVals (fun v hv => hV v (by simp [hv])))
            hrel.2.2) hrest
    · have hb' : Bubble S f code c := hb
      obtain ⟨p, q, u, r, hqu, ⟨-, hcode, rfl⟩ | ⟨a, -, hcode, rfl⟩⟩ := fnv_bubble hb'
      · subst hcode
        obtain ⟨x', R', rfl, hV, hx, hR⟩ := CodeR.split_nc hc rfl (by simp)
        rw [ARel.trap_inv hx]
        obtain ⟨u', r', rfl, hlen, hr⟩ := CodeR.split_app hR
        have hne : q ≠ [] ∨ u' ≠ [] := by
          rcases hqu with h | h
          · exact .inl h
          · exact .inr (nonempty_of_length hlen h)
        have hst' : Step P noHost ⟨T, f', vals q ++ [.trap] ++ u'⟩ ⟨T, f', [.trap]⟩ :=
          .trapInstrs hne
        have := lift_instrs p r' _ _ hst'
        refine ⟨⟨T, f', vals p ++ [.trap] ++ r'⟩, by simpa using this, hS, hf, ?_⟩
        exact CodeR.append (CodeR.append (CodeR.ofVals (fun v hv => hV v (by simp [hv])))
          CodeR.trap) hr
      · subst hcode
        obtain ⟨x', R', rfl, hV, hx, hR⟩ := CodeR.split_nc hc rfl (by simp)
        obtain rfl := ARel.plain_simple rfl hx
        obtain ⟨u', r', rfl, hlen, hr⟩ := CodeR.split_app hR
        have hne : q ≠ [] ∨ u' ≠ [] := by
          rcases hqu with h | h
          · exact .inl h
          · exact .inr (nonempty_of_length hlen h)
        have hst' : Step P noHost ⟨T, f', vals q ++ throwing a ++ u'⟩ ⟨T, f', throwing a⟩ :=
          .throwRefInstrs hne
        have := lift_instrs p r' _ _ hst'
        refine ⟨⟨T, f', vals p ++ throwing a ++ r'⟩, by simpa [Val.toAdmin] using this, hS, hf, ?_⟩
        exact CodeR.append (CodeR.append (CodeR.ofVals (fun v hv => hV v (by simp [hv])))
          (CodeR.throwing a)) hr

/-- One step of related configurations. -/
theorem sim1 {X : SimCtx} (hX : X.WF) {m : Mode} {c d c' : Config H} (h : Step P noHost c d)
    (hc : ConfRel X m c c') : ∃ d', Step P noHost c' d' ∧ ConfRel X m d d' := by
  rcases c with ⟨S, f, code⟩
  rcases c' with ⟨T, f', code'⟩
  exact sim hX _ S f code d (Nat.lt_succ_self _) h T f' code' m hc.1 hc.2.1 hc.2.2

/-- Runs of related configurations. -/
theorem sim_steps {X : SimCtx} (hX : X.WF) {m : Mode} {c d : Config H}
    (h : Steps P noHost c d) : ∀ {c' : Config H}, ConfRel X m c c' →
    ∃ d', Steps P noHost c' d' ∧ ConfRel X m d d' := by
  induction h with
  | refl => exact fun hc => ⟨_, .refl, hc⟩
  | tail _ hst ih =>
    intro c' hc
    obtain ⟨e', h1, h2⟩ := ih hc
    obtain ⟨d', h3, h4⟩ := sim1 hX hst h2
    exact ⟨d', h1.tail h3, h4⟩

/-- Divergence of related configurations. -/
theorem sim_diverges {X : SimCtx} (hX : X.WF) {m : Mode} {c c' : Config H}
    (h : Diverges P noHost c) (hc : ConfRel X m c c') : Diverges P noHost c' := by
  refine InfiniteTrace.coinduct (fun d' => ∃ d, ConfRel X m d d' ∧ InfiniteTrace (Step P noHost) d)
    ?_ ⟨c, hc, h⟩
  rintro d' ⟨d, hd, hinf⟩
  obtain ⟨e, hde, hinf'⟩ := hinf.unfold
  obtain ⟨e', hst, he⟩ := sim1 hX hde hd
  exact ⟨e', hst, e, he, hinf'⟩

/-- Related results are equal. -/
theorem ConfRel.result {X : SimCtx} {m : Mode} {c c' : Config H} {r : Result}
    (hc : ConfRel X m c c') (h : c.code = r.toAdmin) : c'.code = r.toAdmin := by
  have hcode := hc.2.2
  rw [h] at hcode
  cases r with
  | values vs => exact (CodeR.vals_inv (V := vs) hcode).1
  | throw a => exact CodeR.throwing_inv hcode
  | trap => exact CodeR.trap_inv hcode

end Silmaril.Wasm.Binaryen.RUMESim
