module

public import Silmaril.Wasm.Component.Streams.NetSem.Defs
public import Silmaril.Wasm.Component.Streams.Live.Thms
public import Silmaril.Wasm.Component.Algebra.Pipe.Thms

/-!
# Chains and tees as equivalences, in networks and in the component algebra

The correctness theorems of `Pipes` (`pipe_correct`, `chain_correct`, `tee_correct`) say what a
sink holds *if* it finishes; with liveness (`Live.exec_done`) every maximal execution finishes,
and some maximal execution exists (`greedy`). So the outcomes of a network are exactly one value:

* `pipeOut_iff`: a pipe's outcome is `T.run xs`; `chainOut_iff`: `U.run (T.run xs)`;
  `teeOut_iff`: the pair of the two pipes' outcomes.
* `netEquiv_iff`: two transformer components are observationally equivalent in networks iff they
  have the same whole outputs (`Tr.EquivF`).
* **`chain_eq_comp`** restated as an equivalence: the network of two separate components has the
  outcomes of the network of the single fused component, `chainOut xs T U = pipeOut xs (T ⟫ U)`;
  `chain_congr` and `tee_congr`: replacing components by network-equivalent ones does not change
  the outcomes of a chain or of a tee.

**The link to the component algebra** (`VSem`, any compositional semantics, e.g. a
`StreamSem` or the algebra track's stream game): `chain_realizes` (plugging two realisations
realises `T ⟫ U`, whose network is the chain's), `chain_compEquiv` (a realisation of a transformer
equivalent to `T ⟫ U` is a component equivalent to the plug, and its pipe has the chain's
outcomes), **`equiv_compose`** (realisations of equivalent transformers compose to equivalent
components, and their chains have the same outcomes: *the composition of equivalent components is
equivalent*, in both semantics), and `tee_realizes` (the same for the branches of a tee).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.NetSem

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Live
open Silmaril.Wasm.Component.Streams.Pipes
open Silmaril.Proofs.Wasm.Component.Streams.Live (Setting exec_reach)

variable {σ τ σ' τ' : Type}

/-! ## Some execution finishes -/

open Classical in
/-- The greedy scheduler: any enabled step, until none is. -/
noncomputable def greedy (net : Network) : Nat → Sys net
  | 0 => init net
  | n + 1 => if h : Enabled net (greedy net n) then Classical.choose h else greedy net n

theorem exec_greedy (net : Network) : Exec net (greedy net) := by
  refine ⟨rfl, fun n => ?_⟩
  by_cases h : Enabled net (greedy net n)
  · left
    have e : greedy net (n + 1) = Classical.choose h := by simp [greedy, h]
    rw [e]
    exact Classical.choose_spec h
  · right
    exact ⟨h, by simp [greedy, h]⟩

/-- **The outcomes of a network with a unique final observation `v`** are `v`. -/
theorem outcomes_iff {α : Type} {net : Network} {L : Fin net.k → List Val} (S : Setting net L)
    {obs : Sys net → α} {v : α} (hv : ∀ s, Reach net s → s.AllDone → obs s = v) (a : α) :
    Outcomes net obs a ↔ a = v := by
  constructor
  · rintro ⟨r, hr, n, hd, rfl⟩
    exact hv _ (exec_reach hr n) hd
  · rintro rfl
    obtain ⟨n, -, hst⟩ := exec_done S (exec_greedy net)
    exact ⟨greedy net, exec_greedy net, n, (hst n (le_refl n)).2,
      hv _ (exec_reach (exec_greedy net) n) (hst n (le_refl n)).2⟩

/-! ## Pipes, chains, tees -/

theorem pipeOut_iff (xs : List Val) (T : Tr σ Val Val) (a : List Val) :
    pipeOut xs T a ↔ a = T.run xs :=
  outcomes_iff (pipe_setting xs T) (fun _ h hd => by
    obtain ⟨b, hb⟩ := (hd 2).1
    exact pipe_correct xs T h hb) a

theorem chainOut_iff (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) (a : List Val) :
    chainOut xs T U a ↔ a = U.run (T.run xs) :=
  outcomes_iff (chain_setting xs T U) (fun _ h hd => by
    obtain ⟨b, hb⟩ := (hd 3).1
    exact chain_correct xs T U h hb) a

theorem teeOut_iff (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) (a : List Val × List Val) :
    teeOut xs T U a ↔ a = (T.run xs, U.run xs) :=
  outcomes_iff (tee_setting xs T U) (fun _ h hd => by
    obtain ⟨b₁, hb₁⟩ := (hd 4).1
    obtain ⟨b₂, hb₂⟩ := (hd 5).1
    rw [(tee_correct xs T U h).1 b₁ hb₁, (tee_correct xs T U h).2 b₂ hb₂]) a

/-- **Network equivalence is equality of whole outputs.** -/
theorem netEquiv_iff (T : Tr σ Val Val) (U : Tr τ Val Val) : NetEquiv T U ↔ T.EquivF U := by
  constructor
  · intro h xs
    have h1 : pipeOut xs T (T.run xs) := (pipeOut_iff xs T _).2 rfl
    rw [h xs] at h1
    exact (pipeOut_iff xs U _).1 h1
  · intro h xs
    funext a
    exact propext ((pipeOut_iff xs T a).trans (by rw [h xs]; exact (pipeOut_iff xs U a).symm))

theorem NetEquiv.of_equiv {T : Tr σ Val Val} {U : Tr τ Val Val} (h : T.Equiv U) : NetEquiv T U :=
  (netEquiv_iff T U).2 fun xs => (h xs).2

/-- **`chain_eq_comp` as an equivalence**: a chain of two separate components has exactly the
outcomes of the single component running the fused transformer. -/
theorem chain_eq_comp (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) :
    chainOut xs T U = pipeOut xs (T.comp U) := by
  funext a
  exact propext ((chainOut_iff xs T U a).trans
    (by rw [← Tr.run_comp']; exact (pipeOut_iff xs (T.comp U) a).symm))

/-- **Congruence of chains**: network-equivalent components give chains with the same outcomes. -/
theorem chain_congr {T : Tr σ Val Val} {T' : Tr σ' Val Val} {U : Tr τ Val Val} {U' : Tr τ' Val Val}
    (hT : NetEquiv T T') (hU : NetEquiv U U') (xs : List Val) :
    chainOut xs T U = chainOut xs T' U' := by
  have hT' := (netEquiv_iff T T').1 hT
  have hU' := (netEquiv_iff U U').1 hU
  funext a
  exact propext ((chainOut_iff xs T U a).trans
    (by rw [hT' xs, hU' _]; exact (chainOut_iff xs T' U' a).symm))

/-- **A tee's outcome is the pair of its branches' pipe outcomes.** -/
theorem teeOut_pair (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) (a b : List Val) :
    teeOut xs T U (a, b) ↔ pipeOut xs T a ∧ pipeOut xs U b := by
  rw [teeOut_iff, pipeOut_iff, pipeOut_iff, Prod.mk.injEq]

/-- **Congruence of tees**: network-equivalent branches give tees with the same outcomes. -/
theorem tee_congr {T : Tr σ Val Val} {T' : Tr σ' Val Val} {U : Tr τ Val Val} {U' : Tr τ' Val Val}
    (hT : NetEquiv T T') (hU : NetEquiv U U') (xs : List Val) :
    teeOut xs T U = teeOut xs T' U' := by
  funext a
  obtain ⟨a₁, a₂⟩ := a
  exact propext ((teeOut_pair xs T U a₁ a₂).trans
    (by rw [hT xs, hU xs]; exact (teeOut_pair xs T' U' a₁ a₂).symm))

/-! ## The link to the component algebra -/

variable {M : Type} [CoreModule M] {C : CoreSem M} (V : VSem C)

/-- Plugging realises composition. -/
theorem VSem.Realizes.seq {c d : Comp M} {T : Tr σ Val Val} {U : Tr τ Val Val}
    (hc : V.Realizes c T) (hd : V.Realizes d U) : V.Realizes (Algebra.seq c d) (T.comp U) :=
  ⟨hc.1, (Algebra.sizes_seq c d).2.trans hd.2.1,
    by rw [Algebra.denU_seq, hc.2.2, hd.2.2, V.den_comp]⟩

/-- Realisations of equivalent transformers are equivalent components. -/
theorem VSem.Realizes.equiv {c d : Comp M} {T : Tr σ Val Val} {U : Tr τ Val Val}
    (hc : V.Realizes c T) (hd : V.Realizes d U) (h : T.Equiv U) : Algebra.CompEquiv C c d :=
  ⟨⟨hc.1.trans hd.1.symm, hc.2.1.trans hd.2.1.symm⟩, by rw [hc.2.2, hd.2.2, V.den_congr h]⟩

/-- **A plug of two realisations realises the fused transformer, which is what the chain network
of the two components computes.** -/
theorem chain_realizes {c d : Comp M} {T : Tr σ Val Val} {U : Tr τ Val Val}
    (hc : V.Realizes c T) (hd : V.Realizes d U) :
    V.Realizes (Algebra.seq c d) (T.comp U) ∧ ∀ xs, chainOut xs T U = pipeOut xs (T.comp U) :=
  ⟨VSem.Realizes.seq V hc hd, fun xs => chain_eq_comp xs T U⟩

/-- **A realisation of a transformer equivalent to `T ⟫ U`** is a component equivalent to the plug
of realisations of `T` and `U`, and its pipe has the outcomes of their chain. -/
theorem chain_compEquiv {ρ : Type} {c d e : Comp M} {T : Tr σ Val Val} {U : Tr τ Val Val}
    {W : Tr ρ Val Val} (hc : V.Realizes c T) (hd : V.Realizes d U) (he : V.Realizes e W)
    (hW : (T.comp U).Equiv W) :
    Algebra.CompEquiv C (Algebra.seq c d) e ∧ ∀ xs, chainOut xs T U = pipeOut xs W := by
  refine ⟨VSem.Realizes.equiv V (VSem.Realizes.seq V hc hd) he hW, fun xs => ?_⟩
  rw [chain_eq_comp]
  exact NetEquiv.of_equiv hW xs

/-- **The composition of equivalent components is equivalent**, in the algebra (`seq`) and in
networks (chains). -/
theorem equiv_compose {c c' d d' : Comp M} {T : Tr σ Val Val} {T' : Tr σ' Val Val}
    {U : Tr τ Val Val} {U' : Tr τ' Val Val} (hc : V.Realizes c T) (hc' : V.Realizes c' T')
    (hd : V.Realizes d U) (hd' : V.Realizes d' U') (hT : T.Equiv T') (hU : U.Equiv U') :
    Algebra.CompEquiv C (Algebra.seq c d) (Algebra.seq c' d') ∧
      ∀ xs, chainOut xs T U = chainOut xs T' U' :=
  ⟨Algebra.seq_congr (VSem.Realizes.equiv V hc hc' hT) (VSem.Realizes.equiv V hd hd' hU),
    chain_congr (NetEquiv.of_equiv hT) (NetEquiv.of_equiv hU)⟩

/-- **Tees**: realisations of equivalent branch transformers are equivalent components, and the
tee networks have the same outcomes. -/
theorem tee_realizes {c c' d d' : Comp M} {T : Tr σ Val Val} {T' : Tr σ' Val Val}
    {U : Tr τ Val Val} {U' : Tr τ' Val Val} (hc : V.Realizes c T) (hc' : V.Realizes c' T')
    (hd : V.Realizes d U) (hd' : V.Realizes d' U') (hT : T.Equiv T') (hU : U.Equiv U') :
    Algebra.CompEquiv C c c' ∧ Algebra.CompEquiv C d d' ∧
      ∀ xs, teeOut xs T U = teeOut xs T' U' :=
  ⟨VSem.Realizes.equiv V hc hc' hT, VSem.Realizes.equiv V hd hd' hU,
    tee_congr (NetEquiv.of_equiv hT) (NetEquiv.of_equiv hU)⟩

end Silmaril.Wasm.Component.Streams.NetSem
