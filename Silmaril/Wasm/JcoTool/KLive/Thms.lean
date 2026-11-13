module

public import Silmaril.Wasm.JcoTool.KLive.Defs
public import Silmaril.Wasm.JcoTool.KChain.Thms
public import Silmaril.Proofs.Wasm.JcoTool.KLive.Chain
public import Silmaril.Proofs.Wasm.JcoTool.KLive.Rest

/-!
# Networks of generated modules are live

Proofs in `Silmaril.Proofs.Wasm.JcoTool.KLive.{Term,Cases,Mod,Bound,Net,Main,Chain}`.

For any network whose transformer nodes may run as generated modules (`KNet.MNet`: modules
`KDrop.genD k N`, run by the callback runtime over the Component Model's drop behaviour), under
`MNet.Live` (well placed, numbered along its streams, a consistent specification, and the
kernels' bounds `KFits`):

* **`mreach_progress`** (no deadlock): every reachable system in which some node has not finished
  or some module has not exited can step. No module traps on the way: under the network's
  invariant every built-in it calls succeeds, every event it receives is well formed and is one
  it handles, and every case of its callback returns (`Cases`, `Mod`; a module's pending read
  holds at most its read size, `Bound`).
* **`no_infinite_mrun`** (termination): there is no infinite execution; every step decreases
  `2 · pot + #(modules resuming WR)` (`Term`).
* **`mexec_done`** (liveness under every scheduler): every maximal execution reaches a system where
  every node has finished and every module has exited (so every sink has dropped its input),
  and stays there.
* **Chains of any length** (`kchain_exec_correct`) and **tees** (`ktee_exec_correct`) of generated
  modules: every maximal execution ends with the sinks holding the kernels' composite
  (`KDrop.runs`, which `KChain.trsN` composes in the stream game: `kchain_exec_game`), and the two
  branches' runs.

* **`mreach_notrap`** (no trap, for every event): every invocation of a reachable module's
  callback, after `YIELD` or on *any* event its waitable set delivers, returns (`KRead.NoTrap`).
* **The pipe model of `KRead`** (`source xs → genD k N → sink`): **`genD_notrap_fits`** (round 2's
  frozen `KRead.Task.genD_notrap`, for every kernel whose bounds hold) and **`genD_reads_fits`**
  (`Task.genD_reads`, likewise, with `FlushNil`): the closed pipe finishes with
  `(trV k).run xs` and only that, and the open pipe (the source never ends its stream) comes to
  rest, with exactly `(trV k).runP xs` at the sink.

What is assumed: the kernels' bounds `KFits` (a kernel whose output or buffer can exceed the
module's fixed regions traps by design); as in `KDrop`, the fragment's semantics `dexec` for the
module's WebAssembly and the runtime delivering only well-formed events (`wfD`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KLive

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams.Net (NSt)
open Silmaril.Wasm.Component.Streams.Kernel (KM)
open Silmaril.Wasm.JcoTool.KCore (trV)
open Silmaril.Wasm.JcoTool.KDrop (runs)
open Silmaril.Wasm.JcoTool.KNet

/-- **No deadlock**: a reachable system that is not done can step. -/
theorem mreach_progress {M : MNet} (hL : M.Live) {m : MSys M.net} (h : MReach M m)
    (hnd : ¬ MDone M m) : MEnabled M m :=
  Silmaril.Proofs.Wasm.JcoTool.KLive.mprogress hL h hnd

/-- **Termination**: no infinite execution. -/
theorem no_infinite_mrun {M : MNet} (hL : M.Live) (r : Nat → MSys M.net) (h0 : MReach M (r 0)) :
    ¬ ∀ n, MStep M (r n) (r (n + 1)) := by
  obtain ⟨L, S⟩ := Silmaril.Proofs.Wasm.JcoTool.KLive.live_setting hL
  exact Silmaril.Proofs.Wasm.JcoTool.KLive.no_infinite_mrun hL.ok S r h0

/-- **Liveness under every scheduler**: every maximal execution finishes every node and module, and
stays there. -/
theorem mexec_done {M : MNet} (hL : M.Live) {r : Nat → MSys M.net} (hr : MExec M r) :
    ∃ n, ∀ j, n ≤ j → r j = r n ∧ MDone M (r n) :=
  Silmaril.Proofs.Wasm.JcoTool.KLive.mexec_done hL hr

/-! ## Chains and tees -/

/-- A chain of generated modules satisfies the hypotheses of liveness. -/
theorem kchainM_live {xs : List Val} {ks : List KM} {Nb : Nat → Nat}
    (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) (hws : ks.length < 2 ^ 26)
    (hfit : ∀ (i : Nat) (h : i < ks.length), KFits ks[i] (Nb i)) : (kchainM xs ks Nb).Live :=
  Silmaril.Proofs.Wasm.JcoTool.KLive.kchainM_live hN hws hfit

/-- **Every maximal execution of a chain of generated modules of any length ends with the sink
holding the kernels' composite.** -/
theorem kchain_exec_correct {xs : List Val} {ks : List KM} {Nb : Nat → Nat}
    (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) (hws : ks.length < 2 ^ 26)
    (hfit : ∀ (i : Nat) (h : i < ks.length), KFits ks[i] (Nb i))
    {r : Nat → MSys (kchainM xs ks Nb).net} (hr : MExec _ r) :
    ∃ n, ∀ j, n ≤ j → r j = r n ∧ (∃ b, ((r n).ns (snkM xs ks Nb)).rd = .gone b) ∧
      ((r n).ns (snkM xs ks Nb)).got = runs ks xs := by
  obtain ⟨n, hn⟩ := mexec_done (kchainM_live hN hws hfit) hr
  have hreach : MReach _ (r n) := by
    have hreachAll : ∀ j, MReach _ (r j) := by
      intro j
      induction j with
      | zero => rw [hr.1]; exact MSteps.refl _
      | succ j ih =>
        rcases hr.2 j with h | ⟨-, he⟩
        · exact MSteps.tail ih h
        · rw [he]; exact ih
    exact hreachAll n
  have hg : (kchainM xs ks Nb).gen (snkM xs ks Nb) = none := by
    unfold kchainM
    dsimp only
    split
    · rename_i h; exact absurd h.2 (by show ¬ (ks.length + 1 ≤ ks.length); omega)
    · rfl
  obtain ⟨b, hb⟩ := (((hn n le_rfl).2 (snkM xs ks Nb)).1 hg).1
  exact ⟨n, fun j hj => ⟨(hn j hj).1, ⟨b, hb⟩,
    Silmaril.Proofs.Wasm.JcoTool.KLive.kchainM_correct hN hws hreach hb⟩⟩

/-- **In the stream game**: the final output of a nonempty chain is the run of the composite
`KChain.trsN` (the transformer that plugged realisations of the kernels realise). -/
theorem kchain_exec_game {xs : List Val} {k : KM} {ks : List KM} {Nb : Nat → Nat}
    (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) (hws : (k :: ks).length < 2 ^ 26)
    (hfit : ∀ (i : Nat) (h : i < (k :: ks).length), KFits (k :: ks)[i] (Nb i))
    {r : Nat → MSys (kchainM xs (k :: ks) Nb).net} (hr : MExec _ r) :
    ∃ n, ∀ j, n ≤ j → r j = r n ∧
      ((r n).ns (snkM xs (k :: ks) Nb)).got = (KChain.trsN k ks).2.run xs ∧
      Silmaril.Wasm.Component.Streams.NetSem.pipeOut xs (KChain.trsN k ks).2
        ((r n).ns (snkM xs (k :: ks) Nb)).got := by
  obtain ⟨n, hn⟩ := kchain_exec_correct hN hws hfit hr
  have hg : ((r n).ns (snkM xs (k :: ks) Nb)).got = (KChain.trsN k ks).2.run xs :=
    ((hn n le_rfl).2.2).trans (KChain.trsN_run k ks xs).symm
  exact ⟨n, fun j hj => ⟨(hn j hj).1, hg,
    (Silmaril.Wasm.Component.Streams.NetSem.pipeOut_iff xs _ _).2 hg⟩⟩

/-- A tee of generated modules satisfies the hypotheses of liveness. -/
theorem ktee_live {xs : List Val} {k₁ k₂ : KM} {N₁ N₂ : Nat} (h₁ : 0 < N₁ ∧ N₁ ≤ 256)
    (h₂ : 0 < N₂ ∧ N₂ ≤ 256) (f₁ : KFits k₁ N₁) (f₂ : KFits k₂ N₂) : (ktee xs k₁ k₂ N₁ N₂).Live :=
  Silmaril.Proofs.Wasm.JcoTool.KLive.ktee_live h₁ h₂ f₁ f₂

/-- **Every maximal execution of a tee of generated modules ends with each sink holding its
branch's kernel run on the whole input.** -/
theorem ktee_exec_correct {xs : List Val} {k₁ k₂ : KM} {N₁ N₂ : Nat} (h₁ : 0 < N₁ ∧ N₁ ≤ 256)
    (h₂ : 0 < N₂ ∧ N₂ ≤ 256) (f₁ : KFits k₁ N₁) (f₂ : KFits k₂ N₂)
    {r : Nat → MSys (ktee xs k₁ k₂ N₁ N₂).net} (hr : MExec _ r) :
    ∃ n, ∀ j, n ≤ j → r j = r n ∧ ((r n).ns (4 : Fin 6)).got = (trV k₁).run xs ∧
      ((r n).ns (5 : Fin 6)).got = (trV k₂).run xs := by
  obtain ⟨n, hn⟩ := mexec_done (ktee_live h₁ h₂ f₁ f₂) hr
  have hreach : MReach _ (r n) := by
    have hreachAll : ∀ j, MReach _ (r j) := by
      intro j
      induction j with
      | zero => rw [hr.1]; exact MSteps.refl _
      | succ j ih =>
        rcases hr.2 j with h | ⟨-, he⟩
        · exact MSteps.tail ih h
        · rw [he]; exact ih
    exact hreachAll n
  obtain ⟨b₄, hb₄⟩ := (((hn n le_rfl).2 (4 : Fin 6)).1 rfl).1
  obtain ⟨b₅, hb₅⟩ := (((hn n le_rfl).2 (5 : Fin 6)).1 rfl).1
  obtain ⟨c₄, c₅⟩ := KNet.ktee_correct h₁ h₂ hreach
  exact ⟨n, fun j hj => ⟨(hn j hj).1, c₄ b₄ hb₄, c₅ b₅ hb₅⟩⟩

/-! ## No trap, and the pipe model of `KRead` -/

/-- **In a live network, no reachable module traps**, on any event its set delivers. -/
theorem mreach_notrap {M : MNet} (hL : M.Live) {m : MSys M.net} (h : MReach M m)
    {i : Fin M.net.k} {k : KM} {N : Nat} (hg : M.gen i = some (k, N)) :
    Silmaril.Wasm.JcoTool.KRead.NoTrap (Silmaril.Wasm.JcoTool.KDrop.genD k N) m.st (m.ms i) :=
  Silmaril.Proofs.Wasm.JcoTool.KLive.mreach_notrap hL h hg

/-- **The module of the pipe model never traps**, for every kernel
whose bounds hold. -/
theorem genD_notrap_fits {k : KM} {N : Nat} (hN : 0 < N ∧ N ≤ 256) (hfit : KFits k N) :
    Silmaril.Wasm.JcoTool.KRead.NoTrapAt k N := fun _ _ _ h =>
  Silmaril.Proofs.Wasm.JcoTool.KLive.pipe_notrap hN hfit h

/-- **The pipe model of `genD k N` reads as `trV k`**: its whole
outputs are exactly `(trV k).run xs` (some run finishes), and its outputs so far exactly
`(trV k).runP xs` (the open pipe comes to rest with them). -/
theorem genD_reads_fits {k : KM} {N : Nat} (hN : 0 < N ∧ N ≤ 256) (hfit : KFits k N)
    (hfl : Silmaril.Wasm.JcoTool.KRead.FlushNil k) :
    (Silmaril.Wasm.JcoTool.KRead.dropObs k N).Reads (trV k) :=
  Silmaril.Proofs.Wasm.JcoTool.KLive.pipe_reads hN hfit hfl

end Silmaril.Wasm.JcoTool.KLive
