module

public import Silmaril.Proofs.Wasm.JcoTool.KLive.Trap
public import Silmaril.Proofs.Wasm.JcoTool.KLive.Chain

/-!
# The pipe harness of `KRead` is a chain with one module

`KRead.PSys`/`PStep` (a source, one generated module, a sink) is the network with modules
`kchainM xs [k] (fun _ => N)` (`pM`): `toM` maps a pipe state to a system (the module's node and
the other nodes' machines stay initial), every pipe step is a step of the system
(`pstep_mstep`), and every step of the system from the image of a pipe state is a closed pipe step
(`mstep_pstep`). So:

* **`pipe_notrap`**: the module of a reachable pipe (open or closed) never traps
  (`mreach_notrap`), given the kernel's bounds;
* **`pipe_whole`**: a finished closed pipe holds `(trV k).run xs`, and some run of the closed
  pipe finishes (`kchain_exec_correct` on a maximal execution).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KLive

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams.Drop (DStore)
open Silmaril.Wasm.Component.Streams.Net (NSt NStep rh wh)
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore (MS trV)
open Silmaril.Wasm.JcoTool.KDrop (DRStep genD runs kchain)
open Silmaril.Wasm.JcoTool.KNet
open Silmaril.Wasm.JcoTool.KLive
open Silmaril.Wasm.JcoTool.KRead (PSys PStep PSteps m₀ NoTrap obsOf dropObs)

/-- **The pipe as a network with modules**: the chain with the one kernel `k`. -/
abbrev pM (xs : List Val) (k : KM) (N : Nat) : MNet := kchainM xs [k] (fun _ => N)

/-- The machine of a node that is not a module. -/
def exM : MS := ⟨fun _ => 0, fun _ => 0, none, .exited⟩

/-- **A pipe state as a system**: node `0` the source, node `2` the sink, machine `1` the
module. -/
def toM {xs : List Val} {k : KM} {N : Nat} (c : PSys MS) : MSys (pM xs k N).net where
  st := c.st
  ns i := if i.val = 0 then c.src else if i.val = 2 then c.snk
    else NSt.init ((pM xs k N).net.node i)
  ms i := if i.val = 1 then c.m else exM

/-- The source, the module and the sink of the pipe. -/
def i0 (xs : List Val) (k : KM) (N : Nat) : Fin (pM xs k N).net.k := ⟨0, by simp [kchainM, kchain]⟩
def i1 (xs : List Val) (k : KM) (N : Nat) : Fin (pM xs k N).net.k := ⟨1, by simp [kchainM, kchain]⟩
def i2 (xs : List Val) (k : KM) (N : Nat) : Fin (pM xs k N).net.k := ⟨2, by simp [kchainM, kchain]⟩

variable {xs : List Val} {k : KM} {N : Nat}

theorem pM_k : (pM xs k N).net.k = 3 := rfl

theorem pM_gen0 : (pM xs k N).gen (i0 xs k N) = none := rfl

theorem pM_gen2 : (pM xs k N).gen (i2 xs k N) = none := rfl

theorem pM_gen1 : (pM xs k N).gen (i1 xs k N) = some (k, N) := rfl

theorem fin3 (i : Fin (pM xs k N).net.k) : i = i0 xs k N ∨ i = i1 xs k N ∨ i = i2 xs k N := by
  obtain ⟨v, hv⟩ := i
  have hv' : v < 3 := hv
  rcases v with _ | _ | _ | v
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)
  · omega

theorem toM_init : toM (xs := xs) (k := k) (N := N) (PSys.init xs k (m₀ k)) = MSys.init (pM xs k N) := by
  simp only [toM, MSys.init, PSys.init]
  congr 1
  · funext i
    rcases fin3 i with rfl | rfl | rfl <;> rfl
  · funext i
    rcases fin3 i with rfl | rfl | rfl <;> rfl

theorem toM_src {c : PSys MS} {st' : DStore} {x' : NSt KSt} :
    toM (xs := xs) (k := k) (N := N) { c with st := st', src := x' } =
      ⟨st', Function.update (toM (xs := xs) (k := k) (N := N) c).ns (i0 xs k N) x',
        (toM (xs := xs) (k := k) (N := N) c).ms⟩ := by
  simp only [toM]
  congr 1
  funext i
  rcases fin3 i with rfl | rfl | rfl <;> rfl

theorem toM_snk {c : PSys MS} {st' : DStore} {x' : NSt KSt} :
    toM (xs := xs) (k := k) (N := N) { c with st := st', snk := x' } =
      ⟨st', Function.update (toM (xs := xs) (k := k) (N := N) c).ns (i2 xs k N) x',
        (toM (xs := xs) (k := k) (N := N) c).ms⟩ := by
  simp only [toM]
  congr 1
  funext i
  rcases fin3 i with rfl | rfl | rfl <;> rfl

theorem toM_mod {c : PSys MS} {st' : DStore} {m' : MS} :
    toM (xs := xs) (k := k) (N := N) { c with st := st', m := m' } =
      ⟨st', (toM (xs := xs) (k := k) (N := N) c).ns,
        Function.update (toM (xs := xs) (k := k) (N := N) c).ms (i1 xs k N) m'⟩ := by
  simp only [toM]
  congr 1
  funext i
  rcases fin3 i with rfl | rfl | rfl <;> rfl

/-- **A pipe step is a step of the system.** -/
theorem pstep_mstep {op : Bool} {c c' : PSys MS} (h : PStep xs k op (DRStep (genD k N)) c c') :
    MStep (pM xs k N) (toM c) (toM c') := by
  cases h with
  | @src st' x' hn _ =>
    rw [toM_src (c := c) (st' := st') (x' := x')]
    exact MStep.node (s := toM c) (i0 xs k N) rfl hn
  | @snk st' x' hn =>
    rw [toM_snk (c := c) (st' := st') (x' := x')]
    exact MStep.node (s := toM c) (i2 xs k N) rfl hn
  | @mod st' m' hR =>
    rw [toM_mod (c := c) (st' := st') (m' := m')]
    exact MStep.mod (s := toM c) (i1 xs k N) (k := k) (N := N) rfl hR

/-- **A step of the system from a pipe state is a closed pipe step.** -/
theorem mstep_pstep {c : PSys MS} {m' : MSys (pM xs k N).net} (h : MStep (pM xs k N) (toM c) m') :
    ∃ c', m' = toM c' ∧ PStep xs k false (DRStep (genD k N)) c c' := by
  cases h with
  | node i hg hn =>
    rcases fin3 i with rfl | rfl | rfl
    · exact ⟨_, toM_src.symm, .src hn (fun h => by cases h)⟩
    · cases hg
    · exact ⟨_, toM_snk.symm, .snk hn⟩
  | mod i hg hd =>
    rcases fin3 i with rfl | rfl | rfl
    · cases hg
    · simp only [pM_gen1, Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨_, toM_mod.symm, .mod hd⟩
    · cases hg

/-- Runs of the pipe are runs of the system. -/
theorem psteps_mreach {op : Bool} {c : PSys MS}
    (h : PSteps xs k op (DRStep (genD k N)) (PSys.init xs k (m₀ k)) c) :
    MReach (pM xs k N) (toM c) := by
  induction h with
  | refl => rw [toM_init]; exact .refl _
  | tail _ h ih => exact ih.tail (pstep_mstep h)

/-- Runs of the system are runs of the closed pipe. -/
theorem mreach_psteps {m : MSys (pM xs k N).net} (h : MReach (pM xs k N) m) :
    ∃ c, m = toM c ∧ PSteps xs k false (DRStep (genD k N)) (PSys.init xs k (m₀ k)) c := by
  induction h with
  | refl => exact ⟨_, toM_init.symm, .refl⟩
  | tail _ h ih =>
    obtain ⟨c, rfl, hc⟩ := ih
    obtain ⟨c', rfl, h'⟩ := mstep_pstep h
    exact ⟨c', rfl, hc.tail h'⟩

/-- The pipe satisfies the hypotheses of liveness. -/
theorem pM_live (hN : 0 < N ∧ N ≤ 256) (hfit : KFits k N) : (pM xs k N).Live :=
  kchainM_live (fun _ => hN) (by simp) (fun i hi => by
    have : i = 0 := by simp at hi; omega
    subst this; exact hfit)

/-- **The module of a reachable pipe never traps.** -/
theorem pipe_notrap (hN : 0 < N ∧ N ≤ 256) (hfit : KFits k N) {op : Bool} {c : PSys MS}
    (h : PSteps xs k op (DRStep (genD k N)) (PSys.init xs k (m₀ k)) c) :
    NoTrap (genD k N) c.st c.m :=
  mreach_notrap (pM_live hN hfit) (psteps_mreach h) (i := i1 xs k N) pM_gen1

/-! ## The closed pipe -/

/-- Some execution is maximal. -/
theorem exists_mexec (M : MNet) : ∃ r, MExec M r := by
  classical
  let f : MSys M.net → MSys M.net := fun m => if h : MEnabled M m then Classical.choose h else m
  refine ⟨fun n => f^[n] (MSys.init M), rfl, fun n => ?_⟩
  dsimp only
  rw [Function.iterate_succ_apply']
  by_cases h : MEnabled M (f^[n] (MSys.init M))
  · left
    simp only [f, h, ↓reduceDIte]
    exact Classical.choose_spec h
  · right
    simp only [f, h, ↓reduceDIte, not_false_eq_true, and_self]

theorem runs_one (xs : List Val) (k : KM) : runs [k] xs = (trV k).run xs := rfl

/-- Every system of an execution is reachable. -/
theorem mexec_reach {M : MNet} {r : Nat → MSys M.net} (hr : MExec M r) : ∀ j, MReach M (r j) := by
  intro j
  induction j with
  | zero => rw [hr.1]; exact .refl _
  | succ j ih =>
    rcases hr.2 j with h | ⟨-, he⟩
    · exact ih.tail h
    · rw [he]; exact ih

/-- **Some run of the closed pipe finishes**, with the kernel's whole output at the sink. -/
theorem pipe_whole_exists (hN : 0 < N ∧ N ≤ 256) (hfit : KFits k N) :
    (dropObs k N).whole xs ((trV k).run xs) := by
  obtain ⟨r, hr⟩ := exists_mexec (pM xs k N)
  obtain ⟨n, hn⟩ := mexec_done (pM_live hN hfit) hr
  have hreach : MReach (pM xs k N) (r n) := mexec_reach hr n
  obtain ⟨b, hb⟩ := (((hn n le_rfl).2 (i2 xs k N)).1 rfl).1
  have hg := kchainM_correct (fun _ => hN) (by simp) hreach (b := b) hb
  obtain ⟨c, hcm, hc⟩ := mreach_psteps hreach
  rw [hcm] at hb hg
  exact ⟨c, hc, ⟨b, hb⟩, hg⟩

/-- **The whole outputs of the closed pipe are the kernel's.** -/
theorem pipe_whole (hN : 0 < N ∧ N ≤ 256) (hfit : KFits k N) (ys : List Val) :
    (dropObs k N).whole xs ys ↔ ys = (trV k).run xs := by
  constructor
  · rintro ⟨c, hc, ⟨b, hb⟩, rfl⟩
    exact kchainM_correct (fun _ => hN) (by simp) (psteps_mreach hc) (m := toM c) (b := b) hb
  · rintro rfl
    exact pipe_whole_exists hN hfit

end Silmaril.Proofs.Wasm.JcoTool.KLive
