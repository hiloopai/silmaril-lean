module

public import Silmaril.Proofs.Wasm.JcoTool.KDrop.Main
public import Silmaril.Wasm.Component.Streams.Pipes.Thms

/-!
# Chains of generated modules

`kchain_wf`: the chain network is well formed. `kreach_abs`: every reachable system of the chain
with generated modules stands for a reachable system of `kchain` (the `Net` network whose
transformer nodes are the generic node program), through `RelD` for the modules. `kchain_spec`:
the specification propagates along the chain (`Pipes.net_spec`), so the sink holds the
composite's output.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KDrop

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)

variable {xs : List Val} {ks : List KM}

/-! ## The network -/

theorem wf_inp_rd (i : Fin (kchain xs ks).k) (c : Nat) (h : ((kchain xs ks).node i).inp = some c) :
    c < (kchain xs ks).m ∧ (kchain xs ks).rd c = i := by
  have hi : i.val < ks.length + 2 := i.isLt
  have h0 : i.val ≠ 0 ∧ c = i.val - 1 := by
    simp only [kchain] at h
    split_ifs at h with h0
    exact ⟨h0, (Option.some.inj h).symm⟩
  have h1 : (i.val - 1 + 1) % (ks.length + 2) = i.val := by
    rw [Nat.sub_add_cancel (by omega)]; exact Nat.mod_eq_of_lt hi
  obtain ⟨-, rfl⟩ := h0
  exact ⟨by simp only [kchain]; omega, Fin.ext h1⟩

theorem wf_out_wr (i : Fin (kchain xs ks).k) (j c : Nat) (h : ((kchain xs ks).node i).outs[j]? = some c) :
    c < (kchain xs ks).m ∧ (kchain xs ks).wr c = (i, j) := by
  have hi : i.val < ks.length + 2 := i.isLt
  have hj : j = 0 ∧ c = i.val ∧ i.val ≠ ks.length + 1 := by
    simp only [kchain] at h
    split_ifs at h with h0
    · simp at h
    · rcases j with _ | j <;> simp_all
  obtain ⟨rfl, rfl, hne⟩ := hj
  exact ⟨by simp only [kchain]; omega, Prod.ext (Fin.ext (Nat.mod_eq_of_lt hi)) rfl⟩

theorem kchain_wf (xs : List Val) (ks : List KM) : (kchain xs ks).WF where
  rd_inp c hc := by
    have h1 : (c + 1) % (ks.length + 2) = c + 1 := Nat.mod_eq_of_lt (by simp [kchain] at hc; omega)
    simp [kchain, h1]
  wr_out c hc := by
    have h1 : c % (ks.length + 2) = c := Nat.mod_eq_of_lt (by simp [kchain] at hc; omega)
    have h2 : c ≠ ks.length + 1 := by simp [kchain] at hc; omega
    simp [kchain, h1, h2]
  inp_rd := wf_inp_rd
  out_wr := wf_out_wr
  no_loop c hc := by
    have h1 : (c + 1) % (ks.length + 2) = c + 1 := Nat.mod_eq_of_lt (by simp [kchain] at hc; omega)
    have h2 : c % (ks.length + 2) = c := Nat.mod_eq_of_lt (by simp [kchain] at hc; omega)
    intro h
    have := congrArg Fin.val h
    simp [kchain, h1, h2] at this

/-- The index of module `i` in the network. -/
def mid (i : Fin ks.length) : Fin (kchain xs ks).k := ⟨i.val + 1, Nat.succ_lt_succ (Nat.lt_succ_of_lt i.isLt)⟩

theorem mid_ne (i : Fin ks.length) : (i.val = ks.length) = False := by
  have := i.isLt
  simp only [eq_iff_iff, iff_false]
  omega

/-- The node of module `i`: its kernel, reading stream `i`, writing stream `i + 1`. -/
theorem chainT_mod (i : Fin ks.length) : chainT xs ks (i.val + 1) = trV (ks.get i) := by
  simp [chainT]

/-- A step of the node `node k c c'` is a step of any node with the same parts. -/
theorem nstep_of {k : KM} {c c' ws : Nat} {T : Tr KSt Val Val} {inp : Option Nat} {outs : List Nat}
    {st st' : DStore} {x x' : NSt KSt} (hT : T = trV k) (hi : inp = some c) (ho : outs = [c'])
    (h : NStep (node k c c') ws st x st' x') : NStep ⟨KSt, T, inp, outs⟩ ws st x st' x' := by
  subst hT hi ho
  exact h

theorem nstep_mod {i : Fin ks.length} {ws : Nat} {st st' : DStore} {x x' : NSt KSt}
    (h : NStep (node (ks.get i) i (i + 1)) ws st x st' x') :
    NStep ((kchain xs ks).node (mid i)) ws st x st' x' :=
  nstep_of (chainT_mod i) (by simp [mid]) (by simp [mid, mid_ne]) h

theorem init_mod (i : Fin ks.length) :
    NSt.init ((kchain xs ks).node (mid i)) = NSt.init (node (ks.get i) i (i + 1)) := by
  simp [NSt.init, kchain, node, chainT_mod, mid, mid_ne]

/-! ## The abstraction -/

/-- A system with modules stands for the system `s` of `kchain`. -/
def Abs (c : KSys ks.length) (s : Sys (kchain xs ks)) : Prop :=
  s.st = c.st ∧ s.ns ⟨0, by simp [kchain]⟩ = c.src ∧ s.ns ⟨ks.length + 1, by simp [kchain]⟩ = c.snk ∧
    ∀ i : Fin ks.length, RelD (rh i) (wh (i + 1)) ((kchain xs ks).ws (i + 1)) (c.ms i)
      (s.ns (mid i))

theorem abs_init : Abs (KSys.init xs ks) (init (kchain xs ks)) := by
  refine ⟨rfl, rfl, rfl, fun i => ?_⟩
  have h := init_rel (ks.get i) i (i + 1) ((kchain xs ks).ws (i + 1))
  rw [← init_mod (xs := xs) i] at h
  exact h

theorem mid_ne0 (i : Fin ks.length) : mid (xs := xs) i ≠ ⟨0, by simp [kchain]⟩ := by
  intro h; have := congrArg Fin.val h; simp [mid] at this

theorem mid_neL (i : Fin ks.length) : mid (xs := xs) i ≠ ⟨ks.length + 1, by simp [kchain]⟩ := by
  intro h; have := congrArg Fin.val h; have := i.isLt; simp [mid] at *; omega

theorem mid_inj {i j : Fin ks.length} (h : j ≠ i) : mid (xs := xs) j ≠ mid i := by
  intro h'; exact h (Fin.ext (by have := congrArg Fin.val h'; simpa [mid] using this))

theorem zero_neL : (⟨0, by simp [kchain]⟩ : Fin (kchain xs ks).k) ≠ ⟨ks.length + 1, by simp [kchain]⟩ := by
  intro h; have := congrArg Fin.val h; simp at this

/-- A step of the source keeps the abstraction. -/
theorem abs_src {c : KSys ks.length} {s : Sys (kchain xs ks)} {st' : DStore} {x' : NSt KSt}
    (hR : Reach (kchain xs ks) s) (hA : Abs c s)
    (hn : NStep ((kchain xs ks).node ⟨0, by simp [kchain]⟩) ((kchain xs ks).ws 0) c.st c.src st' x') :
    ∃ s', Reach (kchain xs ks) s' ∧ Abs { c with st := st', src := x' } s' := by
  obtain ⟨hst, hsrc, hsnk, hms⟩ := hA
  rw [← hst, ← hsrc] at hn
  refine ⟨_, .tail hR (.node _ hn), rfl, (by show Function.update s.ns (⟨0, by simp [kchain]⟩ : Fin (kchain xs ks).k) x' (⟨0, by simp [kchain]⟩ : Fin (kchain xs ks).k) = x'; exact Function.update_self _ _ _), ?_, fun i => ?_⟩
  · show Function.update s.ns (⟨0, by simp [kchain]⟩ : Fin (kchain xs ks).k) x' (⟨ks.length + 1, by simp [kchain]⟩ : Fin (kchain xs ks).k) = c.snk
    erw [Function.update_of_ne (zero_neL (xs := xs) (ks := ks)).symm]; exact hsnk
  · show RelD _ _ _ _ (Function.update s.ns _ x' (mid i))
    erw [Function.update_of_ne (mid_ne0 i)]; exact hms i

/-- A step of the sink keeps the abstraction. -/
theorem abs_snk {c : KSys ks.length} {s : Sys (kchain xs ks)} {st' : DStore} {x' : NSt KSt}
    (hR : Reach (kchain xs ks) s) (hA : Abs c s)
    (hn : NStep ((kchain xs ks).node ⟨ks.length + 1, by simp [kchain]⟩) ((kchain xs ks).ws (ks.length + 1))
      c.st c.snk st' x') :
    ∃ s', Reach (kchain xs ks) s' ∧ Abs { c with st := st', snk := x' } s' := by
  obtain ⟨hst, hsrc, hsnk, hms⟩ := hA
  rw [← hst, ← hsnk] at hn
  refine ⟨_, .tail hR (.node _ hn), rfl, ?_, (by show Function.update s.ns (⟨ks.length + 1, by simp [kchain]⟩ : Fin (kchain xs ks).k) x' (⟨ks.length + 1, by simp [kchain]⟩ : Fin (kchain xs ks).k) = x'; exact Function.update_self _ _ _), fun i => ?_⟩
  · show Function.update s.ns (⟨ks.length + 1, by simp [kchain]⟩ : Fin (kchain xs ks).k) x' (⟨0, by simp [kchain]⟩ : Fin (kchain xs ks).k) = c.src
    erw [Function.update_of_ne (zero_neL (xs := xs) (ks := ks))]; exact hsrc
  · show RelD _ _ _ _ (Function.update s.ns _ x' (mid i))
    erw [Function.update_of_ne (mid_neL i)]; exact hms i

/-- A step of module `i` keeps the abstraction. -/
theorem abs_mod {Nb : Nat → Nat} (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) (hws : ks.length < 2 ^ 26)
    {c : KSys ks.length} {s : Sys (kchain xs ks)} {st' : DStore} {m' : MS} {i : Fin ks.length}
    (hR : Reach (kchain xs ks) s) (hA : Abs c s) (h : DRStep (genD (ks.get i) (Nb i)) c.st (c.ms i) st' m') :
    ∃ s', Reach (kchain xs ks) s' ∧ Abs { c with st := st', ms := Function.update c.ms i m' } s' := by
  obtain ⟨hst, hsrc, hsnk, hms⟩ := hA
  have hs : (kchain xs ks).ws (i + 1) < 2 ^ 28 := by
    have := i.isLt; simp only [Network.ws, kchain]; omega
  obtain ⟨x', hR', hx⟩ := step_sim (hN i) hs (hms i) h
  rcases hx with hn | ⟨rfl, rfl⟩
  · rw [← hst] at hn
    refine ⟨_, .tail hR (.node (mid i) (nstep_mod hn)), rfl, ?_, ?_, fun j => ?_⟩
    · show Function.update s.ns (mid i) x' (⟨0, by simp [kchain]⟩ : Fin (kchain xs ks).k) = c.src
      erw [Function.update_of_ne (mid_ne0 i).symm]; exact hsrc
    · show Function.update s.ns (mid i) x' (⟨ks.length + 1, by simp [kchain]⟩ : Fin (kchain xs ks).k) = c.snk
      erw [Function.update_of_ne (mid_neL i).symm]; exact hsnk
    · by_cases hj : j = i
      · subst hj
        show RelD _ _ _ (Function.update c.ms j m' j) (Function.update s.ns _ x' (mid j))
        erw [Function.update_self, Function.update_self]; exact hR'
      · show RelD _ _ _ (Function.update c.ms i m' j) (Function.update s.ns _ x' (mid j))
        erw [Function.update_of_ne hj, Function.update_of_ne (mid_inj hj)]; exact hms j
  · refine ⟨s, hR, hst, hsrc, hsnk, fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      show RelD _ _ _ (Function.update c.ms j m' j) _
      erw [Function.update_self]; exact hR'
    · show RelD _ _ _ (Function.update c.ms i m' j) _
      erw [Function.update_of_ne hj]; exact hms j

/-- **The refinement**: every reachable system of the chain with generated modules stands for a
reachable system of `kchain`. -/
theorem kreach_abs {Nb : Nat → Nat} (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) (hws : ks.length < 2 ^ 26)
    {c : KSys ks.length} (h : KReach xs ks Nb c) : ∃ s, Reach (kchain xs ks) s ∧ Abs c s := by
  induction h with
  | refl => exact ⟨_, .refl _, abs_init⟩
  | tail _ hs ih =>
    obtain ⟨s, hR, hA⟩ := ih
    cases hs with
    | src hn => exact abs_src hR hA hn
    | snk hn => exact abs_snk hR hA hn
    | mod i hd => exact abs_mod hN hws hR hA hd

/-! ## The specification along the chain -/

open Silmaril.Proofs.Wasm.Component.Streams.Net (SpecOK)

theorem runs_succ {i : Nat} (hi : i < ks.length) :
    runs (ks.take (i + 1)) xs = (trV ks[i]).run (runs (ks.take i) xs) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [runs, Option.toList, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem wr_fst {c : Nat} (hc : c < ks.length + 2) :
    ((kchain xs ks).wr c).1 = ⟨c, hc⟩ := Fin.ext (Nat.mod_eq_of_lt hc)

theorem spec_zero {s : Sys (kchain xs ks)} (hR : Reach (kchain xs ks) s) :
    SpecOK s ⟨1, by simp [kchain]⟩ (runs (ks.take 0) xs) := by
  have h0 : SpecOK s ((kchain xs ks).wr 0).1 [] :=
    Silmaril.Wasm.Component.Streams.Pipes.net_src (kchain_wf xs ks) hR _ (by rw [wr_fst (by omega)]; simp [kchain])
  have h1 : SpecOK s ⟨1, by simp [kchain]⟩ (((kchain xs ks).node ((kchain xs ks).wr 0).1).T.run []) :=
    Silmaril.Wasm.Component.Streams.Pipes.net_spec (kchain_wf xs ks) hR ⟨1, by simp [kchain]⟩
      (c := 0) (by simp [kchain]) [] h0
  have hT : ((kchain xs ks).node ((kchain xs ks).wr 0).1).T.run [] = runs (ks.take 0) xs := by
    simp [kchain, chainT, srcK, Tr.run, Tr.feed, runs]
  rwa [hT] at h1

theorem spec_succ {s : Sys (kchain xs ks)} (hR : Reach (kchain xs ks) s) {i : Nat} (hi : i + 1 ≤ ks.length)
    (ih : SpecOK s ⟨i + 1, by simp [kchain]; omega⟩ (runs (ks.take i) xs)) :
    SpecOK s ⟨i + 1 + 1, by simp [kchain]; omega⟩ (runs (ks.take (i + 1)) xs) := by
  have hU : SpecOK s ((kchain xs ks).wr (i + 1)).1 (runs (ks.take i) xs) := by
    rw [wr_fst (by omega)]; exact ih
  have h1 : SpecOK s ⟨i + 1 + 1, by simp [kchain]; omega⟩
      (((kchain xs ks).node ((kchain xs ks).wr (i + 1)).1).T.run (runs (ks.take i) xs)) :=
    Silmaril.Wasm.Component.Streams.Pipes.net_spec (kchain_wf xs ks) hR _ (c := i + 1) (by simp [kchain]) _ hU
  have hm : (i + 1) % (ks.length + 2) = i + 1 := Nat.mod_eq_of_lt (by omega)
  have hT : ((kchain xs ks).node ((kchain xs ks).wr (i + 1)).1).T.run (runs (ks.take i) xs) =
      runs (ks.take (i + 1)) xs := by
    rw [runs_succ (by omega)]
    simp [kchain, chainT, hm, List.getElem?_eq_getElem (show i < ks.length by omega)]
  rwa [hT] at h1

/-- **Along the chain**: node `i + 1` has read a prefix of the first `i` kernels' composite on
`xs`, all of it once its input ended. -/
theorem chain_spec {s : Sys (kchain xs ks)} (hR : Reach (kchain xs ks) s) :
    ∀ i (hi : i ≤ ks.length), SpecOK s ⟨i + 1, by simp [kchain]; omega⟩ (runs (ks.take i) xs) := by
  intro i
  induction i with
  | zero => exact fun _ => spec_zero hR
  | succ i ih => exact fun hi => spec_succ hR hi (ih (by omega))

/-- **A chain of generated modules is correct**: once the sink has dropped its input, it holds
the kernels' composite on the source's items. -/
theorem kchain_correct {Nb : Nat → Nat} (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) (hws : ks.length < 2 ^ 26)
    {c : KSys ks.length} (h : KReach xs ks Nb c) {b : Bool} (hb : c.snk.rd = .gone b) :
    c.snk.got = runs ks xs := by
  obtain ⟨s, hR, hst, -, hsnk, -⟩ := kreach_abs hN hws h
  have hspec := chain_spec hR ks.length le_rfl
  rw [List.take_length] at hspec
  have hb' : (s.ns ⟨ks.length + 1, by simp [kchain]⟩).rd = .gone b := by rw [hsnk]; exact hb
  have ht := Silmaril.Wasm.Component.Streams.Pipes.net_sink_eof (kchain_wf xs ks) hR
    ⟨ks.length + 1, by simp [kchain]⟩ (by simp [kchain]) (fun _ => by simp [kchain, chainT, sinkK]) hb'
  subst ht
  rw [← hsnk]
  exact hspec.2 hb'

/-- **Safety**: at every point the sink holds a prefix of the composite. -/
theorem kchain_safe {Nb : Nat → Nat} (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) (hws : ks.length < 2 ^ 26)
    {c : KSys ks.length} (h : KReach xs ks Nb c) : c.snk.got <+: runs ks xs := by
  obtain ⟨s, hR, -, -, hsnk, -⟩ := kreach_abs hN hws h
  have hspec := chain_spec hR ks.length le_rfl
  rw [List.take_length] at hspec
  rw [← hsnk]
  exact hspec.1

end Silmaril.Proofs.Wasm.JcoTool.KDrop
