module

public import Silmaril.Wasm.JcoTool.KNetCore.Defs
public import Silmaril.Wasm.JcoTool.KTeeNet.Thms
public import Silmaril.Wasm.JcoTool.KLive.Thms
public import Silmaril.Wasm.JcoTool.KRead.Thms

/-!
# Networks of generated modules on Core 3.0: the refinement

`mreach_greach`: a model network is a `KTeeNet.GNet` with kernel modules only (`toG`), so its
reachable systems keep their buffers in bounds (`KTeeNet.greach_buf`), which `KCoreRun.genD_safe`
needs. `creach_abs`: by `KRead.bwd_step` (a Core step of a module's runtime is a model step, given
that the model does not trap there: `KLive.mreach_notrap`), every reachable Core system stands for
a reachable model system.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KNetCore

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core (Store ModuleInst)
open Silmaril.Wasm.Numerics (Profile GrowKind)
open Silmaril.Wasm.Component.Streams.Drop (DStore)
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Kernel (KM)
open Silmaril.Wasm.JcoTool.KCore (BI MS Mode)
open Silmaril.Wasm.JcoTool.KDrop (genD DRStep)
open Silmaril.Wasm.JcoTool.KNet (MNet MSys MStep MSteps MReach)
open Silmaril.Wasm.JcoTool.KTeeNet (GNet Gen GStep GSteps GReach)
open Silmaril.Wasm.JcoTool.KCoreRun (InstR CbAt)
open Silmaril.Wasm.JcoTool.KRead (CRStepU)
open Silmaril.Wasm.JcoTool.KNetCore

/-- A model network as a network with kernel modules. -/
def toG (M : MNet) : GNet := ⟨M.net, fun i => (M.gen i).map fun p => Gen.kern p.1 p.2⟩

theorem toG_kern {M : MNet} {i : Fin M.net.k} {k : KM} {N : Nat} (h : (toG M).gen i = some (.kern k N)) :
    M.gen i = some (k, N) := by
  simp only [toG, Option.map_eq_some_iff] at h
  obtain ⟨⟨k', N'⟩, h1, h2⟩ := h
  cases h2
  exact h1

theorem toG_ok {M : MNet} (hM : M.OK) : (toG M).OK where
  kern i k N hg := hM.node i k N (toG_kern hg)
  tee i N hg := by
    simp only [toG, Option.map_eq_some_iff] at hg
    obtain ⟨_, -, h⟩ := hg
    cases h
  size i g hg := by
    simp only [toG, Option.map_eq_some_iff] at hg
    obtain ⟨⟨k, N⟩, h1, rfl⟩ := hg
    exact hM.size i k N h1
  ws := hM.ws
  wf := hM.wf

theorem init_eq (M : MNet) : Silmaril.Wasm.JcoTool.KTeeNet.GSys.init (toG M) = MSys.init M := by
  have hm : Silmaril.Wasm.JcoTool.KTeeNet.initG (toG M) = Silmaril.Wasm.JcoTool.KNet.initM M := by
    funext i
    cases hg : M.gen i with
    | none => simp [Silmaril.Wasm.JcoTool.KTeeNet.initG, Silmaril.Wasm.JcoTool.KNet.initM, toG, hg]
    | some p => simp [Silmaril.Wasm.JcoTool.KTeeNet.initG, Silmaril.Wasm.JcoTool.KNet.initM, toG, hg]
  simp only [Silmaril.Wasm.JcoTool.KTeeNet.GSys.init, MSys.init, hm]
  rfl

/-- **A model network's reachable systems are those of its `GNet`.** -/
theorem mreach_greach {M : MNet} {m : MSys M.net} (h : MReach M m) : GReach (toG M) m := by
  unfold MReach at h
  unfold GReach
  rw [init_eq]
  induction h with
  | refl => exact .refl _
  | tail _ hs ih =>
    refine .tail ih ?_
    cases hs with
    | node i hg hn => exact .node (M := toG M) i (by simp [toG, hg]) hn
    | mod i hg hd => exact .mod (M := toG M) (g := .kern _ _) i (by simp [toG, hg]) hd

variable {H : Type}

/-- A module's runtime cannot step on Core once it has exited. -/
theorem crstep_not_exited {o : GrowKind → Nat → Nat → Nat → Bool} {hb : BI → H} {ma a : Nat}
    {st st' : DStore} {cs cs' : Store H} {rp rp' : Option (Nat × Nat)} {md' : Mode}
    (h : CRStepU (Profile.deterministic o) hb ma a (st, cs, rp, .exited) (st', cs', rp', md')) : False := by
  cases h

/-- The relation after module `i` stepped. -/
theorem crel_mod {hb : BI → H} {ma : Nat} {M : MNet} {mi : Fin M.net.k → ModuleInst}
    {a : Fin M.net.k → Nat} {m : MSys M.net} {c : CSys H M.net} (hC : CRel hb ma M mi a m c)
    {i : Fin M.net.k} {k : KM} {N : Nat} {st' : DStore} {cs' : Store H} {rp' : Option (Nat × Nat)}
    {md' : Mode} {ms' : MS} (hg : M.gen i = some (k, N)) (hrp : ms'.rp = rp') (hmd : ms'.mode = md')
    (hI : InstR hb ma cs' (mi i) ms'.g ms'.m) (hcb : CbAt cs' (mi i) (genD k N) (a i)) :
    CRel hb ma M mi a ⟨st', m.ns, Function.update m.ms i ms'⟩ ⟨st', c.ns, Function.update c.cs i cs',
      Function.update c.rp i rp', Function.update c.md i md'⟩ := by
  obtain ⟨-, hns, hmods⟩ := hC
  refine ⟨rfl, hns, fun j k' N' hj => ?_⟩
  by_cases hji : j = i
  · subst hji
    have hkN : k = k' ∧ N = N' := by
      have := hj.symm.trans hg
      simp only [Option.some.injEq, Prod.mk.injEq] at this
      exact ⟨this.1.symm, this.2.symm⟩
    rw [← hkN.1, ← hkN.2]
    simp only [Function.update_self]
    exact ⟨hrp.symm, hmd.symm, hI, hcb⟩
  · simp only [Function.update_of_ne hji]
    exact hmods j k' N' hj

/-- A module step on Core from a related system is a model step to a related system. -/
theorem abs_mod {o : GrowKind → Nat → Nat → Nat → Bool} {hb : BI → H} {ma : Nat} {M : MNet}
    (hL : M.Live) (hinj : Function.Injective hb) {mi : Fin M.net.k → ModuleInst} {a : Fin M.net.k → Nat}
    {m : MSys M.net} {c : CSys H M.net} (hR : MReach M m) (hC : CRel hb ma M mi a m c)
    {i : Fin M.net.k} {k : KM} {N : Nat} {st' : DStore} {cs' : Store H} {rp' : Option (Nat × Nat)}
    {md' : Mode} (hg : M.gen i = some (k, N))
    (h : CRStepU (Profile.deterministic o) hb ma (a i) (c.st, c.cs i, c.rp i, c.md i) (st', cs', rp', md')) :
    ∃ m', MReach M m' ∧ CRel hb ma M mi a m' ⟨st', c.ns, Function.update c.cs i cs',
      Function.update c.rp i rp', Function.update c.md i md'⟩ := by
  have hrel := hC.2.2 i k N hg
  have h' : CRStepU (Profile.deterministic o) hb ma (a i)
      (m.st, c.cs i, (m.ms i).rp, (m.ms i).mode) (st', cs', rp', md') := by
    rw [← hC.1, ← hrel.1, ← hrel.2.1]; exact h
  have hgG : (toG M).gen i = some (.kern k N) := by
    show (M.gen i).map (fun p => Gen.kern p.1 p.2) = _
    rw [hg]; rfl
  have hbuf := Silmaril.Wasm.JcoTool.KTeeNet.greach_buf (toG_ok hL.ok) (mreach_greach hR) hgG
  rcases hbuf with hex | hbuf
  · rw [hex] at h'; exact (crstep_not_exited h').elim
  have hsafe : Silmaril.Wasm.JcoTool.KCoreRun.CbSafe (genD k N) (m.ms i).g :=
    Silmaril.Wasm.JcoTool.KCoreRun.genD_safe k (hL.ok.size i k N hg).2 (m.ms i).g hbuf
  have hnt : Silmaril.Wasm.JcoTool.KRead.NoTrap (genD k N) m.st (m.ms i) :=
    Silmaril.Wasm.JcoTool.KLive.mreach_notrap hL hR hg
  obtain ⟨ms', hd, hrp', hmd', hI', hcb'⟩ := Silmaril.Wasm.JcoTool.KRead.bwd_step o
    (Silmaril.Wasm.JcoTool.KRead.unique_val hinj o) hrel.2.2.1 hrel.2.2.2 hsafe hnt h'
  exact ⟨_, .tail hR (.mod i hg hd), crel_mod hC hg hrp' hmd' hI' hcb'⟩

/-- **The refinement**: every reachable Core system of a live network stands for a reachable model
system. -/
theorem creach_abs {o : GrowKind → Nat → Nat → Nat → Bool} {hb : BI → H} {ma : Nat} {M : MNet}
    (hL : M.Live) (hinj : Function.Injective hb) {mi : Fin M.net.k → ModuleInst} {a : Fin M.net.k → Nat}
    {c₀ c : CSys H M.net} (h0 : CRel hb ma M mi a (MSys.init M) c₀) (h : CSteps o hb ma M a c₀ c) :
    ∃ m, MReach M m ∧ CRel hb ma M mi a m c := by
  induction h with
  | refl => exact ⟨_, .refl _, h0⟩
  | tail _ hs ih =>
    obtain ⟨m, hR, hC⟩ := ih
    cases hs with
    | node i hg hn =>
      rename_i s₁ st' x'
      obtain ⟨hst, hns, hmods⟩ := hC
      have hn' : NStep (M.net.node i) (M.net.ws i) m.st (m.ns i) st' x' := by
        rw [← hst, ← hns]; exact hn
      refine ⟨_, .tail hR (.node i hg hn'), rfl, by rw [hns], fun j k N hj => hmods j k N hj⟩
    | mod i hg hd => exact abs_mod hL hinj hR hC hg hd

end Silmaril.Proofs.Wasm.JcoTool.KNetCore
