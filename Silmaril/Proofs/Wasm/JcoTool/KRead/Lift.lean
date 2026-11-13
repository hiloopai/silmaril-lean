module

public import Silmaril.Proofs.Wasm.JcoTool.KRead.Step
public import Silmaril.Proofs.Wasm.JcoTool.KRead.Unf

/-!
# The pipe of a generated module on Core, both ways

`PRel c d`: the model pipe state `c` (the drop runtime's machine) and the Core pipe state `d`
(Core store, pending read, mode) have the same store, source and sink, and the Core store holds
the machine's globals and memory and the callback (`InstR`, `CbAt`).

* `ri_steps`: along the model pipe, the machine stays related to a node state (`RelD`), so it is
  within the buffer bounds (`okD`) whenever it can step.
* `fwd_steps`: every run of the model pipe from a related pair is matched
  by a run of the Core pipe, related at the end.
* `bwd_steps` (for injective `hb`, given `Task.genD_notrap`, in the
  deterministic profile): every run of the Core pipe from a pair whose model state is reachable is matched by a
  run of the model pipe.
* `psteps_kreach`: a run of the model pipe is a run of `KDrop`'s chain `kchain xs [k]`.
-/

public section

namespace Silmaril.Proofs.Wasm.JcoTool.KRead

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core (Store ModuleInst)
open Silmaril.Wasm.Numerics (Profile GrowKind)
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.JcoTool.KRead
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (BI M32 Prog MS Mode)
open Silmaril.Wasm.JcoTool.KDrop (DRStep genD RelD okD initMSD KSys KStep KSteps KReach kchain)
open Silmaril.Wasm.Component.Streams.Drop (DStore)
open Silmaril.Wasm.Component.Streams.Net (NSt rh wh)
open Silmaril.Wasm.Component.Streams.Kernel (KM)

variable {H : Type} {hb : BI → H} {ma : Nat}

/-- The model pipe state and the Core pipe state agree. -/
structure PRel (hb : BI → H) (ma : Nat) (mi : ModuleInst) (a : Nat) (P : Prog) (c : PSys MS)
    (d : PSys (CM H)) : Prop where
  st : d.st = c.st
  src : d.src = c.src
  snk : d.snk = c.snk
  rp : d.m.2.1 = c.m.rp
  md : d.m.2.2 = c.m.mode
  inst : InstR hb ma d.m.1 mi c.m.g c.m.m
  cb : CbAt d.m.1 mi P a

/-- The machine is related to some node state. -/
def RI (c : PSys MS) : Prop := ∃ x, RelD (rh 0) (wh 1) wsM c.m x

theorem drstep_live {P : Prog} {st st' : DStore} {ms ms' : MS} (h : DRStep P st ms st' ms') :
    ms.mode ≠ .exited := by
  cases h with
  | ready hm _ => rw [hm]; exact fun h => by cases h
  | event hm _ _ _ => rw [hm]; exact fun h => by cases h

theorem okD_of {ms : MS} {x : NSt Silmaril.Wasm.Component.Streams.Kernel.KSt} {r w s : Nat}
    (h : RelD r w s ms x) (hm : ms.mode ≠ .exited) : okD ms r w s := by
  unfold RelD at h
  simp only [hm, ↓reduceIte] at h
  exact h.1

/-- The callback of `genD k N` is `CbSafe` at a related machine that is not exited. -/
theorem safe_of {k : KM} {N : Nat} (hN : N ≤ 256) {c : PSys MS}
    (hri : RI c) (hm : c.m.mode ≠ .exited) : CbSafe (genD k N) c.m.g := by
  obtain ⟨x, hx⟩ := hri
  have hok := okD_of hx hm
  exact genD_safe k hN c.m.g ⟨hok.2.2.2.1, hok.2.2.2.2.1, hok.2.2.2.2.2⟩

theorem wsM_lt : wsM < 2 ^ 28 := by decide

theorem ri_step {xs : List Val} {k : KM} {N : Nat} {op : Bool} (hN : 0 < N ∧ N ≤ 256)
    {c c' : PSys MS} (hri : RI c) (h : PStep xs k op (DRStep (genD k N)) c c') : RI c' := by
  cases h with
  | src _ _ => exact hri
  | snk _ => exact hri
  | mod hR =>
    obtain ⟨x, hx⟩ := hri
    obtain ⟨x', hx', -⟩ := Silmaril.Wasm.JcoTool.KDrop.step_sim hN wsM_lt hx hR
    exact ⟨x', hx'⟩

theorem ri_init (xs : List Val) (k : KM) : RI (PSys.init xs k (m₀ k)) :=
  ⟨_, Silmaril.Wasm.JcoTool.KDrop.init_rel k 0 1 wsM⟩

theorem ri_steps {xs : List Val} {k : KM} {N : Nat} {op : Bool} (hN : 0 < N ∧ N ≤ 256)
    {c c' : PSys MS} (hri : RI c) (h : PSteps xs k op (DRStep (genD k N)) c c') : RI c' := by
  induction h with
  | refl => exact hri
  | tail _ h ih => exact ri_step hN ih h

/-- One model pipe step is matched by one Core pipe step. -/
theorem fwd_pstep (Pf : Profile) {xs : List Val} {k : KM} {N : Nat}
    {op : Bool} (hN : 0 < N ∧ N ≤ 256) {mi : ModuleInst} {a : Nat} {c c' : PSys MS}
    {d : PSys (CM H)} (hri : RI c) (hd : PRel hb ma mi a (genD k N) c d)
    (h : PStep xs k op (DRStep (genD k N)) c c') :
    ∃ d', PStep xs k op (coreR Pf hb ma a) d d' ∧ PRel hb ma mi a (genD k N) c' d' := by
  cases h with
  | @src st' x' hn hcl =>
    refine ⟨{ d with st := st', src := x' }, .src (by rw [hd.st, hd.src]; exact hn) hcl, ?_⟩
    exact ⟨rfl, rfl, hd.snk, hd.rp, hd.md, hd.inst, hd.cb⟩
  | @snk st' x' hn =>
    refine ⟨{ d with st := st', snk := x' }, .snk (by rw [hd.st, hd.snk]; exact hn), ?_⟩
    exact ⟨rfl, hd.src, rfl, hd.rp, hd.md, hd.inst, hd.cb⟩
  | @mod st' m' hR =>
    have hsafe := safe_of (k := k) hN.2 hri (drstep_live hR)
    obtain ⟨cs', hC, hI', hcb'⟩ := fwd_step Pf hd.inst hd.cb hsafe hR
    refine ⟨{ d with st := st', m := (cs', m'.rp, m'.mode) }, .mod ?_, ?_⟩
    · show CRStepU Pf hb ma a (d.st, d.m.1, d.m.2.1, d.m.2.2) (st', cs', m'.rp, m'.mode)
      rw [hd.st, hd.rp, hd.md]
      exact hC
    · exact ⟨rfl, hd.src, hd.snk, rfl, rfl, hI', hcb'⟩

/-- **Runs of the model pipe are runs of the Core pipe**. -/
theorem fwd_steps (Pf : Profile) {xs : List Val} {k : KM} {N : Nat}
    {op : Bool} (hN : 0 < N ∧ N ≤ 256) {mi : ModuleInst} {a : Nat} {c c₁ : PSys MS}
    (hri : RI c) (h : PSteps xs k op (DRStep (genD k N)) c c₁) {d : PSys (CM H)}
    (hd : PRel hb ma mi a (genD k N) c d) :
    ∃ d₁, PSteps xs k op (coreR Pf hb ma a) d d₁ ∧ PRel hb ma mi a (genD k N) c₁ d₁ := by
  induction h with
  | refl => exact ⟨d, .refl, hd⟩
  | @tail c' c'' h₁ h₂ ih =>
    obtain ⟨d', hd', hr'⟩ := ih
    obtain ⟨d'', hd'', hr''⟩ := fwd_pstep Pf hN (ri_steps hN hri h₁) hr' h₂
    exact ⟨d'', hd'.tail hd'', hr''⟩

/-- A module step of the Core pipe is a module step of the model pipe. -/
theorem bwd_mod (hinj : Function.Injective hb) 
    (o : GrowKind → Nat → Nat → Nat → Bool) {xs : List Val} {k : KM} {N : Nat} {op : Bool}
    (hN : 0 < N ∧ N ≤ 256) {mi : ModuleInst} {a : Nat} {c : PSys MS} {d : PSys (CM H)}
    {st' : DStore} {m' : CM H} (hri : RI c) (hnt : NoTrap (genD k N) c.st c.m)
    (hd : PRel hb ma mi a (genD k N) c d) (hR : coreR (Profile.deterministic o) hb ma a d.st d.m st' m') :
    ∃ c', PStep xs k op (DRStep (genD k N)) c c' ∧
      PRel hb ma mi a (genD k N) c' { d with st := st', m := m' } := by
  have hR₀ : CRStepU (Profile.deterministic o) hb ma a (d.st, d.m.1, d.m.2.1, d.m.2.2)
      (st', m'.1, m'.2.1, m'.2.2) := hR
  have hR' : CRStepU (Profile.deterministic o) hb ma a (c.st, d.m.1, c.m.rp, c.m.mode)
      (st', m'.1, m'.2.1, m'.2.2) := by rw [← hd.st, ← hd.rp, ← hd.md]; exact hR₀
  have hm : c.m.mode ≠ .exited := fun he => by rw [he] at hR'; cases hR'
  have hsafe := safe_of (k := k) hN.2 hri hm
  obtain ⟨ms', hD, hrp, hmd, hI', hcb'⟩ :=
    bwd_step o (fun _ _ _ hy hz vy vz => unique_val hinj o hy hz vy vz) hd.inst hd.cb hsafe hnt hR'
  exact ⟨{ c with st := st', m := ms' }, .mod hD, ⟨rfl, hd.src, hd.snk, hrp.symm, hmd.symm, hI', hcb'⟩⟩

/-- One Core pipe step is matched by one model pipe step, from a machine that does not trap. -/
theorem bwd_pstep (hinj : Function.Injective hb) (o : GrowKind → Nat → Nat → Nat → Bool)
    {xs : List Val} {k : KM} {N : Nat} {op : Bool} (hN : 0 < N ∧ N ≤ 256) {mi : ModuleInst}
    {a : Nat} {c : PSys MS} {d d' : PSys (CM H)} (hri : RI c)
    (hnt : NoTrap (genD k N) c.st c.m) (hd : PRel hb ma mi a (genD k N) c d)
    (h : PStep xs k op (coreR (Profile.deterministic o) hb ma a) d d') :
    ∃ c', PStep xs k op (DRStep (genD k N)) c c' ∧ PRel hb ma mi a (genD k N) c' d' := by
  cases h with
  | @src st' x' hn hcl =>
    refine ⟨{ c with st := st', src := x' }, .src (by rw [← hd.st, ← hd.src]; exact hn) hcl, ?_⟩
    exact ⟨rfl, rfl, hd.snk, hd.rp, hd.md, hd.inst, hd.cb⟩
  | @snk st' x' hn =>
    refine ⟨{ c with st := st', snk := x' }, .snk (by rw [← hd.st, ← hd.snk]; exact hn), ?_⟩
    exact ⟨rfl, hd.src, rfl, hd.rp, hd.md, hd.inst, hd.cb⟩
  | @mod st' m' hR => exact bwd_mod hinj o hN hri hnt hd hR

/-- **Runs of the Core pipe are runs of the model pipe** (given `hb` injective,
`NoTrapAt k N`), from a reachable model state. -/
theorem bwd_steps (hinj : Function.Injective hb) {k : KM} {N : Nat} (hn : NoTrapAt k N)
    (o : GrowKind → Nat → Nat → Nat → Bool) {xs : List Val} {op : Bool}
    (hN : 0 < N ∧ N ≤ 256) {mi : ModuleInst} {a : Nat} {c : PSys MS}
    (hc : PSteps xs k op (DRStep (genD k N)) (PSys.init xs k (m₀ k)) c) {d d₁ : PSys (CM H)}
    (hd : PRel hb ma mi a (genD k N) c d)
    (h : PSteps xs k op (coreR (Profile.deterministic o) hb ma a) d d₁) :
    ∃ c₁, PSteps xs k op (DRStep (genD k N)) c c₁ ∧ PRel hb ma mi a (genD k N) c₁ d₁ := by
  induction h with
  | refl => exact ⟨c, .refl, hd⟩
  | @tail d' d'' h₁ h₂ ih =>
    obtain ⟨c', hc', hr'⟩ := ih
    have hreach := hc.trans hc'
    obtain ⟨c'', hc'', hr''⟩ := bwd_pstep hinj o hN (ri_steps hN (ri_init xs k) hreach)
      (hn xs op c' hreach) hr' h₂
    exact ⟨c'', hc'.tail hc'', hr''⟩

/-- The pipe's model state as a state of `KDrop`'s chain. -/
@[expose] def kof {k : KM} (c : PSys MS) : KSys [k].length := ⟨c.st, c.src, fun _ => c.m, c.snk⟩

theorem kof_snk {k : KM} (c : PSys MS) : (kof (k := k) c).snk = c.snk := rfl

theorem kof_init (xs : List Val) (k : KM) :
    kof (k := k) (PSys.init xs k (m₀ k)) = KSys.init xs [k] := by
  simp only [kof, PSys.init, KSys.init]
  congr 1
  funext i
  have hi : i = 0 := Fin.ext (by have := i.isLt; simp only [List.length_cons, List.length_nil] at this; simp only [Fin.val_zero]; omega)
  subst hi
  rfl

/-- **A run of the model pipe is a run of the chain `kchain xs [k]`.** -/
theorem psteps_kreach {xs : List Val} {k : KM} {N : Nat} {op : Bool} {c : PSys MS}
    (h : PSteps xs k op (DRStep (genD k N)) (PSys.init xs k (m₀ k)) c) :
    KReach xs [k] (fun _ => N) (kof c) := by
  induction h with
  | refl => rw [kof_init]; exact .refl _
  | @tail c' c'' _ h₂ ih =>
    refine ih.tail ?_
    cases h₂ with
    | src hn _ => exact .src hn
    | snk hn => exact .snk hn
    | @mod st' m' hR =>
      have h1 := KStep.mod (xs := xs) (Nb := fun _ => N) (c := kof (k := k) c') 0 hR
      have e : kof (k := k) { c' with st := st', m := m' } =
          { kof (k := k) c' with st := st', ms := Function.update (kof (k := k) c').ms 0 m' } := by
        simp only [kof]
        congr 1
        funext i
        have hi : i = 0 := Fin.ext (by have := i.isLt; simp only [List.length_cons, List.length_nil] at this; simp only [Fin.val_zero]; omega)
        subst hi
        simp
      rw [e]
      exact h1

end Silmaril.Proofs.Wasm.JcoTool.KRead
