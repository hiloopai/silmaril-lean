module

public import Silmaril.Elf.Link.Dyn.Mt.Defs
public import Silmaril.Process.Mt.Thms

/-!
# Proofs: `ProcX` results hold of the one-thread multithreaded process

The header is `Silmaril/Elf/Link/Dyn/Mt/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Proofs.Elf.Link.Dyn.Mt

open Silmaril.X86 (Word)
open Silmaril.X86.RelIsa (Res Must)
open Silmaril.Process (Memory)
open Silmaril.Process.Mt
open Silmaril.Process.Mt.X86 (Core)
open Silmaril.Elf.Link.Dyn.Proc (World Ghost)
open Silmaril.Elf.Link.Dyn.ProcX (XPState procX)
open Silmaril.Elf.Link.Dyn.Mt

variable {W : World} {prims : List (Word × Nat)} {P : PrimTable Ghost} {base : Base Ghost} {tid : Nat}

/-- An image step keeps the ghost. -/
theorem image_ghost {s s' : XPState} (h : Silmaril.Elf.Link.Dyn.ProcX.step W s (.ok s'))
    (hi : W.InImage s.p.m.core.rip.toNat) : s'.p.g = s.p.g := by
  unfold Silmaril.Elf.Link.Dyn.ProcX.step at h
  split at h
  · cases h
  · simp only [hi, ↓reduceIte] at h
    split at h
    · cases h; rfl
    · cases h

/-- Away from the primitives, a thread's action is a `ProcX` outcome. -/
theorem step_none {t : Nat} {c : Core} {m : Memory} {g : Ghost} {o : UOut Core Ghost}
    (hp : prims.find? (·.1 == c.core.rip) = none) :
    step W prims t c m g o ↔
      ∃ r, Silmaril.Elf.Link.Dyn.ProcX.step W (toX c m g) r ∧ o = out (decide (W.InImage c.core.rip.toNat)) r := by
  unfold step; rw [hp]

theorem out_ne_sys {b : Bool} {r : Res XPState} {nr : Nat} {args : List Word} {k : Word → Core}
    {ch : Core} : out b r ≠ .sys nr args k ch := by
  cases b <;> cases r <;> simp [out]

theorem out_ne_prim {b : Bool} {r : Res XPState} {p : Nat} {args : List Word} {k : Word → Core} :
    out b r ≠ .prim p args k := by
  cases b <;> cases r <;> simp [out]

theorem out_stop {b : Bool} {r : Res XPState} (h : UOut.stop = out b r) : r = .stop := by
  cases b <;> cases r <;> simp [out] at h ⊢

/-- The single-threaded view's state as a `ProcX` state. -/
def xs (x : SoloCfg Core Ghost) : XPState := toX x.st x.mem x.g

theorem must_solo {R Q : XPState → Prop} {s : XPState} (h : Must (procX W) R Q s)
    (hR : ∀ s, R s → prims.find? (·.1 == s.p.m.core.rip) = none) :
    ∀ x : SoloCfg Core Ghost, xs x = s →
      SMust (SoloStep (mtDyn W prims) P base tid) (SoloFault (mtDyn W prims) P tid) (fun x => Q (xs x)) x := by
  induction h with
  | done hq => intro x hx; exact .done (hx ▸ hq)
  | @step s hr hns _ ih =>
    intro x hx
    subst hx
    have hp := hR _ hr
    refine .step ?_ ?_
    · rintro ⟨_, hf | ⟨p, args, k, hf, _⟩⟩
      · obtain ⟨r, h1, h2⟩ := (step_none (t := tid) hp).1 hf
        obtain rfl := out_stop h2
        exact hns h1
      · obtain ⟨r, _, h2⟩ := (step_none (t := tid) hp).1 hf
        exact out_ne_prim h2.symm
    · intro x' hs
      cases hs with
      | user hl hs =>
        obtain ⟨r, h1, h2⟩ := (step_none (t := tid) hp).1 hs
        cases hb : decide (W.InImage x.st.core.rip.toNat) <;> rw [hb] at h2 <;> cases r <;>
          simp only [out, reduceCtorEq] at h2
        rename_i s1
        simp only [UOut.step.injEq] at h2
        obtain ⟨rfl, -, rfl⟩ := h2
        have hg := image_ghost h1 (of_decide_eq_true hb)
        refine ih s1 h1 _ ?_
        simp only [xs, toX] at hg ⊢
        rw [← hg]
      | lib hl hs =>
        obtain ⟨r, h1, h2⟩ := (step_none (t := tid) hp).1 hs
        cases hb : decide (W.InImage x.st.core.rip.toNat) <;> rw [hb] at h2 <;> cases r <;>
          simp only [out, reduceCtorEq] at h2
        rename_i s1
        simp only [UOut.lib.injEq] at h2
        obtain ⟨rfl, rfl, rfl⟩ := h2
        exact ih s1 h1 _ rfl
      | prim hl hs =>
        obtain ⟨r, _, h2⟩ := (step_none (t := tid) hp).1 hs; exact (out_ne_prim h2.symm).elim
      | gettid hl hs =>
        obtain ⟨r, _, h2⟩ := (step_none (t := tid) hp).1 hs; exact (out_ne_sys h2.symm).elim
      | setTid hl hs =>
        obtain ⟨r, _, h2⟩ := (step_none (t := tid) hp).1 hs; exact (out_ne_sys h2.symm).elim
      | exit hl hs =>
        obtain ⟨r, _, h2⟩ := (step_none (t := tid) hp).1 hs; exact (out_ne_sys h2.symm).elim
      | exitGroup hl hs =>
        obtain ⟨r, _, h2⟩ := (step_none (t := tid) hp).1 hs; exact (out_ne_sys h2.symm).elim
      | base hl hs =>
        obtain ⟨r, _, h2⟩ := (step_none (t := tid) hp).1 hs; exact (out_ne_sys h2.symm).elim

/-- `mtDyn` never makes a system call. -/
theorem noThreadSys (x : SoloCfg Core Ghost) : NoThreadSys (mtDyn W prims) tid x := by
  intro nr args k ch hs
  exfalso
  change step W prims tid x.st x.mem x.g _ at hs
  unfold step at hs
  split at hs
  · split at hs
    · obtain ⟨_, _, h⟩ := hs; cases h
    · cases hs
  · obtain ⟨r, _, h⟩ := hs; exact out_ne_sys h.symm

theorem must_mt {R Q : XPState → Prop} {c : Core} {m : Memory} {g : Ghost}
    (h : Must (procX W) R Q (toX c m g))
    (hR : ∀ s, R s → prims.find? (·.1 == s.p.m.core.rip) = none) :
    SMust (MtStep (mtDyn W prims) sc P base) (MtFault (mtDyn W prims) sc P)
      (fun C => ∃ y, SoloRel tid y C ∧ Q (xs y)) (MtCfg.init (S := sc.S) tid c m g) :=
  solo_must (must_solo h hR ⟨c, m, {}, g, none⟩ rfl) (fun y _ => noThreadSys y) soloRel_init

end Silmaril.Proofs.Elf.Link.Dyn.Mt
