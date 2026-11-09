module

public import Silmaril.Proofs.X86.Bir9.Step

/-!
# Symbolic forms of the instructions, with their soundness lemmas

One soundness lemma per instruction family of `Silmaril.X86.Ext.exec` (and of the extension
instructions `XInstr`); the symbolic forms are defined in `Silmaril.X86.Bir9.Defs`. Each lemma has the shape

```
Rel σ env s mem → StepRel (exec i s mem len) (runStmts (sI σ len …).1 env) (sI σ len …).2
```

and `symStep_sound` dispatches to them.
-/

@[expose] public section

namespace Silmaril.X86.Bir9

open Silmaril.X86 (Reg Word State Flags AluOp Byte pushWord popWord wordOfBytes?)
open Silmaril.X86.Ext
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)

variable {σ : SState} {env : Env} {s : State} {mem : Memory}

theorem retire_map (next : Word) (o : Option Word) (g : Word → State × Memory) :
    retire next (o.map g) = match o with
      | none => .dataFault
      | some x => retire next (some (g x)) := by
  cases o <;> rfl

/-- After a read, finish with a pure state change and retire. -/
theorem finish_pure {σ0 σ1 σ' : SState} {env env1 : Env} {s s' : State} {mem : Memory} {e : E}
    (h : Rel σ0 env s mem) (hok : ReadOK σ0 σ1 env env1 s mem e) (len : Nat)
    (h' : Rel σ' env1 s' mem) :
    StepRel (retire (s.rip + BitVec.ofNat 64 len) (some (s', mem))) (runStmts [] env1)
      { σ' with rip := nxOf σ0 len } :=
  (ORel.pure h').retire (hok.nx h len) (by rw [hok.rel.len]; exact hok.nxw h len)

/-! ## Moves -/

theorem sMov_sound (h : Rel σ env s mem) (len : Nat) (sz : Sz) (dst : RM) {e : E} (he : e.wf σ.n)
    {v : BitVec sz.bits} (hv : v = (e.den env).setWidth sz.bits) :
    StepRel (retire (s.rip + BitVec.ofNat 64 len) (writeRM sz dst v s mem (s.rip + BitVec.ofNat 64 len)))
      (runStmts (sMov σ len sz dst e).1 env) (sMov σ len sz dst e).2 := by
  subst hv
  exact (sWriteRM_sound h (nxOf_den h len) (nxOf_wfn h len) sz dst he).retire (nxOf_den h len)
    (nxOf_wf h len)

theorem sMovN_sound (h : Rel σ env s mem) (len : Nat) (n : Narrow) (dst : RM) {e : E}
    (he : e.wf σ.n) {v : BitVec n.bits} (hv : v = (e.den env).setWidth n.bits) :
    StepRel (retire (s.rip + BitVec.ofNat 64 len)
        (writeNarrow n dst v s mem (s.rip + BitVec.ofNat 64 len)))
      (runStmts (sMovN σ len n dst e).1 env) (sMovN σ len n dst e).2 := by
  subst hv
  exact (sWriteN_sound h (nxOf_den h len) (nxOf_wfn h len) n dst he).retire (nxOf_den h len)
    (nxOf_wf h len)

theorem sSet_sound (h : Rel σ env s mem) (len : Nat) (r : Reg) {e : E} (he : e.wf σ.n)
    {v : Word} (hv : v = e.den env) :
    StepRel (retire (s.rip + BitVec.ofNat 64 len) (some (s.write r v, mem)))
      (runStmts (sSet σ len r e).1 env) (sSet σ len r e).2 :=
  pure_sound h len (h.setReg' r he hv)

theorem sReadSet_sound (h : Rel σ env s mem) (len : Nat) (op : RM) (k : Nat) (r : Reg)
    (mk : E → E) (g : Word → Word)
    (hmk : ∀ e n, e.wf n → (∀ q, (σ.regs q).wf n) → (mk e).wf n)
    (hg : ∀ env1 x e, env.Ext env1 → x = e.den env1 → g x = (mk e).den env1) :
    StepRel (match rawRead op s mem (s.rip + BitVec.ofNat 64 len) k with
        | none => .dataFault
        | some x => retire (s.rip + BitVec.ofNat 64 len) (some (s.write r (g x), mem)))
      (runStmts (sReadSet σ len op k r mk).1 env) (sReadSet σ len op k r mk).2 := by
  have hnx := nxOf_den h len
  cases hr : rawRead op s mem (s.rip + BitVec.ofNat 64 len) k with
  | none => simp only [sReadSet]; rw [runStmts_append, sRead_none h hnx hr]; rfl
  | some xw =>
    obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
    simp only [sReadSet]
    apply StepRel.prepend hrun
    refine finish_pure h hok len (hok.rel.setReg' r (hmk _ _ hok.wf ?_) (hg env1 xw _ hok.ext hx))
    intro q; rw [← hok.regs]; exact hok.rel.wf.1 q

/-! ## The instruction table -/

theorem immW_den (w : Nat) (hw : w ≤ 64) (b : BitVec w) (env : Env) :
    ((immW w b).den env).setWidth w = b := setWidth_64_setWidth hw b

/-! ## More generic shapes -/

theorem sFlags_sound (h : Rel σ env s mem) (len : Nat) {f : F} (hf : f.wf σ.n) {fl : Flags}
    (hfl : fl = f.den env) :
    StepRel (retire (s.rip + BitVec.ofNat 64 len) (some ({ s with flags := fl }, mem)))
      (runStmts (sFlags σ len f).1 env) (sFlags σ len f).2 :=
  pure_sound h len (h.setFlags' hf hfl)

theorem sReadSetF_sound (h : Rel σ env s mem) (len : Nat) (op : RM) (k : Nat) (r : Reg)
    (mk : E → E) (fl : E → F) (g : Word → Word) (gf : Word → Flags)
    (hmk : ∀ e n, σ.n ≤ n → e.wf n → (mk e).wf n)
    (hfl : ∀ e n, σ.n ≤ n → e.wf n → (fl e).wf n)
    (hg : ∀ env1 x e, env.Ext env1 → x = e.den env1 → g x = (mk e).den env1)
    (hgf : ∀ env1 x e, env.Ext env1 → x = e.den env1 → gf x = (fl e).den env1) :
    StepRel (match rawRead op s mem (s.rip + BitVec.ofNat 64 len) k with
        | none => .dataFault
        | some x => retire (s.rip + BitVec.ofNat 64 len)
            (some ({ s.write r (g x) with flags := gf x }, mem)))
      (runStmts (sReadSetF σ len op k r mk fl).1 env) (sReadSetF σ len op k r mk fl).2 := by
  have hnx := nxOf_den h len
  cases hr : rawRead op s mem (s.rip + BitVec.ofNat 64 len) k with
  | none => simp only [sReadSetF]; rw [runStmts_append, sRead_none h hnx hr]; rfl
  | some xw =>
    obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
    simp only [sReadSetF]
    apply StepRel.prepend hrun
    have h1 := hok.rel.setReg' r (hmk _ _ (hok.mono h) hok.wf) (hg env1 xw _ hok.ext hx)
    have h2 := h1.setFlags' (f := fl (sRead σ (nxOf σ len) k op).2.1)
      (by simpa [SState.setReg] using hfl _ _ (hok.mono h) hok.wf) (hgf env1 xw _ hok.ext hx)
    exact finish_pure h hok len h2

theorem sReadF_sound (h : Rel σ env s mem) (len : Nat) (op : RM) (k : Nat)
    (fl : E → F) (gf : Word → Flags)
    (hfl : ∀ e n, σ.n ≤ n → e.wf n → (fl e).wf n)
    (hgf : ∀ env1 x e, env.Ext env1 → x = e.den env1 → gf x = (fl e).den env1) :
    StepRel (match rawRead op s mem (s.rip + BitVec.ofNat 64 len) k with
        | none => .dataFault
        | some x => retire (s.rip + BitVec.ofNat 64 len) (some ({ s with flags := gf x }, mem)))
      (runStmts (sReadF σ len op k fl).1 env) (sReadF σ len op k fl).2 := by
  have hnx := nxOf_den h len
  cases hr : rawRead op s mem (s.rip + BitVec.ofNat 64 len) k with
  | none => simp only [sReadF]; rw [runStmts_append, sRead_none h hnx hr]; rfl
  | some xw =>
    obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
    simp only [sReadF]
    apply StepRel.prepend hrun
    exact finish_pure h hok len
      (hok.rel.setFlags' (hfl _ _ (hok.mono h) hok.wf) (hgf env1 xw _ hok.ext hx))

theorem sRMW_sound (h : Rel σ env s mem) (len : Nat) (sz : Sz) (dst : RM) (val : E → E)
    (V : BitVec sz.bits → BitVec sz.bits)
    (hval : ∀ e n, σ.n ≤ n → e.wf n → (val e).wf n)
    (hV : ∀ env1 e, env.Ext env1 → V ((e.den env1).setWidth sz.bits) = ((val e).den env1).setWidth sz.bits) :
    StepRel (match readRM sz dst s mem (s.rip + BitVec.ofNat 64 len) with
        | none => .dataFault
        | some x => retire (s.rip + BitVec.ofNat 64 len)
            (writeRM sz dst (V x) s mem (s.rip + BitVec.ofNat 64 len)))
      (runStmts (sRMW σ len sz dst val none).1 env) (sRMW σ len sz dst val none).2 := by
  have hnx := nxOf_den h len
  rw [readRM_eq]
  cases hr : rawRead dst s mem (s.rip + BitVec.ofNat 64 len) sz.bytes with
  | none => simp only [Option.map_none, sRMW]; rw [runStmts_append, sRead_none h hnx hr]; rfl
  | some xw =>
    obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
    simp only [Option.map_some, sRMW, Option.map_none, Option.getD_none]
    apply StepRel.prepend hrun
    rw [hx, hV env1 _ hok.ext]
    have hw := sWriteRM_sound hok.rel (hok.nx h len) (hok.nxw h len) sz dst
      (e := val (sRead σ (nxOf σ len) sz.bytes dst).2.1) (hval _ _ (hok.mono h) hok.wf)
    have := hw.retire (hok.nx h len) (by rw [hok.rel.len]; exact hok.nxw h len)
    simpa using this

theorem sRMWF_sound (h : Rel σ env s mem) (len : Nat) (sz : Sz) (dst : RM) (val : E → E)
    (fl : E → F) (V : BitVec sz.bits → BitVec sz.bits) (FL : BitVec sz.bits → Flags)
    (hval : ∀ e n, σ.n ≤ n → e.wf n → (val e).wf n)
    (hfl : ∀ e n, σ.n ≤ n → e.wf n → (fl e).wf n)
    (hV : ∀ env1 e, env.Ext env1 → V ((e.den env1).setWidth sz.bits) = ((val e).den env1).setWidth sz.bits)
    (hFL : ∀ env1 e, env.Ext env1 → FL ((e.den env1).setWidth sz.bits) = (fl e).den env1) :
    StepRel (match readRM sz dst s mem (s.rip + BitVec.ofNat 64 len) with
        | none => .dataFault
        | some x => retire (s.rip + BitVec.ofNat 64 len)
            ((writeRM sz dst (V x) s mem (s.rip + BitVec.ofNat 64 len)).map fun r =>
              ({ r.1 with flags := FL x }, r.2)))
      (runStmts (sRMW σ len sz dst val (some fl)).1 env) (sRMW σ len sz dst val (some fl)).2 := by
  have hnx := nxOf_den h len
  rw [readRM_eq]
  cases hr : rawRead dst s mem (s.rip + BitVec.ofNat 64 len) sz.bytes with
  | none => simp only [Option.map_none, sRMW]; rw [runStmts_append, sRead_none h hnx hr]; rfl
  | some xw =>
    obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
    simp only [Option.map_some, sRMW, Option.getD_some]
    apply StepRel.prepend hrun
    rw [hx, hV env1 _ hok.ext, hFL env1 _ hok.ext]
    have hw := sWriteRM_sound hok.rel (hok.nx h len) (hok.nxw h len) sz dst
      (e := val (sRead σ (nxOf σ len) sz.bytes dst).2.1) (hval _ _ (hok.mono h) hok.wf)
    have hflw : (fl (sRead σ (nxOf σ len) sz.bytes dst).2.1).wf env1.vals.length := by
      rw [hok.rel.len]; exact hfl _ _ (hok.mono h) hok.wf
    have := (hw.flags _ hflw).retire (hok.nx h len) (by rw [hok.rel.len]; exact hok.nxw h len)
    simpa using this

end Silmaril.X86.Bir9
