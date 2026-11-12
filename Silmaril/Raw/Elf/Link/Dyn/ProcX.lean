module

public import Silmaril.Elf.Link.Dyn.ProcX.Defs
public import Silmaril.Elf.Link.Dyn.Cert.Thms
public import Silmaril.X86.Sse9.Thms

/-! # The process machine with XMM registers: proof rules

PROVED (standard axioms):

* **`mustX_of_must`**: a `Proc.MustQ` result holds of `procX`, whatever the XMM registers
  (a run of `proc` never reaches an SSE instruction, since `proc` stops there); `mustX_bind`
  continues it;
* `mustX_insn`: one `Open9` instruction of the image, XMM registers unchanged;
* **`mustX_sse`**: one SSE instruction of the image, checked against `Sse9.decodeL` (closed by
  `decide`) and run by `Sse9.exec`; `sse_fit`: the instruction lies inside its chunk;
* `mustX_seqX`, **`mustX_blkX_at`**: a checked block certificate (`Cert.BlkX`) on `procX`, the
  XMM registers unchanged.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.ProcX

open Silmaril.X86 (Word Byte MState State)
open Silmaril.Process (Memory)
open Silmaril.X86.RelIsa (Res Must)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.Bir9 (Block Xmm XState liftR)
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Cert

/-! ## `proc` results carry over -/

theorem mustX_of_must_aux {W : World} {Q : PState → Prop} {p : PState} (h : MustQ W Q p) :
    ∀ s : XPState, s.p = p → MustX W (fun t => Q t.p) s := by
  induction h with
  | done hq => intro s hs; exact Must.done (by rw [hs]; exact hq)
  | @step p _ hns _ ih =>
    intro s hs
    subst hs
    refine Must.step trivial ?_ ?_
    · intro hst
      apply hns
      simp only [procX, step] at hst
      simp only [proc, Proc.step]
      split at hst
      · rename_i hd; simp only [hd]
      · rename_i hd
        simp only [hd]
        split at hst
        · rename_i hin
          simp only [hin, ↓reduceIte]
          cases ho : Silmaril.X86.Open9.step s.p.m with
          | none => simp
          | some m' =>
            rw [Silmaril.X86.Sse9.step_of_open9 (x := ⟨s.p.m, s.x⟩) ho] at hst
            cases hst
        · rename_i hin
          simp only [hin, ↓reduceIte]
          obtain ⟨r', h1, h2⟩ := hst
          cases r' with
          | ok _ => cases h2
          | stop => exact h1
    · intro t ht
      simp only [procX, step] at ht
      split at ht
      · cases ht
      · rename_i hd
        split at ht
        · rename_i hin
          cases ho : Silmaril.X86.Open9.step s.p.m with
          | none =>
            exfalso; apply hns
            simp only [proc, Proc.step, hd, hin, ↓reduceIte, ho]
          | some m' =>
            rw [Silmaril.X86.Sse9.step_of_open9 (x := ⟨s.p.m, s.x⟩) ho] at ht
            simp only [Res.ok.injEq] at ht
            subst ht
            exact ih ⟨m', s.p.g⟩ (by simp only [proc, Proc.step, hd, hin, ↓reduceIte, ho]) _ rfl
        · rename_i hin
          obtain ⟨r', h1, h2⟩ := ht
          cases r' with
          | stop => cases h2
          | ok u =>
            exact ih u (by simp only [proc, Proc.step, hd, hin, ↓reduceIte]; exact h1) _ h2

/-- **Every `proc` result holds of `procX`**, whatever the XMM registers. -/
theorem mustX_of_must {W : World} {Q : PState → Prop} {s : XPState} (h : MustQ W Q s.p) :
    MustX W (fun t => Q t.p) s :=
  mustX_of_must_aux h s rfl

/-- A `proc` result, continued on `procX`. -/
theorem mustX_bind {W : World} {Q : PState → Prop} {R : XPState → Prop} {s : XPState}
    (h : MustQ W Q s.p) (k : ∀ t : XPState, Q t.p → MustX W R t) : MustX W R s :=
  Must.bind (mustX_of_must h) k

/-! ## Instructions -/

/-- **One `Open9` instruction of the image** on `procX` (XMM registers unchanged). -/
theorem mustX_insn {W : World} {Q : XPState → Prop} {s : XPState} {base : Word}
    {code : List Byte} {o l : Nat} {i : Silmaril.X86.Ext9.Instr} (hd : s.p.g.done = none)
    (hin : W.InImage s.p.m.core.rip.toNat) (hl : Loaded s.p.m.memory base code)
    (hrip : s.p.m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : Silmaril.X86.Open9.decode ((code.drop o).take l) = some (i, l))
    (h : WP (Silmaril.X86.Ext9.exec i s.p.m.core s.p.m.memory l)
      fun c m => MustX W Q ⟨⟨⟨c, m⟩, s.p.g⟩, s.x⟩) : MustX W Q s := by
  revert h
  cases e : Silmaril.X86.Ext9.exec i s.p.m.core s.p.m.memory l with
  | ok c m =>
    intro h
    have hs : Silmaril.X86.Sse9.step ⟨s.p.m, s.x⟩ = some ⟨⟨c, m⟩, s.x⟩ :=
      Silmaril.X86.Sse9.step_of_open9 (Silmaril.X86.Open9.step_of_listed hl hrip hfit hdec e)
    refine Must.step trivial ?_ ?_
    · intro hstop
      simp only [procX, step, hd, hin, ↓reduceIte, hs] at hstop
      cases hstop
    · intro t ht
      simp only [procX, step, hd, hin, ↓reduceIte, hs, Res.ok.injEq] at ht
      subst ht
      exact h
  | _ => intro h; exact h.elim

/-- The weakest precondition of an SSE instruction's result. -/
def WPX : Silmaril.X86.Sse9.XResult →
    (State → Silmaril.X86.Sse9.XFile → Memory → Prop) → Prop
  | .ok c x m, P => P c x m
  | _, _ => False

/-- A listed SSE instruction lies inside its code chunk. -/
theorem sse_fit {code : List Byte} {o l : Nat} {i : Silmaril.X86.Sse9.Instr}
    (h : Silmaril.X86.Sse9.decodeL ((code.drop o).take l) = some (i, l)) : o + l ≤ code.length := by
  unfold Silmaril.X86.Sse9.decodeL at h
  split at h
  · rename_i i' n hd
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have h1 := hc.2.2.2.2.1
      unfold Silmaril.X86.Sse9.decodeSse at hd
      split at hd
      · simp only [Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨-, hn⟩ := hd
        have : n ≤ ((code.drop o).take n).length := by omega
        simp only [List.length_take, List.length_drop] at this
        omega
      · cases hd
    · cases h
  · cases h

/-- **One SSE instruction of the image**, decoded by `Sse9.decodeL` and run by `Sse9.exec`. -/
theorem mustX_sse {W : World} {Q : XPState → Prop} {s : XPState} {base : Word}
    {code : List Byte} {o l : Nat} {i : Silmaril.X86.Sse9.Instr} (hd : s.p.g.done = none)
    (hin : W.InImage s.p.m.core.rip.toNat) (hl : Loaded s.p.m.memory base code)
    (hrip : s.p.m.core.rip = base + BitVec.ofNat 64 o)
    (hdec : Silmaril.X86.Sse9.decodeL ((code.drop o).take l) = some (i, l))
    (h : WPX (Silmaril.X86.Sse9.exec i s.p.m.core s.x s.p.m.memory
        (s.p.m.core.rip + BitVec.ofNat 64 l))
      fun c xs m => MustX W Q ⟨⟨⟨c, m⟩, s.p.g⟩, xs⟩) : MustX W Q s := by
  revert h
  cases e : Silmaril.X86.Sse9.exec i s.p.m.core s.x s.p.m.memory
      (s.p.m.core.rip + BitVec.ofNat 64 l) with
  | ok c xs m =>
    intro h
    have hs : Silmaril.X86.Sse9.step ⟨s.p.m, s.x⟩ = some ⟨⟨c, m⟩, xs⟩ :=
      Silmaril.X86.Sse9.step_of_listed_sse (x := ⟨s.p.m, s.x⟩) hl hrip (sse_fit hdec) hdec e
    refine Must.step trivial ?_ ?_
    · intro hstop
      simp only [procX, step, hd, hin, ↓reduceIte, hs] at hstop
      cases hstop
    · intro t ht
      simp only [procX, step, hd, hin, ↓reduceIte, hs, Res.ok.injEq] at ht
      subst ht
      exact h
  | _ => intro h; exact h.elim

/-! ## Block certificates on `procX` -/

/-- What a listing run must lead to, on `procX`. -/
def XPostX (W : World) (Q : XPState → Prop) (g : Ghost) (xs : Silmaril.X86.Sse9.XFile) :
    Silmaril.X86.Bir9.XResult → Prop
  | .ok t m => MustX W Q ⟨⟨⟨t.core, m⟩, g⟩, xs⟩
  | _ => False

set_option maxHeartbeats 400000 in
theorem mustX_seqX {W : World} {Q : XPState → Prop} {base : Word} {code : List Byte} :
    ∀ (L : List (Silmaril.X86.Bir9X.XL × Nat)) (o : Nat) (s : XPState) (x : Xmm),
    seqAtX code o L = true → s.p.g.done = none →
    (∀ o', o ≤ o' → o' < o + lenLX L → W.InImage (base + BitVec.ofNat 64 o').toNat) →
    Loaded s.p.m.memory base code → CodeRO s.p.m.memory base code →
    (L ≠ [] → s.p.m.core.rip = base + BitVec.ofNat 64 o) →
    XPostX W Q s.p.g s.x (Silmaril.X86.Bir9X.execBlockX L ⟨s.p.m.core, x⟩ s.p.m.memory) →
    MustX W Q s
  | [], _, s, x, _, _, _, _, _, _, h => by
    simp only [Silmaril.X86.Bir9X.execBlockX, XPostX] at h; exact h
  | (i, l) :: rest, o, s, x, hok, hd, hin, hl, hro, hrip, h => by
    simp only [seqAtX] at hok
    split at hok
    · cases hok
    · rename_i j hj
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨⟨⟨hdec, hl0⟩, hfit⟩, hft⟩, hlift⟩, hrest⟩ := hok
      have hrip' := hrip (List.cons_ne_nil _ _)
      have hx := xl_exec hj x s.p.m.core s.p.m.memory l
      obtain ⟨c, m', he⟩ : ∃ c m', Silmaril.X86.Ext9.exec j s.p.m.core s.p.m.memory l = .ok c m' := by
        revert h
        simp only [Silmaril.X86.Bir9X.execBlockX, hx]
        cases Silmaril.X86.Ext9.exec j s.p.m.core s.p.m.memory l <;> simp [liftR, XPostX]
      have hx' : i.exec ⟨s.p.m.core, x⟩ s.p.m.memory l = .ok ⟨c, x⟩ m' := by rw [hx, he]; rfl
      have hb : Silmaril.X86.Bir9X.execBlockX ((i, l) :: rest) ⟨s.p.m.core, x⟩ s.p.m.memory =
          Silmaril.X86.Bir9X.execBlockX rest ⟨c, x⟩ m' := by
        simp only [Silmaril.X86.Bir9X.execBlockX, hx']
      rw [hb] at h
      obtain ⟨bi, hbi⟩ := Option.isSome_iff_exists.mp hlift
      have hfr : Frame s.p.m.memory m' := by
        have h1 := Silmaril.X86.Bir9X.liftBlockX_sound hbi ⟨s.p.m.core, x⟩ s.p.m.memory
        have h2 : Silmaril.X86.Bir9X.execBlockX [(i, l)] ⟨s.p.m.core, x⟩ s.p.m.memory =
            .ok ⟨c, x⟩ m' := by
          simp only [Silmaril.X86.Bir9X.execBlockX, hx']
        rw [h2] at h1
        exact block_frame h1.symm
      refine mustX_insn hd (by rw [hrip']; exact hin o (Nat.le_refl _) (by simp only [lenLX]; omega))
        hl hrip' hfit hdec ?_
      rw [he, WP_ok]
      refine mustX_seqX rest (o + l) ⟨⟨⟨c, m'⟩, s.p.g⟩, s.x⟩ x hrest hd
        (fun o' h1 h2 => hin o' (by omega) (by simp only [lenLX]; omega))
        (loaded_frame hl hro hfr) (codeRO_frame hro hfr) (fun hne => ?_) h
      have hf : Silmaril.X86.BlockCert9.fallsThrough9 j = true := by
        cases rest with
        | nil => exact absurd rfl hne
        | cons _ _ => simpa using hft
      show c.rip = _
      rw [exec_rip9 hf he, hrip', ripadd]

/-- The state a block leaves on `procX` (XMM registers unchanged). -/
def postX (b : Block) (s : XPState) (env : Silmaril.X86.Bir9.Env) : XPState :=
  ⟨post b s.p env, s.x⟩

/-- **A checked `BlkX` certificate on `procX`** (as `Cert.must_blkX_at`). -/
theorem mustX_blkX_at {W : World} {Q : XPState → Prop} {s : XPState} {b : Word} {cb : Nat}
    {code : List Byte} (B : BlkX) (hok : B.ok code = true) (hd : s.p.g.done = none)
    (himg : ∀ n, n < code.length → W.InImage (b + BitVec.ofNat 64 (cb + n)).toNat)
    (hl : Loaded s.p.m.memory (b + BitVec.ofNat 64 cb) code)
    (hro : CodeRO s.p.m.memory (b + BitVec.ofNat 64 cb) code)
    (hrip : s.p.m.core.rip = b + BitVec.ofNat 64 (cb + B.off))
    (h : Wp B.b.stmts (env0 s.p.m) fun env => MustX W Q (postX B.b s env)) : MustX W Q s := by
  have hfit : B.off + B.len ≤ code.length ∨ B.L = [] := by
    simp only [BlkX.ok, Bool.and_eq_true] at hok; exact seqAtX_fit _ _ hok.1
  simp only [BlkX.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hseq, hlift⟩ := hok
  refine mustX_seqX B.L B.off s (fun _ => 0) hseq hd (fun o' h1 h2 => ?_) hl hro
    (fun _ => by rw [hrip, ripadd]) ?_
  · rw [ripadd]
    rcases hfit with hf | hn
    · exact himg o' (by simp only [BlkX.len] at hf; omega)
    · simp [hn, lenLX] at h2; omega
  · rw [Silmaril.X86.Bir9X.liftBlockX_sound hlift]
    obtain ⟨env, he, hP⟩ := (wp_iff _ _ _).1 h
    unfold Block.run
    simp only [env0] at he
    rw [he]
    exact hP

end Silmaril.Elf.Link.Dyn.ProcX
