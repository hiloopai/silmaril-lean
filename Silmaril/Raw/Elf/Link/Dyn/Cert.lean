module

public import Silmaril.Elf.Link.Dyn.Cert.Defs
public import Silmaril.Elf.Link.Dyn.Proc.Thms
public import Silmaril.X86.Bir9.Thms
public import Silmaril.X86.BlockCert9.Thms
public import Silmaril.X86.Bir9.X.Thms

/-! # Block certificates: the checker lemma

PROVED (standard axioms):

* `stmt_frame`, `runStmts_frame`, `block_frame`: a Bir9 block keeps the memory map and every
  byte that is not writable (its stores are permission-checked);
* `must_seq`: a checked listing (`seqAt`) whose run succeeds is a run of the process machine
  inside the executable's image; the code stays loaded because every instruction lifts on its
  own, so it keeps the bytes that are not writable, and the code is not writable (`CodeRO`);
* **`must_blk`**: a checked certificate (`Blk.ok`, closed by `decide +kernel`) and the weakest
  precondition `Wp` of its block's statements give a `MustQ` step from the block's entry to the
  state the block describes (`post`);
* `wp_nil`, `wp_load`, `wp_store`, `wp_push`, `wp_pop`, `wp_cond`, `wp_chk`, `wp_align`: the
  statement rules. Loaded values and condition outcomes are universally quantified (the caller
  gets the value and the equation that produced it), stores become `Proc.storeMem`;
* `must_seqX`, **`must_blkX`**, `must_blkX_at`: the same for certificates over the extended
  lifter `Bir9X` (`BlkX`: `Ext8` byte forms, ADC/SBB);
* `eval_some`: a condition on fully defined flags (`alu`, `logic`, `test`) has an outcome;
* tactics `blk_wp` (apply the statement rules, leaving the side conditions) and `blk_simp`
  (evaluate block terms in an environment).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Cert

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.X86.Bir9 (LInstr Block Stmt Env XState XResult Xmm execBlock liftR E F)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn.Proc

/-! ## The memory frame of a block -/

/-- `m'` has `m`'s memory map and the bytes of `m` that are not writable. -/
def Frame (m m' : Memory) : Prop :=
  m'.regions = m.regions ∧ ∀ a, m.permits .write a = false → m'.bytes.get? a = m.bytes.get? a

theorem Frame.refl (m : Memory) : Frame m m := ⟨rfl, fun _ _ => rfl⟩

theorem permits_of_regions {m m' : Memory} (h : m'.regions = m.regions) (acc : Access) (a : Nat) :
    m'.permits acc a = m.permits acc a := by
  unfold Memory.permits; rw [h]

theorem Frame.trans {m₁ m₂ m₃ : Memory} (h₁ : Frame m₁ m₂) (h₂ : Frame m₂ m₃) : Frame m₁ m₃ :=
  ⟨h₂.1.trans h₁.1, fun a ha =>
    (h₂.2 a (by rw [permits_of_regions h₁.1]; exact ha)).trans (h₁.2 a ha)⟩

theorem Frame.keeps {m m' : Memory} (h : Frame m m') :
    Keeps (fun a => m.permits .write a = false) m m' :=
  fun a ha => ⟨h.2 a ha, fun acc => permits_of_regions h.1 acc a⟩

theorem frame_write {m m' : Memory} {a : Nat} {bs : List Byte} (h : m.writeBytes a bs = some m') :
    Frame m m' := by
  have hw := Memory.writeBytes_writesOnly h
  have hp := Memory.writeBytes_permitted h
  refine ⟨hw.1, fun x hx => hw.2 x ?_⟩
  rw [Memory.Permitted, Memory.checkSpan_iff] at hp
  by_contra hc
  have := hp.2.2 (x - a) (by omega)
  rw [show a + (x - a) = x by omega, hx] at this
  cases this

theorem stmt_frame {st : Stmt} {env env' : Env} (h : st.run env = .ok env') :
    Frame env.mem env'.mem := by
  cases st with
  | load k a =>
    simp only [Stmt.run] at h; split at h
    · cases h
    · cases h; exact Frame.refl _
  | store k a x =>
    simp only [Stmt.run] at h; split at h
    · cases h
    · rename_i m hm; cases h; exact frame_write hm
  | push a x =>
    simp only [Stmt.run] at h; split at h
    · cases h
    · rename_i m hm; cases h; exact frame_write hm
  | pop a =>
    simp only [Stmt.run] at h; split at h
    · cases h
    · cases h; exact Frame.refl _
  | cond c f =>
    simp only [Stmt.run] at h; split at h
    · cases h
    · cases h; exact Frame.refl _
  | trap => simp only [Stmt.run] at h; cases h
  | align a k =>
    simp only [Stmt.run] at h; split at h
    · cases h; exact Frame.refl _
    · cases h
  | chk o a b c =>
    simp only [Stmt.run] at h; split at h
    · cases h; exact Frame.refl _
    · cases h

theorem runStmts_frame : ∀ {sts : List Stmt} {env env' : Env},
    Silmaril.X86.Bir9.runStmts sts env = .ok env' → Frame env.mem env'.mem
  | [], env, env', h => by simp only [Silmaril.X86.Bir9.runStmts] at h; cases h; exact Frame.refl _
  | st :: rest, env, env', h => by
    simp only [Silmaril.X86.Bir9.runStmts] at h
    split at h
    · cases h
    · rename_i e he; exact (stmt_frame he).trans (runStmts_frame h)

theorem block_frame {b : Block} {x x' : XState} {m m' : Memory} (h : b.run x m = .ok x' m') :
    Frame m m' := by
  unfold Block.run at h
  split at h
  · rename_i f _; cases f <;> cases h
  · rename_i env he; cases h; exact runStmts_frame he

/-! ## Instructions -/

theorem linstr_exec {i : LInstr} {j : Silmaril.X86.Ext9.Instr} (hj : Silmaril.X86.Bir9.toX9 i = some j)
    (x : Xmm) (c : State) (m : Memory) (l : Nat) :
    i.exec ⟨c, x⟩ m l = liftR x (Silmaril.X86.Ext9.exec j c m l) := by
  cases i <;> simp [Silmaril.X86.Bir9.toX9] at hj <;> subst hj <;> rfl

theorem exec_rip9 {j : Silmaril.X86.Ext9.Instr} (hf : Silmaril.X86.BlockCert9.fallsThrough9 j = true)
    {c c' : State} {m m' : Memory} {l : Nat} (h : Silmaril.X86.Ext9.exec j c m l = .ok c' m') :
    c'.rip = c.rip + BitVec.ofNat 64 l := by
  rcases j with (e | e) | n
  · exact Silmaril.X86.BlockCert9.exec_rip hf h
  · simp [Silmaril.X86.BlockCert9.fallsThrough9] at hf
  · exact Silmaril.X86.BlockCert9.execNew_rip hf h

theorem loaded_frame {m m' : Memory} {base : Word} {code : List Byte} (hl : Loaded m base code)
    (hro : CodeRO m base code) (hf : Frame m m') : Loaded m' base code := by
  unfold Loaded at hl ⊢
  rw [hf.keeps.fetchBytes (fun k hk => hro k hk)]
  exact hl

theorem codeRO_frame {m m' : Memory} {base : Word} {code : List Byte} (hro : CodeRO m base code)
    (hf : Frame m m') : CodeRO m' base code := fun k hk => by
  rw [permits_of_regions hf.1]; exact hro k hk

/-- What a listing run must lead to. -/
def XPost (W : World) (Q : PState → Prop) (g : Ghost) : XResult → Prop
  | .ok t m => MustQ W Q ⟨⟨t.core, m⟩, g⟩
  | _ => False

set_option maxHeartbeats 400000 in
/-- **A checked listing runs on the process machine.** -/
theorem must_seq {W : World} {Q : PState → Prop} {base : Word} {code : List Byte} :
    ∀ (L : List (LInstr × Nat)) (o : Nat) (s : PState) (x : Xmm),
    seqAt code o L = true → s.g.done = none →
    (∀ o', o ≤ o' → o' < o + lenL L → W.InImage (base + BitVec.ofNat 64 o').toNat) →
    Loaded s.m.memory base code → CodeRO s.m.memory base code →
    (L ≠ [] → s.m.core.rip = base + BitVec.ofNat 64 o) →
    XPost W Q s.g (execBlock L ⟨s.m.core, x⟩ s.m.memory) → MustQ W Q s
  | [], _, s, x, _, _, _, _, _, _, h => by
    simp only [execBlock, XPost] at h; exact h
  | (i, l) :: rest, o, s, x, hok, hd, hin, hl, hro, hrip, h => by
    simp only [seqAt] at hok
    split at hok
    · cases hok
    · rename_i j hj
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨⟨⟨hdec, hl0⟩, hfit⟩, hft⟩, hlift⟩, hrest⟩ := hok
      have hrip' := hrip (List.cons_ne_nil _ _)
      have hx := linstr_exec hj x s.m.core s.m.memory l
      obtain ⟨c, m', he⟩ : ∃ c m', Silmaril.X86.Ext9.exec j s.m.core s.m.memory l = .ok c m' := by
        revert h
        simp only [execBlock, hx]
        cases Silmaril.X86.Ext9.exec j s.m.core s.m.memory l <;> simp [liftR, XPost]
      have hx' : i.exec ⟨s.m.core, x⟩ s.m.memory l = .ok ⟨c, x⟩ m' := by rw [hx, he]; rfl
      have hb : execBlock ((i, l) :: rest) ⟨s.m.core, x⟩ s.m.memory = execBlock rest ⟨c, x⟩ m' := by
        simp only [execBlock, hx']
      rw [hb] at h
      -- the instruction's memory frame, from its own lift
      obtain ⟨bi, hbi⟩ := Option.isSome_iff_exists.mp hlift
      have hfr : Frame s.m.memory m' := by
        have h1 := Silmaril.X86.Bir9.liftBlock_sound hbi ⟨s.m.core, x⟩ s.m.memory
        have h2 : execBlock [(i, l)] ⟨s.m.core, x⟩ s.m.memory = .ok ⟨c, x⟩ m' := by
          simp only [execBlock, hx']
        rw [h2] at h1
        exact block_frame h1.symm
      refine must_insn hd (by rw [hrip']; exact hin o (Nat.le_refl _) (by simp only [lenL]; omega)) hl hrip'
        hfit hdec ?_
      rw [he, WP_ok]
      refine must_seq rest (o + l) ⟨⟨c, m'⟩, s.g⟩ x hrest hd
        (fun o' h1 h2 => hin o' (by omega) (by simp only [lenL]; omega))
        (loaded_frame hl hro hfr) (codeRO_frame hro hfr) (fun hne => ?_) h
      have hf : Silmaril.X86.BlockCert9.fallsThrough9 j = true := by
        cases rest with
        | nil => exact absurd rfl hne
        | cons _ _ => simpa using hft
      show c.rip = _
      rw [exec_rip9 hf he, hrip', ripadd]

/-! ## The weakest precondition of a block -/

theorem wp_iff : ∀ (sts : List Stmt) (env : Env) (P : Env → Prop),
    Wp sts env P ↔ ∃ env', Silmaril.X86.Bir9.runStmts sts env = .ok env' ∧ P env'
  | [], env, P => by simp [Wp, Silmaril.X86.Bir9.runStmts]
  | st :: rest, env, P => by
    simp only [Wp, Silmaril.X86.Bir9.runStmts]
    split
    · rename_i e he; rw [he]; exact wp_iff rest e P
    · rename_i f hf; rw [hf]; simp

/-- **The checker lemma.** A checked block certificate at the current `rip`, the code loaded and
not writable, every byte of the block in the image: the weakest precondition of the block's
statements, with the goal at the state the block describes, gives the goal. -/
theorem must_blk {W : World} {Q : PState → Prop} {s : PState} {base : Word} {code : List Byte}
    (B : Blk) (hok : B.ok code = true) (hd : s.g.done = none)
    (hin : ∀ o', B.off ≤ o' → o' < B.off + B.len → W.InImage (base + BitVec.ofNat 64 o').toNat)
    (hl : Loaded s.m.memory base code) (hro : CodeRO s.m.memory base code)
    (hrip : s.m.core.rip = base + BitVec.ofNat 64 B.off)
    (h : Wp B.b.stmts (env0 s.m) fun env => MustQ W Q (post B.b s env)) : MustQ W Q s := by
  simp only [Blk.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hseq, hlift⟩ := hok
  refine must_seq B.L B.off s (fun _ => 0) hseq hd hin hl hro (fun _ => hrip) ?_
  rw [Silmaril.X86.Bir9.liftBlock_sound hlift]
  obtain ⟨env, he, hP⟩ := (wp_iff _ _ _).1 h
  unfold Block.run
  simp only [env0] at he
  rw [he]
  exact hP

theorem seqAt_fit {code : List Byte} : ∀ (L : List (LInstr × Nat)) (o : Nat),
    seqAt code o L = true → o + lenL L ≤ code.length ∨ L = []
  | [], _, _ => Or.inr rfl
  | (i, l) :: rest, o, h => by
    simp only [seqAt] at h
    split at h
    · cases h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨_, _⟩, hfit⟩, _⟩, _⟩, hrest⟩ := h
      left
      rcases seqAt_fit rest (o + l) hrest with h' | rfl
      · simp only [lenL]; omega
      · simp only [lenL]; omega

/-- **`must_blk` for a chunk in the image**: the chunk is at `b + cb` and every byte of it is in the
image (one fact per chunk instead of one per block). -/
theorem must_blk_at {W : World} {Q : PState → Prop} {s : PState} {b : Word} {cb : Nat}
    {code : List Byte} (B : Blk) (hok : B.ok code = true) (hd : s.g.done = none)
    (himg : ∀ n, n < code.length → W.InImage (b + BitVec.ofNat 64 (cb + n)).toNat)
    (hl : Loaded s.m.memory (b + BitVec.ofNat 64 cb) code)
    (hro : CodeRO s.m.memory (b + BitVec.ofNat 64 cb) code)
    (hrip : s.m.core.rip = b + BitVec.ofNat 64 (cb + B.off))
    (h : Wp B.b.stmts (env0 s.m) fun env => MustQ W Q (post B.b s env)) : MustQ W Q s := by
  have hfit : B.off + B.len ≤ code.length ∨ B.L = [] := by
    simp only [Blk.ok, Bool.and_eq_true] at hok; exact seqAt_fit _ _ hok.1
  refine must_blk B hok hd (fun o' h1 h2 => ?_) hl hro (by rw [hrip, ripadd]) h
  rw [ripadd]
  rcases hfit with hf | hn
  · exact himg o' (by omega)
  · simp [Blk.len, hn, lenL] at h2; omega

/-- `must_blk` with the goal generalised: the block's outcome satisfies `P`, and every state
satisfying `P` meets the goal (`Proc.must_gen` style). -/
theorem must_blk_gen {W : World} {Q : PState → Prop} {s : PState} {base : Word} {code : List Byte}
    (B : Blk) (hok : B.ok code = true) (hd : s.g.done = none)
    (hin : ∀ o', B.off ≤ o' → o' < B.off + B.len → W.InImage (base + BitVec.ofNat 64 o').toNat)
    (hl : Loaded s.m.memory base code) (hro : CodeRO s.m.memory base code)
    (hrip : s.m.core.rip = base + BitVec.ofNat 64 B.off) (P : PState → Prop)
    (h : Wp B.b.stmts (env0 s.m) fun env => P (post B.b s env))
    (k : ∀ u, P u → MustQ W Q u) : MustQ W Q s :=
  must_blk B hok hd hin hl hro hrip ((wp_iff _ _ _).2 (by
    obtain ⟨env, he, hP⟩ := (wp_iff _ _ _).1 h
    exact ⟨env, he, k _ hP⟩))


/-! ## Certificates over the extended lifter -/

open Silmaril.X86.Bir9X (XL toX9X liftBlockX execBlockX)

theorem xl_exec {i : XL} {j : Silmaril.X86.Ext9.Instr} (hj : toX9X i = some j)
    (x : Xmm) (c : State) (m : Memory) (l : Nat) :
    i.exec ⟨c, x⟩ m l = liftR x (Silmaril.X86.Ext9.exec j c m l) := by
  cases i with
  | base i => exact linstr_exec hj x c m l
  | e8 i => simp only [toX9X, Option.some.injEq] at hj; subst hj; rfl

set_option maxHeartbeats 400000 in
/-- **A checked `Bir9X` listing runs on the process machine.** -/
theorem must_seqX {W : World} {Q : PState → Prop} {base : Word} {code : List Byte} :
    ∀ (L : List (XL × Nat)) (o : Nat) (s : PState) (x : Xmm),
    seqAtX code o L = true → s.g.done = none →
    (∀ o', o ≤ o' → o' < o + lenLX L → W.InImage (base + BitVec.ofNat 64 o').toNat) →
    Loaded s.m.memory base code → CodeRO s.m.memory base code →
    (L ≠ [] → s.m.core.rip = base + BitVec.ofNat 64 o) →
    XPost W Q s.g (execBlockX L ⟨s.m.core, x⟩ s.m.memory) → MustQ W Q s
  | [], _, s, x, _, _, _, _, _, _, h => by
    simp only [execBlockX, XPost] at h; exact h
  | (i, l) :: rest, o, s, x, hok, hd, hin, hl, hro, hrip, h => by
    simp only [seqAtX] at hok
    split at hok
    · cases hok
    · rename_i j hj
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨⟨⟨hdec, hl0⟩, hfit⟩, hft⟩, hlift⟩, hrest⟩ := hok
      have hrip' := hrip (List.cons_ne_nil _ _)
      have hx := xl_exec hj x s.m.core s.m.memory l
      obtain ⟨c, m', he⟩ : ∃ c m', Silmaril.X86.Ext9.exec j s.m.core s.m.memory l = .ok c m' := by
        revert h
        simp only [execBlockX, hx]
        cases Silmaril.X86.Ext9.exec j s.m.core s.m.memory l <;> simp [liftR, XPost]
      have hx' : i.exec ⟨s.m.core, x⟩ s.m.memory l = .ok ⟨c, x⟩ m' := by rw [hx, he]; rfl
      have hb : execBlockX ((i, l) :: rest) ⟨s.m.core, x⟩ s.m.memory = execBlockX rest ⟨c, x⟩ m' := by
        simp only [execBlockX, hx']
      rw [hb] at h
      obtain ⟨bi, hbi⟩ := Option.isSome_iff_exists.mp hlift
      have hfr : Frame s.m.memory m' := by
        have h1 := Silmaril.X86.Bir9X.liftBlockX_sound hbi ⟨s.m.core, x⟩ s.m.memory
        have h2 : execBlockX [(i, l)] ⟨s.m.core, x⟩ s.m.memory = .ok ⟨c, x⟩ m' := by
          simp only [execBlockX, hx']
        rw [h2] at h1
        exact block_frame h1.symm
      refine must_insn hd (by rw [hrip']; exact hin o (Nat.le_refl _) (by simp only [lenLX]; omega)) hl hrip'
        hfit hdec ?_
      rw [he, WP_ok]
      refine must_seqX rest (o + l) ⟨⟨c, m'⟩, s.g⟩ x hrest hd
        (fun o' h1 h2 => hin o' (by omega) (by simp only [lenLX]; omega))
        (loaded_frame hl hro hfr) (codeRO_frame hro hfr) (fun hne => ?_) h
      have hf : Silmaril.X86.BlockCert9.fallsThrough9 j = true := by
        cases rest with
        | nil => exact absurd rfl hne
        | cons _ _ => simpa using hft
      show c.rip = _
      rw [exec_rip9 hf he, hrip', ripadd]

/-- **The checker lemma for `BlkX`.** -/
theorem must_blkX {W : World} {Q : PState → Prop} {s : PState} {base : Word} {code : List Byte}
    (B : BlkX) (hok : B.ok code = true) (hd : s.g.done = none)
    (hin : ∀ o', B.off ≤ o' → o' < B.off + B.len → W.InImage (base + BitVec.ofNat 64 o').toNat)
    (hl : Loaded s.m.memory base code) (hro : CodeRO s.m.memory base code)
    (hrip : s.m.core.rip = base + BitVec.ofNat 64 B.off)
    (h : Wp B.b.stmts (env0 s.m) fun env => MustQ W Q (post B.b s env)) : MustQ W Q s := by
  simp only [BlkX.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hseq, hlift⟩ := hok
  refine must_seqX B.L B.off s (fun _ => 0) hseq hd hin hl hro (fun _ => hrip) ?_
  rw [Silmaril.X86.Bir9X.liftBlockX_sound hlift]
  obtain ⟨env, he, hP⟩ := (wp_iff _ _ _).1 h
  unfold Block.run
  simp only [env0] at he
  rw [he]
  exact hP

theorem seqAtX_fit {code : List Byte} : ∀ (L : List (XL × Nat)) (o : Nat),
    seqAtX code o L = true → o + lenLX L ≤ code.length ∨ L = []
  | [], _, _ => Or.inr rfl
  | (i, l) :: rest, o, h => by
    simp only [seqAtX] at h
    split at h
    · cases h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨_, _⟩, hfit⟩, _⟩, _⟩, hrest⟩ := h
      left
      rcases seqAtX_fit rest (o + l) hrest with h' | rfl
      · simp only [lenLX]; omega
      · simp only [lenLX]; omega

/-- **`must_blkX` for a chunk in the image** (as `must_blk_at`). -/
theorem must_blkX_at {W : World} {Q : PState → Prop} {s : PState} {b : Word} {cb : Nat}
    {code : List Byte} (B : BlkX) (hok : B.ok code = true) (hd : s.g.done = none)
    (himg : ∀ n, n < code.length → W.InImage (b + BitVec.ofNat 64 (cb + n)).toNat)
    (hl : Loaded s.m.memory (b + BitVec.ofNat 64 cb) code)
    (hro : CodeRO s.m.memory (b + BitVec.ofNat 64 cb) code)
    (hrip : s.m.core.rip = b + BitVec.ofNat 64 (cb + B.off))
    (h : Wp B.b.stmts (env0 s.m) fun env => MustQ W Q (post B.b s env)) : MustQ W Q s := by
  have hfit : B.off + B.len ≤ code.length ∨ B.L = [] := by
    simp only [BlkX.ok, Bool.and_eq_true] at hok; exact seqAtX_fit _ _ hok.1
  refine must_blkX B hok hd (fun o' h1 h2 => ?_) hl hro (by rw [hrip, ripadd]) h
  rw [ripadd]
  rcases hfit with hf | hn
  · exact himg o' (by omega)
  · simp [BlkX.len, hn, lenLX] at h2; omega

/-! ## Statement rules -/

theorem wp_nil {env : Env} {P : Env → Prop} (h : P env) : Wp [] env P := by simp only [Wp]; exact h

theorem wp_load {k : Nat} {a : E} {rest : List Stmt} {env : Env} {P : Env → Prop}
    (hr : ∃ v, loadN env.mem (a.den env) k = some v)
    (h : ∀ v, loadN env.mem (a.den env) k = some v → Wp rest (env.push v) P) :
    Wp (.load k a :: rest) env P := by
  obtain ⟨v, hv⟩ := hr
  simp only [Wp, Stmt.run, hv]
  exact h v hv

theorem wp_store {k : Nat} {a x : E} {rest : List Stmt} {env : Env} {P : Env → Prop}
    (hp : env.mem.Permitted .write (a.den env).toNat k)
    (h : Wp rest { env with mem := storeMem env.mem (a.den env) k (x.den env) } P) :
    Wp (.store k a x :: rest) env P := by
  simp only [Wp, Stmt.run, storeN_ok hp]
  exact h

theorem wp_push {a x : E} {rest : List Stmt} {env : Env} {P : Env → Prop}
    (hp : env.mem.Permitted .write (a.den env).toNat 8)
    (h : Wp rest { env with mem := storeMem env.mem (a.den env) 8 (x.den env) } P) :
    Wp (.push a x :: rest) env P := by
  have hw : env.mem.writeBytes (a.den env).toNat
      (Silmaril.Machine.LittleEndian.encodeWords [x.den env]) =
      some (storeMem env.mem (a.den env) 8 (x.den env)) := by
    rw [← Silmaril.X86.Ext.leBytes_eight]; exact storeN_ok hp
  simp only [Wp, Stmt.run, hw]
  exact h

theorem wp_pop {a : E} {rest : List Stmt} {env : Env} {P : Env → Prop}
    (hr : ∃ v, (env.mem.readBytes (a.den env).toNat 8).bind Silmaril.X86.wordOfBytes? = some v)
    (h : ∀ v, (env.mem.readBytes (a.den env).toNat 8).bind Silmaril.X86.wordOfBytes? = some v →
      Wp rest (env.push v) P) :
    Wp (.pop a :: rest) env P := by
  obtain ⟨v, hv⟩ := hr
  simp only [Wp, Stmt.run, hv]
  exact h v hv

theorem wp_cond {c : Silmaril.X86.Ext.Cond} {f : F} {rest : List Stmt} {env : Env} {P : Env → Prop}
    (hs : ∃ bv, c.eval (f.den env) = some bv)
    (h : ∀ bv, c.eval (f.den env) = some bv → Wp rest (env.push (if bv then 1#64 else 0#64)) P) :
    Wp (.cond c f :: rest) env P := by
  obtain ⟨bv, hv⟩ := hs
  simp only [Wp, Stmt.run, hv]
  exact h bv hv

theorem wp_align {a : E} {k : Nat} {rest : List Stmt} {env : Env} {P : Env → Prop}
    (ha : (a.den env).toNat % k = 0) (h : Wp rest env P) : Wp (.align a k :: rest) env P := by
  simp only [Wp, Stmt.run, ha, ↓reduceIte]
  exact h

theorem wp_chk {o : Silmaril.X86.Bir9.COp} {a b c : E} {rest : List Stmt} {env : Env}
    {P : Env → Prop} (hc : o.fault (a.den env) (b.den env) (c.den env) = none) (h : Wp rest env P) :
    Wp (.chk o a b c :: rest) env P := by
  simp only [Wp, Stmt.run, hc]
  exact h

/-! ## Conditions on defined flags -/

/-- Every flag a condition can read is defined. -/
def Defined (f : Silmaril.X86.Flags) : Prop :=
  f.carry.isSome ∧ f.parity.isSome ∧ f.zero.isSome ∧ f.sign.isSome ∧ f.overflow.isSome

theorem eval_some {f : Silmaril.X86.Flags} (h : Defined f) (c : Silmaril.X86.Ext.Cond) :
    ∃ bv, c.eval f = some bv := by
  obtain ⟨fc, fp, fa, fz, fs, fo⟩ := f
  obtain ⟨hc, hp, hz, hs, ho⟩ := h
  obtain ⟨c1, rfl⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨c2, rfl⟩ := Option.isSome_iff_exists.mp hp
  obtain ⟨c3, rfl⟩ := Option.isSome_iff_exists.mp hz
  obtain ⟨c4, rfl⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨c5, rfl⟩ := Option.isSome_iff_exists.mp ho
  cases c <;> cases c1 <;> cases c3 <;> cases c4 <;> cases c5 <;>
    simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot, Silmaril.X86.Ext.kOr, Silmaril.X86.Ext.kXor]

theorem defined_alu (w : Nat) (op : Silmaril.X86.AluOp) (x y : BitVec w) :
    Defined (Silmaril.X86.Ext.AluOp.flagsN op x y) := by
  cases op <;> simp [Defined, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.addFlagsN,
    Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.logicFlagsN]

theorem defined_logic {w : Nat} (x : BitVec w) : Defined (Silmaril.X86.Ext.logicFlagsN x) := by
  simp [Defined, Silmaril.X86.Ext.logicFlagsN]

/-! ## Registers a block does not change -/

theorem lookupE_of_not_mem {r : Reg} : ∀ {regs : List (Reg × E)},
    r ∉ regs.map Prod.fst → Silmaril.X86.Bir9.lookupE r regs = .reg r
  | [], _ => rfl
  | (a, e) :: rest, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [Silmaril.X86.Bir9.lookupE, h.1, ↓reduceIte]
    exact lookupE_of_not_mem h.2

/-- **A register the block does not list is unchanged** (`hr` closes by `simp [blk, h₁, …]`
from the hypotheses `r ≠ rᵢ`). -/
theorem state_read_other {b : Block} {env : Env} {r : Reg}
    (hr : r ∉ b.regs.map Prod.fst) : (b.state env).core.read r = env.s0.read r := by
  simp only [Silmaril.X86.Bir9.state_read, lookupE_of_not_mem hr, E.den]

theorem post_read_other {b : Block} {s : PState} {env : Env} {r : Reg}
    (hr : r ∉ b.regs.map Prod.fst) : (post b s env).m.core.read r = env.s0.read r :=
  state_read_other hr

/-! ## Memory after a block's stores -/

@[simp] theorem storeMem_regions (m : Memory) (a : Word) (k : Nat) (v : Word) :
    (storeMem m a k v).regions = m.regions := rfl

@[simp] theorem storeMem_permits (m : Memory) (a : Word) (k : Nat) (v : Word) (acc : Access) (x : Nat) :
    (storeMem m a k v).permits acc x = m.permits acc x := rfl

/-- A store outside `P` keeps what `P` covers (for chains of stores: apply repeatedly). -/
theorem keeps_storeMem_right {P : Nat → Prop} {m m' : Memory} {a : Word} {k : Nat} {v : Word}
    (hd : ∀ x, P x → x < a.toNat ∨ a.toNat + k ≤ x) (h : Keeps P m m') :
    Keeps P m (storeMem m' a k v) :=
  h.trans (storeMem_keeps hd)

/-- `jae`/`jb` after `cmp x, y`: unsigned comparisons. -/
theorem eval_ae_sub {w : Nat} (x y : BitVec (w + 1)) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN x y) .ae = some (!(x.ult y)) := by
  simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.kNot,
    Silmaril.X86.Ext.subBorrowN_eq]

theorem eval_b_sub {w : Nat} (x y : BitVec (w + 1)) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN x y) .b = some (x.ult y) := by
  simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.subBorrowN_eq]

/-! ## Tactics -/

/-- Evaluate block terms (`E.den`, `F.den`, the environment's values, the final state). -/
syntax "blk_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| blk_simp $[$loc]?) => `(tactic|
      simp only [E.den, F.den, Env.push, env0, post, List.getD_cons_zero,
        List.getD_cons_succ, List.nil_append, List.cons_append,
        Silmaril.X86.Bir9.state_read, Silmaril.X86.Bir9.state_rip, Silmaril.X86.Bir9.state_flags,
        Silmaril.X86.Bir9.lookupE, reduceCtorEq, ite_true, ite_false, ripadd,
        Silmaril.X86.Ext.AluOp.resultN, storeMem_permitted, storeMem_regions, storeMem_permits] $[$loc]?)
  | `(tactic| blk_simp [$ls,*] $[$loc]?) => `(tactic|
      simp only [$ls,*, E.den, F.den, Env.push, env0, post, List.getD_cons_zero,
        List.getD_cons_succ, List.nil_append, List.cons_append,
        Silmaril.X86.Bir9.state_read, Silmaril.X86.Bir9.state_rip, Silmaril.X86.Bir9.state_flags,
        Silmaril.X86.Bir9.lookupE, reduceCtorEq, ite_true, ite_false, ripadd,
        Silmaril.X86.Ext.AluOp.resultN, storeMem_permitted, storeMem_regions, storeMem_permits] $[$loc]?)

/-- Apply the statement rules of a block's `Wp`, left to right. The side conditions (store and
push permissions, load and pop results, condition outcomes) are left as goals after the final
goal; loaded values and condition outcomes are introduced as variables with their equations. -/
syntax "blk_wp" : tactic

macro_rules
  | `(tactic| blk_wp) => `(tactic| first
    | (refine wp_store ?_ ?_; pick_goal 2; blk_wp)
    | (refine wp_push ?_ ?_; pick_goal 2; blk_wp)
    | (refine wp_load ?_ ?_; pick_goal 2; intro _ hv; (try blk_simp at hv); blk_wp)
    | (refine wp_pop ?_ ?_; pick_goal 2; intro _ hv; (try blk_simp at hv); blk_wp)
    | (refine wp_cond ?_ ?_; pick_goal 2; intro _ hv; (try blk_simp at hv); blk_wp)
    | (refine wp_align ?_ ?_; pick_goal 2; blk_wp)
    | (refine wp_chk ?_ ?_; pick_goal 2; blk_wp)
    | refine wp_nil ?_)

end Silmaril.Elf.Link.Dyn.Cert
