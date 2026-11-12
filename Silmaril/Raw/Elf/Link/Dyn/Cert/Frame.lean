module

public import Silmaril.Elf.Link.Dyn.Cert.Thms
public import Silmaril.Raw.Elf.Link.Dyn.Proc.Frame

/-! # Block certificates: frames of a block's stores

A block's memory is a chain of `storeMem`s on its entry memory. These lemmas carry the frame
facts of a function body (`Proc.Room`, `Proc.Body`) across such a chain:

* `room_store_caller`, `room_store_img`: a store inside the stack room avoids the caller's data
  and the image;
* `storeMem_read8'`: a word read back at the address of the last store to it;
* `BodyX.stores`: the generic stack-frame lemma (a body survives a block storing into its own frame);
* `loadN_storeMem_ne`: a load that misses a store;
* tactics `keeps_chain` (a `Keeps` across a chain of stores, one disjointness goal per store),
  `blk_step` (one block step: `must_blk_at`, `blk_wp`, `blk_simp`) and `blk_perms` (permissions in
  the stack room).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Cert

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.Elf.Link.Dyn.Proc

/-- A store inside the room avoids the caller's data (kept memory, the stack at and above `sp`). -/
theorem room_store_caller {W : World} {m : Memory} {sp a : Word} {n k : Nat} (hroom : Room W m sp n)
    (hlo : sp.toNat - n ≤ a.toNat) (hhi : a.toNat + k ≤ sp.toNat) :
    ∀ x, (W.Kept x ∨ sp.toNat ≤ x) ∧ ¬ (fun _ => False) x → x < a.toNat ∨ a.toNat + k ≤ x := by
  rintro x ⟨hx | hx, -⟩
  · by_contra hc
    exact (hroom.2.2 x (by omega) (by omega)).2.2 hx
  · omega

/-- A store inside the room avoids the image. -/
theorem room_store_img {W : World} {m : Memory} {sp a : Word} {n k : Nat} (hroom : Room W m sp n)
    (hlo : sp.toNat - n ≤ a.toNat) (hhi : a.toNat + k ≤ sp.toNat + 8) :
    ∀ x, W.InImage x → x < a.toNat ∨ a.toNat + k ≤ x := by
  intro x hx
  by_contra hc
  exact (hroom.2.2 x (by omega) (by omega)).2.2 (Or.inl hx)

theorem storeMem_read8' {m : Memory} {a v : Word} {A : Nat} (hr : m.Permitted .read a.toNat 8)
    (he : a.toNat = A) :
    (storeMem m a 8 v).readBytes A 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v]) := by
  rw [← he]; exact storeMem_read8 hr

/-- **A body across a block whose stores all lie in its own frame** `[lo, hi)` (below the saved
registers): the generic stack-frame lemma behind `blk_step`. `hk` comes from `keeps_chain`. -/
theorem BodyX.stores {W : World} {M : Memory → Prop} (hM : ∀ m m', M m → Keeps W.InImage m m' → M m')
    {s u v : PState} {fr n sv : Nat} {saved : List (Nat × Word)} {X : Nat → Prop}
    (hB : BodyX W M s u fr n saved X) (hfr : fr ≤ n) (hsv : ∀ p ∈ saved, p.1 ≤ sv) {lo hi : Nat}
    (hlo : (s.m.core.read .rsp).toNat - fr ≤ lo) (hhi : hi + sv ≤ (s.m.core.read .rsp).toNat)
    (hk : Keeps (fun x => x < lo ∨ hi ≤ x) u.m.memory v.m.memory)
    (hreg : v.m.memory.regions = u.m.memory.regions) (hr : v.m.core.read .rsp = u.m.core.read .rsp)
    (hf : v.m.core.fsBase = u.m.core.fsBase) (hd : v.g.done = u.g.done) :
    BodyX W M s v fr n saved X := by
  have hroom := hB.room
  have hout : ∀ x, W.Kept x → x < lo ∨ hi ≤ x := by
    intro x hx
    by_contra hc
    exact (hroom.2.2 x (by omega) (by omega)).2.2 hx
  have hperm : ∀ acc x, v.m.memory.permits acc x = u.m.memory.permits acc x := fun acc x => by
    unfold Memory.permits; rw [hreg]
  refine ⟨hr.trans hB.rsp, ?_, ?_, ?_, hf.trans hB.fs, hd.trans hB.done, ?_, ?_⟩
  · exact hB.keepX.trans (hk.mono fun x hx => by
      rcases hx.1 with h | h
      · exact hout x h
      · right; omega)
  · exact hroom.keeps fun _ _ _ acc => hperm acc _
  · exact hM _ _ hB.mem (hk.mono fun x hx => hout x (Or.inl hx))
  · intro p hp
    have h1 := hsv p hp
    rw [(hk.mono (P' := fun x => (s.m.core.read .rsp).toNat - p.1 ≤ x) fun x hx => by omega).readBytes
      (fun j hj => by omega)]
    exact hB.saved p hp
  · intro x h1 h2 acc
    rw [hperm]; exact hB.perm x h1 h2 acc

/-- A load that misses a store reads the memory before it. -/
theorem loadN_storeMem_ne {m : Memory} {a A v : Word} {k n : Nat}
    (h : a.toNat + k ≤ A.toNat ∨ A.toNat + n ≤ a.toNat) :
    Silmaril.X86.Ext.loadN (storeMem m a k v) A n = Silmaril.X86.Ext.loadN m A n := by
  simp only [Silmaril.X86.Ext.loadN]
  rw [storeMem_read_ne (by omega)]

/-- `Keeps P m m'` where `m'` is a chain of stores on `m`: one disjointness goal per store. -/
syntax "keeps_chain" : tactic

macro_rules
  | `(tactic| keeps_chain) => `(tactic|
      (repeat (refine keeps_storeMem_right ?_ ?_; pick_goal 2)
       exact Keeps.refl _ _))

/-- **One block step**: `blk_step B hok hd himg hl hro hrip` applies `must_blk_at` with the block's
certificate (`Blk` or `BlkX`), runs its statements (`blk_wp`) and evaluates the terms (`blk_simp [B]`). The goals
left are the final state's goal, then the side conditions (loads, outcomes, permissions). -/
syntax "blk_step " term:max term:max term:max term:max term:max term:max term:max : tactic

macro_rules
  | `(tactic| blk_step $B $hok $hd $himg $hl $hro $hrip) => `(tactic|
      (first
         | refine Silmaril.Elf.Link.Dyn.Cert.must_blk_at $B $hok $hd $himg $hl $hro $hrip ?_
         | refine Silmaril.Elf.Link.Dyn.Cert.must_blkX_at $B $hok $hd $himg $hl $hro $hrip ?_
       blk_wp
       all_goals blk_simp [$B:term]))

/-- Discharge the read and write permissions of a block's side conditions inside the stack room
`hroom` (after rewriting with the given equations, e.g. `rbp = rsp - 8`). -/
syntax "blk_perms " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| blk_perms $hroom) => `(tactic|
      all_goals try
        (try simp only [Silmaril.Elf.Link.Dyn.Proc.storeMem_permitted]
         first
         | (refine Silmaril.Elf.Link.Dyn.Proc.room_perm $hroom (Or.inr rfl) ?_ ?_ <;> bv_omega)
         | (refine Silmaril.Elf.Link.Dyn.Proc.room_perm $hroom (Or.inl rfl) ?_ ?_ <;> bv_omega)))
  | `(tactic| blk_perms $hroom [$ls,*]) => `(tactic|
      all_goals try
        (try simp only [Silmaril.Elf.Link.Dyn.Proc.storeMem_permitted, $ls,*]
         first
         | (refine Silmaril.Elf.Link.Dyn.Proc.room_perm $hroom (Or.inr rfl) ?_ ?_ <;> bv_omega)
         | (refine Silmaril.Elf.Link.Dyn.Proc.room_perm $hroom (Or.inl rfl) ?_ ?_ <;> bv_omega)))

end Silmaril.Elf.Link.Dyn.Cert
