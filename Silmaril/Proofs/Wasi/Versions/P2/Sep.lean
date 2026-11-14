module

public import Silmaril.Wasi.Versions.P2.Sep.Defs
public import Silmaril.Wasi.Versions.P2.World.Thms
public import Silmaril.Wasi.Comp.Thms

/-!
# Proofs: `trusting` is correct under the strict reading

The invariant method (`Silmaril.Wasi.Comp.ag_of_inv`) with the invariant `TS`: the reachable control
states of `trusting`, with the facts the strict theory provides at each of them:

* waiting on `block(p)` for the stream `s`: the theory knows `p` is a pollable of `s`;
* about to call `check-write(s)`: the theory has seen a pollable of `s` ready;
* about to `write` one byte to `s`: the guest's permit for `s` is at least `1`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P2

open Silmaril.Games
open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- The imports of `p2Command`. -/
abbrev PI : Set FnName := p2Command.imports
/-- The exports of `p2Command`. -/
abbrev PX : Set FnName := p2Command.exports

/-- **The invariant of `trusting`.** -/
inductive TS : CSt PI PX → P2St → (BitVec 32 → Nat) → Prop
  | idle {qT qG} : TS .idle qT qG
  | start {qT qG} (q) : TS (.run q (.call getOp2 tGot)) qT qG
  | getW {qT qG} (q) : TS (.wait q getOp2 tGot) qT qG
  | sub {qT qG} (q s) : TS (.run q (.call (subOp s) (tSub s))) qT qG
  | subW {qT qG} (q s) : TS (.wait q (subOp s) (tSub s)) qT qG
  | blk {qT : P2St} {qG} (q s p) (h : qT.1.parent p = some s) :
      TS (.run q (.call (blkOp p) (tBlk s))) qT qG
  | blkW {qT : P2St} {qG} (q s p) (h : qT.1.parent p = some s) :
      TS (.wait q (blkOp p) (tBlk s)) qT qG
  | cw {qT : P2St} {qG} (q s) (h : qT.1.ready s = true) : TS (.run q (.call (cwOp s) (tCw s))) qT qG
  | cwW {qT : P2St} {qG} (q s) (h : qT.1.ready s = true) : TS (.wait q (cwOp s) (tCw s)) qT qG
  | wr {qT} {qG : BitVec 32 → Nat} (q s) (h : 1 ≤ qG s) : TS (.run q (.call (wr1Op s) tDone)) qT qG
  | wrW {qT qG} (q s) : TS (.wait q (wr1Op s) tDone) qT qG
  | fin {qT qG} (q r) : TS (.run q (.pure r)) qT qG

/-! ## Theory and guarantee steps -/

/-- A non-answer leaves the theory state. -/
theorem p2_run_nonimp {r : Reading} {q q' : P2St} {e : WEv} (he : e.isImp = false)
    (h : (p2Th r).run q (hostView [e]) = some q') : q' = q := by
  rw [hostView_single_of_not_imp he] at h
  exact (Option.some.inj h).symm

/-- An answer: admissible, and the `wasi:io` state is updated. -/
theorem p2_run_imp {r : Reading} {q q' : P2St} {f : FnName} {a : List Val}
    {n : Option (List Val)} (h : (p2Th r).run q (hostView [.imp f a n]) = some q') :
    ansOk r q.1 (ioOp f) a n = true ∧ q'.1 = ioUpd q.1 (ioOp f) a n := by
  have hv : hostView [WEv.imp f a n] = [.imp f a n] := rfl
  have hp : ((ioTh r).prod (clockTh.prod ((pointwise p2Ok).prod fsTyped))).run (q.1, q.2)
      [.imp f a n] = some q' := hv ▸ h
  rw [Protocol.run_prod] at hp
  obtain ⟨i, hi, hm⟩ := Option.bind_eq_some_iff.1 hp
  obtain ⟨b, -, hb⟩ := Option.map_eq_some_iff.1 hm
  have hstep : ioStep r q.1 (.imp f a n) = some i := by
    simpa [Protocol.run_cons, ioTh] using hi
  by_cases hok : ansOk r q.1 (ioOp f) a n = true
  · have hi' : ioUpd q.1 (ioOp f) a n = i := by simpa [ioStep, hok] using hstep
    exact ⟨hok, by rw [← hb, ← hi']⟩
  · exact absurd hstep (by simp [ioStep, hok])

/-- The guarantee ignores answers other than `check-write`. -/
theorem permit_imp {f : FnName} {a : List Val} {n : Option (List Val)} (qG : BitVec 32 → Nat)
    (hf : ioOp f ≠ .checkWrite) : permitG.step qG (.imp f a n) = some qG := by
  simp [permitG, permitStep, hf]

/-- The guarantee ignores requests other than writes. -/
theorem permit_req {f : FnName} {a : List Val} (qG : BitVec 32 → Nat) (h1 : ioOp f ≠ .write)
    (h2 : ioOp f ≠ .writeZeroes) : permitG.step qG (.req f a) = some qG := by
  simp [permitG, permitStep, h1, h2]

/-- The classes of the functions `trusting` calls. -/
theorem ioOp_getStdout : ioOp getStdout = .other := by decide
theorem ioOp_sub : ioOp osSubscribe = .oSubscribe := by decide
theorem ioOp_block : ioOp pollBlock = .block := by decide
theorem ioOp_cw : ioOp osCheckWrite = .checkWrite := by decide
theorem ioOp_write : ioOp osWrite = .write := by decide

/-! ## The continuations -/

theorem tGot_cases (n : Option (List Val)) :
    (∃ s, tGot n = .call (subOp s) (tSub s)) ∨ ∃ r, tGot n = .pure r := by
  unfold tGot
  split
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, rfl⟩

theorem tSub_cases (s : BitVec 32) (n : Option (List Val)) :
    (tSub s n = .call (blkOp (handleOf n)) (tBlk s)) ∨ ∃ r, tSub s n = .pure r := by
  unfold tSub
  split
  · exact .inl rfl
  · exact .inr ⟨_, rfl⟩

theorem tCw_cases (s : BitVec 32) (n : Option (List Val)) :
    (∃ x, n = some [.variant 0 x] ∧ tCw s n = .call (wr1Op s) tDone) ∨ ∃ r, tCw s n = .pure r := by
  unfold tCw
  split
  · exact .inl ⟨_, rfl, rfl⟩
  · exact .inr ⟨_, rfl⟩

/-! ## The `wasi:io` facts -/

/-- `subscribe` records the pollable's stream. -/
theorem parent_subscribe (s : IoSt) (a : List Val) (n : Option (List Val)) :
    (ioUpd s .oSubscribe a n).parent (handleOf n) = some (selfOf a) := by
  simp [ioUpd, closeOn, IoOp.isStream, upd]

/-- A returned `block` marks the pollable's stream ready. -/
theorem ready_block {s : IoSt} {p h : BitVec 32} (hp : s.parent p = some h) :
    (ioUpd s .block [.u32 p] (some [])).ready h = true := by
  simp [ioUpd, closeOn, IoOp.isStream, markReady, hp, upd, selfOf]

/-- The admissible answer of `block`. -/
theorem block_ans {r : Reading} {s : IoSt} {a : List Val} {n : Option (List Val)}
    (h : ansOk r s .block a n = true) : n = some [] := by
  simp only [ansOk, blockAns_eq_hand, blockAnsH] at h
  split at h
  · rfl
  · cases h

/-- **The strict reading**: an `ok(_)` answer of `check-write` on a ready stream is a permit of at
least `1`. -/
theorem okNat_pos {s : IoSt} {h : BitVec 32} {x : Option Val}
    (hok : ansOk .strict s .checkWrite [.u32 h] (some [.variant 0 x]) = true)
    (hr : s.ready h = true) : 1 ≤ okNat (some [.variant 0 x]) := by
  have hok' : (stickyOk s h (some [.variant 0 x]) && natAns (2 ^ 64) (some [.variant 0 x])) &&
      (Reading.strict == .loose || !s.ready h || !isOkZero (some [.variant 0 x])) = true := hok
  simp only [Bool.and_eq_true] at hok'
  have hn : natAns (2 ^ 64) (some [.variant 0 x]) = true := hok'.1.2
  have hz : isOkZero (some [.variant 0 x]) = false := by simpa [hr] using hok'.2
  rcases x with _ | v
  · simp [natAns] at hn
  cases v
  case u64 m =>
    have hm : m ≠ 0 := by simpa [isOkZero] using hz
    have hm' : m.toNat ≠ 0 := fun h0 => hm (BitVec.eq_of_toNat_eq (by simp [h0]))
    show 1 ≤ m.toNat
    omega
  all_goals simp [natAns] at hn

/-! ## The steps of the invariant -/

/-- What `Inv.step` asks of a move. -/
abbrev Post (c' : CSt PI PX) (qT' : P2St) (qG : BitVec 32 → Nat) (o : Move (nsig PI) (nsig PX)) :
    Prop :=
  ∃ qG', permitG.step qG (wev o) = some qG' ∧ TS c' qT' qG'

variable {c' : CSt PI PX} {o : Move (nsig PI) (nsig PX)} {qT qT' : P2St} {qG : BitVec 32 → Nat}
  {q : (nsig PX).Op}

theorem step_idle (hc : CStep trusting .idle o c') : Post c' qT' qG o := by
  obtain ⟨q, rfl, rfl⟩ := hc.idle_inv
  exact ⟨qG, rfl, TS.start q⟩

theorem step_start (hc : CStep trusting (.run q (.call getOp2 tGot)) o c')
    (hT : (p2Th .strict).run qT (hostView [wev o]) = some qT') : Post c' qT' qG o := by
  obtain ⟨rfl, rfl⟩ := hc.call_inv
  exact ⟨qG, permit_req qG (by decide) (by decide),
    TS.getW q⟩

theorem step_getW (hc : CStep trusting (.wait q getOp2 tGot) o c') : Post c' qT' qG o := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  refine ⟨qG, permit_imp qG (by decide), ?_⟩
  rcases tGot_cases n with ⟨s, hs⟩ | ⟨r, hr⟩
  · exact hs ▸ TS.sub q s
  · exact hr ▸ TS.fin q r

theorem step_sub {s : BitVec 32} (hc : CStep trusting (.run q (.call (subOp s) (tSub s))) o c') :
    Post c' qT' qG o := by
  obtain ⟨rfl, rfl⟩ := hc.call_inv
  exact ⟨qG, permit_req (f := osSubscribe) (a := [.u32 s]) qG (by decide) (by decide), TS.subW q s⟩

theorem step_subW {s : BitVec 32} (hc : CStep trusting (.wait q (subOp s) (tSub s)) o c')
    (hT : (p2Th .strict).run qT (hostView [wev o]) = some qT') : Post c' qT' qG o := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  have hu : qT'.1 = ioUpd qT.1 .oSubscribe [.u32 s] n := ioOp_sub ▸ (p2_run_imp (f := osSubscribe) (a := [.u32 s]) hT).2
  have hp : qT'.1.parent (handleOf n) = some s := hu ▸ parent_subscribe qT.1 [.u32 s] n
  refine ⟨qG, permit_imp (f := osSubscribe) (a := [.u32 s]) qG (by decide), ?_⟩
  rcases tSub_cases s n with hs | ⟨r, hr⟩
  · exact hs ▸ TS.blk q s (handleOf n) hp
  · exact hr ▸ TS.fin q r

theorem step_blk {s p : BitVec 32} (h : qT.1.parent p = some s)
    (hc : CStep trusting (.run q (.call (blkOp p) (tBlk s))) o c')
    (hT : (p2Th .strict).run qT (hostView [wev o]) = some qT') : Post c' qT' qG o := by
  obtain ⟨rfl, rfl⟩ := hc.call_inv
  have hq : qT' = qT := p2_run_nonimp rfl hT
  exact ⟨qG, permit_req (f := pollBlock) (a := [.u32 p]) qG (by decide) (by decide),
    TS.blkW q s p (hq ▸ h)⟩

theorem step_blkW {s p : BitVec 32} (h : qT.1.parent p = some s)
    (hc : CStep trusting (.wait q (blkOp p) (tBlk s)) o c')
    (hT : (p2Th .strict).run qT (hostView [wev o]) = some qT') : Post c' qT' qG o := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  have hi : ansOk .strict qT.1 .block [.u32 p] n = true ∧
      qT'.1 = ioUpd qT.1 .block [.u32 p] n := ioOp_block ▸ p2_run_imp (f := pollBlock) (a := [.u32 p]) hT
  have hn : n = some [] := block_ans hi.1
  have hr : qT'.1.ready s = true := by rw [hi.2, hn]; exact ready_block h
  exact ⟨qG, permit_imp (f := pollBlock) (a := [.u32 p]) qG (by decide), TS.cw q s hr⟩

theorem step_cw {s : BitVec 32} (h : qT.1.ready s = true)
    (hc : CStep trusting (.run q (.call (cwOp s) (tCw s))) o c')
    (hT : (p2Th .strict).run qT (hostView [wev o]) = some qT') : Post c' qT' qG o := by
  obtain ⟨rfl, rfl⟩ := hc.call_inv
  have hq : qT' = qT := p2_run_nonimp rfl hT
  exact ⟨qG, permit_req (f := osCheckWrite) (a := [.u32 s]) qG (by decide) (by decide),
    TS.cwW q s (hq ▸ h)⟩

/-- The guarantee's step on a `check-write` answer. -/
theorem permit_cw (qG : BitVec 32 → Nat) (s : BitVec 32) (n : Option (List Val)) :
    permitG.step qG (.imp osCheckWrite [.u32 s] n) = some (upd qG s (okNat n)) := by
  simp [permitG, permitStep, ioOp_cw, selfOf]

theorem step_cwW {s : BitVec 32} (h : qT.1.ready s = true)
    (hc : CStep trusting (.wait q (cwOp s) (tCw s)) o c')
    (hT : (p2Th .strict).run qT (hostView [wev o]) = some qT') : Post c' qT' qG o := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  have hok : ansOk .strict qT.1 .checkWrite [.u32 s] n = true := ioOp_cw ▸ (p2_run_imp (f := osCheckWrite) (a := [.u32 s]) hT).1
  refine ⟨upd qG s (okNat n), permit_cw qG s n, ?_⟩
  rcases tCw_cases s n with ⟨x, rfl, hx⟩ | ⟨r, hr⟩
  · have hpos : 1 ≤ upd qG s (okNat (some [.variant 0 x])) s := by
      simpa [upd] using okNat_pos hok h
    exact hx ▸ TS.wr q s hpos
  · exact hr ▸ TS.fin q r

/-- The guarantee's step on the one-byte write. -/
theorem permit_wr {qG : BitVec 32 → Nat} {s : BitVec 32} (h : 1 ≤ qG s) :
    permitG.step qG (.req osWrite [.u32 s, bytesV [0x68]]) = some (upd qG s (qG s - 1)) := by
  simp [permitG, permitStep, ioOp_write, writeLen, contentsOf, bytesOf, bytesV, selfOf, h]

theorem step_wr {s : BitVec 32} (h : 1 ≤ qG s)
    (hc : CStep trusting (.run q (.call (wr1Op s) tDone)) o c') : Post c' qT' qG o := by
  obtain ⟨rfl, rfl⟩ := hc.call_inv
  exact ⟨_, permit_wr h, TS.wrW q s⟩

theorem step_wrW {s : BitVec 32} (hc : CStep trusting (.wait q (wr1Op s) tDone) o c') :
    Post c' qT' qG o := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  exact ⟨qG, permit_imp (f := osWrite) (a := [.u32 s, bytesV [0x68]]) qG (by decide), TS.fin q _⟩

theorem step_fin {r : Option (List Val)} (hc : CStep trusting (.run q (.pure r)) o c') :
    Post c' qT' qG o := by
  obtain ⟨rfl, rfl⟩ := hc.pure_inv
  exact ⟨qG, rfl, TS.idle⟩

/-- **The invariant of `trusting` under the strict theory.** -/
theorem trusting_inv : Inv trusting (p2Th .strict) permitG TS where
  init := TS.idle
  step := fun hc hJ hT => by
    cases hJ with
    | idle => exact step_idle hc
    | start q => exact step_start hc hT
    | getW q => exact step_getW hc
    | sub q s => exact step_sub hc
    | subW q s => exact step_subW hc hT
    | blk q s p h => exact step_blk h hc hT
    | blkW q s p h => exact step_blkW h hc hT
    | cw q s h => exact step_cw h hc hT
    | cwW q s h => exact step_cwW h hc hT
    | wr q s h => exact step_wr h hc
    | wrW q s => exact step_wrW hc
    | fin q r => exact step_fin hc

end Silmaril.Wasi.Versions.P2
