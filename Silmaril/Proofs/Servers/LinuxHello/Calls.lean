module

public import Silmaril.Servers.LinuxHello.Defs
public import Silmaril.Servers.Sockets.Thms

/-!
# A Linux hello server loop: the system calls it makes succeed as it expects

Helpers for `Silmaril.Servers.LinuxHello.Thms`: network streams of a list, the loop's memory,
and successful outcomes of `accept`, `read`, `sendto` and `close` in LPS's specifications.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.LinuxHello

open Silmaril.Process Silmaril.Process.LPS Silmaril.Servers.LinuxHello

/-! ## A network stream carrying a list, then `FIN` -/

/-- The bytes of `l`, then the end of the stream. -/
def ofListFin (l : List LPS.Byte) : NetStream where
  item i := if h : i < l.length then .inl l[i] else .inr .fin
  stable i j hij h := by
    by_cases hi : i < l.length
    · simp [hi] at h
    · have hj : ¬ j < l.length := by omega
      simp [hi, hj]

theorem NetStream.ext' {s t : NetStream} (h : ∀ i, s.item i = t.item i) : s = t := by
  cases s; cases t
  simp only [NetStream.mk.injEq]
  exact funext h

theorem takeFrom_ofListFin (l : List LPS.Byte) :
    ∀ (k st : Nat), (ofListFin l).takeFrom st k = (l.drop st).take k
  | 0, _ => by simp [NetStream.takeFrom]
  | k + 1, st => by
    unfold NetStream.takeFrom
    by_cases h : st < l.length
    · have hi : (ofListFin l).item st = .inl l[st] := by simp [ofListFin, h]
      simp only [hi]
      rw [takeFrom_ofListFin l k (st + 1)]
      conv_rhs => rw [List.drop_eq_getElem_cons h]
      rfl
    · have hi : (ofListFin l).item st = .inr .fin := by simp [ofListFin, h]
      simp only [hi]
      simp [List.drop_eq_nil_of_le (by omega : l.length ≤ st)]

theorem drop_ofListFin (l : List LPS.Byte) (n : Nat) :
    (ofListFin l).drop n = ofListFin (l.drop n) := by
  apply NetStream.ext'
  intro i
  simp only [NetStream.drop, ofListFin, List.length_drop, List.getElem_drop]
  by_cases h : n + i < l.length
  · have h' : i < l.length - n := by omega
    simp [h, h']
  · have h' : ¬ i < l.length - n := by omega
    simp [h, h']

theorem take_ofListFin (l : List LPS.Byte) (k : Nat) :
    (ofListFin l).take k = (l.take k, ofListFin (l.drop k)) := by
  simp only [NetStream.take, takeFrom_ofListFin, List.drop_zero, drop_ofListFin,
    List.length_take, Prod.mk.injEq, true_and]
  congr 1
  rcases Nat.le_total k l.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.drop_eq_nil_of_le h, List.drop_eq_nil_of_le le_rfl]

theorem item_ofListFin_cons (b : LPS.Byte) (l : List LPS.Byte) :
    (ofListFin (b :: l)).item 0 = .inl b := by
  simp [ofListFin]

theorem item_ofListFin_nil : (ofListFin []).item 0 = .inr .fin := by
  simp [ofListFin]

/-! ## Words -/

theorem toNat_add_one {a : Word} (h : a.toNat + 1 < 2 ^ 64) : (a + 1).toNat = a.toNat + 1 := by
  rw [BitVec.toNat_add]
  have h1 : (1 : Word).toNat = 1 := rfl
  rw [h1, Nat.mod_eq_of_lt h]

theorem lenWord_toNat {α : Type} (l : List α) (h : l.length < 2 ^ 64) :
    (lenWord l).toNat = l.length := by
  simp only [lenWord, zw, BitVec.toNat_ofInt]
  have : ((l.length : Int) % (2 ^ 64 : Nat) : Int) = l.length := Int.emod_eq_of_lt (by omega)
    (by push_cast; omega)
  omega

/-! ## The loop's memory -/

theorem BUF_toNat : BUF.toNat = 65536 := rfl
theorem OUT_toNat : OUT.toNat = 131072 := rfl

theorem readBytesAux_writable : ∀ (k : Nat) (a : Word), BUF.toNat ≤ a.toNat →
    a.toNat + k ≤ BUF.toNat + 4096 → (readBytesAux writableByte a k).isSome
  | 0, _, _, _ => rfl
  | k + 1, a, h₁, h₂ => by
    have hw : writableByte a = some 0 := by
      simp only [writableByte]
      rw [ite_eq_left ⟨h₁, by omega⟩]
    have ha := toNat_add_one (a := a) (by rw [BUF_toNat] at h₂; omega)
    have ih := readBytesAux_writable k (a + 1) (by omega) (by omega)
    simp only [readBytesAux, hw]
    cases hr : readBytesAux writableByte (a + 1) k with
    | none => rw [hr] at ih; cases ih
    | some _ => rfl

theorem readBytesMap_writable {n : Word} (h : n.toNat ≤ 4096) :
    (readBytesMap writableByte BUF n).isSome :=
  readBytesAux_writable n.toNat BUF le_rfl (by omega)

theorem readableBytesAux_out (s : St) : ∀ (k j : Nat) (a : Word), a.toNat = OUT.toNat + j →
    j + k ≤ 4096 → readableBytesAux (readByte s) a k = ((s.out.take 4096).drop j).take k
  | 0, _, _, _, _ => by simp [readableBytesAux]
  | k + 1, j, a, ha, hk => by
    have hr : readByte s a = (s.out.take 4096)[j]? := by
      simp only [readByte]
      rw [ite_eq_left ⟨by omega, by omega⟩, show a.toNat - OUT.toNat = j by omega]
    have ha' := toNat_add_one (a := a) (by rw [OUT_toNat] at ha; omega)
    simp only [readableBytesAux, hr]
    by_cases hj : j < (s.out.take 4096).length
    · rw [List.getElem?_eq_getElem hj, readableBytesAux_out s k (j + 1) (a + 1) (by omega)
        (by omega), List.drop_eq_getElem_cons hj]
      simp
    · rw [List.getElem?_eq_none (by omega), List.drop_eq_nil_of_le (by omega)]
      simp

theorem readableBytes_out (s : St) {n : Word} (h : n.toNat ≤ 4096) :
    readableBytes (readByte s) OUT n = (s.out.take 4096).take n.toNat := by
  simp only [readableBytes]
  rw [readableBytesAux_out s n.toNat 0 OUT rfl (by omega)]
  simp

/-! ## The arms -/

theorem serverSpec_eq (i : SyscallInput) (m : LPS.Model) (o : Outcome SyscallEffect) :
    serverSpec i m o =
      match lookupArm serverTable i.sysno.toNat with
      | some a => a.spec i m o
      | none => Sys.unmodeled i m o := rfl

/-! ## Materialization without lazy reservations -/

theorem materialize_nolazy {m : LPS.Model} (h : m.vm.lazy = []) (acc : List (Word × Nat)) :
    materializeModelAccesses m acc = some m := by
  have hn : newlyMaterializedPages m.vmLazy m.vmMaterialized acc = [] := by
    simp only [newlyMaterializedPages, Model.vmLazy, h, pageInRanges, List.any_nil,
      Bool.false_and, List.filter_false]
  simp only [materializeModelAccesses, materializeAccesses, hn, Option.map_some]
  simp only [Model.withVmBacking, Model.vmLazy, Model.vmMaterialized]

/-! ## Successful calls -/

theorem accept_ok {fd addrp addrlenp : Word} (i : SyscallInput) (m : LPS.Model)
    (hf : fdLookup m.fds fd = some (.socket .listening)) (ha : addrp = 0)
    (hx : connIxExhausted m.connIx = false) (nfd : Word) (hn : fdLookup m.fds nfd = none)
    (hnfd : nfd = allocFd m.fds) :
    accept4Spec fd addrp addrlenp 0 i m
      (.ok (mkEffect nfd [] [])
        (m.withAccepted (fdInsert m.fds nfd
          (.socket (.connected (nqPeer m.net) (connChannel m.connIx) (nqScript m.net))))) []) := by
  subst ha
  unfold accept4Spec
  apply (Sys.bind_getModel _ i m _).2
  simp only [hf]
  rw [ite_eq_right (by decide), ite_eq_right (by decide)]
  rw [ite_eq_right (by decide)]
  refine Or.inr ?_
  rw [ite_eq_right (by simp [hx])]
  exact ⟨nfd, m, [], [], ⟨nfd, ⟨hn, hnfd⟩, rfl⟩,
    ⟨(), _, [], [], rfl, rfl, rfl⟩, rfl⟩

theorem read_ok {fd : Word} (i : SyscallInput) (m : LPS.Model) (peer : PeerAddr) (ch : Word)
    (l : List LPS.Byte) (hl : l ≠ []) (bs rest : List LPS.Byte) (hbs : l.take 4096 = bs)
    (hrest : l.drop 4096 = rest) (hw : i.wmem = writableByte)
    (hf : fdLookup m.fds fd = some (.socket (.connected peer ch (ofListFin l)))) :
    readSpec fd BUF (BitVec.ofNat 64 4096) i m
      (.ok (mkEffect (lenWord bs) [(BUF, bs)] [])
        (m.withFds (fdInsert m.fds fd (.socket (.connected peer ch (ofListFin rest)))))
        (bs.map (.readEv ch))) := by
  obtain ⟨b, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  have hc : rwCountClamp (BitVec.ofNat 64 4096) = (4096 : Int) := by decide
  have hlen : bs.length ≤ 4096 := hbs ▸ List.length_take_le _ _
  have hlen1 : 1 ≤ bs.length := by rw [← hbs]; simp
  have hlw : (lenWord bs).toNat ≤ 4096 := by
    rw [lenWord_toNat _ (by omega)]; exact hlen
  have h3 : ((ofListFin (b :: l')).takeZ (rwCountClamp (BitVec.ofNat 64 4096))).1 = bs := by
    rw [hc, NetStream.takeZ, ite_eq_left (by decide), take_ofListFin, ← hbs]
    rfl
  have h1 : readBytesMap i.wmem BUF 1 = some [0] := by
    rw [hw]; rfl
  have h2 := readBytesMap_writable hlw
  rw [← hw] at h2
  obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.1 h2
  have htk : (ofListFin (b :: l')).take bs.length = (bs, ofListFin rest) := by
    rw [take_ofListFin, ← hbs, ← hrest, List.length_take]
    rcases Nat.le_total 4096 (b :: l').length with h | h
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right h, List.take_of_length_le h, List.take_of_length_le le_rfl,
        List.drop_eq_nil_of_le h, List.drop_eq_nil_of_le le_rfl]
  unfold readSpec readSpecWith
  refine ⟨i, m, [], _, rfl, ?_, rfl⟩
  apply (Sys.bind_getModel _ i m _).2
  simp only [hf]
  rw [ite_eq_right (by decide), ite_eq_right (by decide)]
  simp only [item_ofListFin_cons, h1, h3, hxs]
  refine ⟨bs, m, [], _, ⟨bs, ⟨hlen1, by rw [hc]; omega, by rw [htk], by rw [hxs]; rfl⟩, rfl⟩,
    ?_, rfl⟩
  beta_reduce
  rw [htk]
  exact ⟨(), _, [], _, rfl, ⟨(), _, _, [], rfl, rfl, rfl⟩, by simp⟩

theorem read_fin {fd : Word} (i : SyscallInput) (m : LPS.Model) (peer : PeerAddr) (ch : Word)
    (hf : fdLookup m.fds fd = some (.socket (.connected peer ch (ofListFin [])))) :
    readSpec fd BUF (BitVec.ofNat 64 4096) i m (.ok (mkEffect 0 [] []) m []) := by
  unfold readSpec readSpecWith
  refine ⟨i, m, [], _, rfl, ?_, rfl⟩
  apply (Sys.bind_getModel _ i m _).2
  simp only [hf]
  rw [ite_eq_right (by decide), ite_eq_right (by decide)]
  simp only [item_ofListFin_nil]
  unfold accessOkZeroWith
  rw [ite_eq_left (by decide)]
  rfl

theorem sendto_ok {fd : Word} (i : SyscallInput) (m : LPS.Model) (peer : PeerAddr) (ch : Word)
    (s : St) (hm : i.mem = readByte s) (hne : s.out ≠ []) (bs : List LPS.Byte)
    (hbs : s.out.take 4096 = bs)
    (hf : fdLookup m.fds fd = some (.socket (.connected peer ch (ofListFin [])))) :
    ∃ eff, sendtoSpec fd OUT (BitVec.ofNat 64 (min s.out.length 4096)) NOSIG 0 0 i m
      (.ok eff m (bs.map (.writeEv ch))) ∧ eff.ret = lenWord bs ∧ eff.writes = [] := by
  have hcnt : (BitVec.ofNat 64 (min s.out.length 4096)).toNat = min s.out.length 4096 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpos : 0 < s.out.length := List.length_pos_of_ne_nil hne
  have hl : bs.length = min s.out.length 4096 := by rw [← hbs, List.length_take, Nat.min_comm]
  have hrb : readableBytes i.mem OUT (BitVec.ofNat 64 (min s.out.length 4096)) = bs := by
    rw [hm, readableBytes_out s (by rw [hcnt]; omega), hcnt, List.take_take, ← hbs]
    rcases Nat.le_total s.out.length 4096 with h | h
    · rw [List.take_of_length_le (by omega), List.take_of_length_le h]
    · congr 1
      omega
  refine ⟨(mkEffect (lenWord bs) [] []).withCopyins (([] ++ [(OUT, bs.length)]) ++ []), ?_, rfl,
    rfl⟩
  unfold sendtoSpec sendtoSpecWith
  have hmc : uns (BitVec.ofNat 64 (min s.out.length 4096)) ≤ rwBytesMax := by
    rw [uns, hcnt, rwBytesMax]; omega
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by
    simp [modeledRwCount, hmc])]
  refine ⟨i, m, [], _, rfl, ?_, rfl⟩
  apply (Sys.bind_getModel _ i m _).2
  unfold accessOkZero
  rw [ite_eq_left (by
    simp only [accessOkb, accessOkbFor, legacySv48AddressSpace, taskSize, uns, hcnt, OUT_toNat,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega)]
  simp only [hf, hrb]
  unfold sendOnSocket
  simp only [sendState, item_ofListFin_nil]
  unfold sendBytes
  have hbne : bs ≠ [] := by
    intro h; rw [h] at hl; simp at hl; omega
  rw [ite_eq_right (by
    simp only [wIs0, beq_iff_eq]
    intro h0
    have := congrArg BitVec.toNat h0
    have h00 : (0 : Word).toNat = 0 := rfl
    rw [hcnt, h00] at this
    omega)]
  rw [ite_eq_right (by simp [hbne])]
  have hb1 : 1 ≤ bs.length := by rw [hl]; omega
  have hb2 : (bs.length : Int) ≤ uns (BitVec.ofNat 64 (min s.out.length 4096)) := by
    rw [uns, hcnt, hl]
  refine ⟨bs, m, [], bs.map (.writeEv ch), ⟨bs, ⟨by exact_mod_cast hb1, hb2,
    List.take_length.symm⟩, rfl⟩, ?_, by simp⟩
  exact ⟨(), m, bs.map (.writeEv ch), [], rfl, ⟨_, m, [], [], rfl, rfl, rfl⟩, by simp⟩

theorem close_ok {fd : Word} (i : SyscallInput) (m : LPS.Model) (e : FdEntry)
    (hf : fdLookup m.fds fd = some e) :
    closeSpec fd i m (.ok (mkEffect 0 [] []) (m.withFds (fdRemove m.fds fd)) []) := by
  unfold closeSpec
  apply (Sys.bind_getModel _ i m _).2
  simp only [hf]
  exact ⟨(), _, [], [], rfl, rfl, rfl⟩

end Silmaril.Proofs.Servers.LinuxHello
