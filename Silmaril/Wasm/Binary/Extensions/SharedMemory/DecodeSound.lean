module

public import Silmaril.Wasm.Binary.Extensions.SharedMemory.Decode
public import Silmaril.Wasm.Binary.Extensions.SharedMemory.DecodeTypesSound

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.SharedMemory.Decode

open Core Core.Decode

theorem readExternType_sound : Sound (ExternType Forms.all) readExternType := by
  intro c a c' h
  obtain ⟨k, c₃, hk, h⟩ := run_bind_ok h
  obtain ⟨hb₃, hr₃⟩ := readByte_ok hk
  dsimp only at h
  split at h
  · rename_i he
    obtain rfl : k = 0x00 := UInt8.toNat_inj.mp he
    obtain ⟨x, c₄, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb₄, p₄, hr₄, hg₄⟩ := readIdx_sound hx
    refine ⟨hb₄.trans hb₃, ([0x00] ++ p₄), ?_,
      (ExternType.func hg₄)⟩
    simp [hr₃, hr₄]
  · rename_i he
    obtain rfl : k = 0x01 := UInt8.toNat_inj.mp he
    obtain ⟨x, c₄, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb₄, p₄, hr₄, hg₄⟩ := readTableType_sound hx
    refine ⟨hb₄.trans hb₃, ([0x01] ++ p₄), ?_,
      (ExternType.table hg₄)⟩
    simp [hr₃, hr₄]
  · rename_i he
    obtain rfl : k = 0x02 := UInt8.toNat_inj.mp he
    obtain ⟨x, c₄, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb₄, p₄, hr₄, hg₄⟩ := readMemType_sound hx
    refine ⟨hb₄.trans hb₃, ([0x02] ++ p₄), ?_,
      (ExternType.memory hg₄)⟩
    simp [hr₃, hr₄]
  · rename_i he
    obtain rfl : k = 0x03 := UInt8.toNat_inj.mp he
    obtain ⟨t, c₄, ht, h⟩ := run_bind_ok h
    obtain ⟨mb, c₅, hmut, h⟩ := run_bind_ok h
    obtain ⟨hb₄, p₄, hr₄, hg₄⟩ := readValType_sound ht
    obtain ⟨hb₅, hr₅⟩ := readByte_ok hmut
    split at h
    · rename_i he
      obtain rfl : mb = 0x00 := UInt8.toNat_inj.mp he
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      refine ⟨hb₅.trans (hb₄.trans hb₃),
        ([0x03] ++ (p₄ ++ [0x00])), ?_,
        (ExternType.global (Core.GlobalType.mk hg₄ Mut.const))⟩
      simp [hr₃, hr₄, hr₅]
    · rename_i he
      obtain rfl : mb = 0x01 := UInt8.toNat_inj.mp he
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      refine ⟨hb₅.trans (hb₄.trans hb₃),
        ([0x03] ++ (p₄ ++ [0x01])), ?_,
        (ExternType.global (Core.GlobalType.mk hg₄ Mut.var))⟩
      simp [hr₃, hr₄, hr₅]
    · obtain ⟨_, _, he, _⟩ := run_bind_ok h
      exact (decodeError_ok he).elim
  · rename_i he
    obtain rfl : k = 0x04 := UInt8.toNat_inj.mp he
    obtain ⟨x, c₄, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb₄, p₄, hr₄, hg₄⟩ := readTag_sound hx
    refine ⟨hb₄.trans hb₃, ([0x04] ++ p₄), ?_,
      (ExternType.tag hg₄)⟩
    simp [hr₃, hr₄]
  · exact (decodeError_ok h).elim


theorem readItem_sound : Sound (Item Forms.all) readItem := by
  intro c a c' h
  obtain ⟨n, cn, hn, h⟩ := run_bind_ok h
  obtain ⟨t, ct, ht, h⟩ := run_bind_ok h
  obtain ⟨rfl, rfl⟩ := run_pure_ok h
  obtain ⟨hb₁, pn, hr₁, hg₁⟩ := readName_sound hn
  obtain ⟨hb₂, pt, hr₂, hg₂⟩ := readExternType_sound ht
  exact ⟨hb₂.trans hb₁, pn ++ pt, by simp [hr₁, hr₂], .mk hg₁ hg₂⟩

theorem readTail_sound (m n : String) : Sound (Tail Forms.all m n) (readTail m n) := by
  intro c a c' h
  unfold readTail at h
  split at h
  · rename_i empty
    have hn : n = "" := by simpa using empty
    subst n
    obtain ⟨ob, cm, hob, h⟩ := bindOk h
    have hc : cm = c := by
      change Except.ok (_, c) = Except.ok (ob, cm) at hob
      exact (Prod.mk.inj (Except.ok.inj hob)).2.symm
    subst cm
    split at h
    · rename_i he
      obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp he
      have be : b = 0x7f := UInt8.toNat_inj.mp he
      subst b
      obtain ⟨x, cm, hx, h⟩ := bindOk h
      obtain ⟨ce, hread⟩ := peekByte_readByte (hb ▸ hob)
      rw [hx] at hread
      obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
      obtain ⟨xs, cx, hxs, h⟩ := bindOk h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hb₁, pr₁⟩ := readByte_ok hx
      obtain ⟨hb₂, p, hr₂, hg⟩ := readVec_sound readItem_sound hxs
      exact ⟨hb₂.trans hb₁, [0x7f] ++ p, by simp [pr₁, hr₂], .sharedModule hg⟩
    · rename_i he
      obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp he
      have be : b = 0x7e := UInt8.toNat_inj.mp he
      subst b
      obtain ⟨x, cm, hx, h⟩ := bindOk h
      obtain ⟨ce, hread⟩ := peekByte_readByte (hb ▸ hob)
      rw [hx] at hread
      obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
      obtain ⟨t, ct, ht, h⟩ := bindOk h
      obtain ⟨ns, cn, hns, h⟩ := bindOk h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hb₁, hr₁⟩ := readByte_ok hx
      obtain ⟨hb₂, pt, hr₂, hgt⟩ := readExternType_sound ht
      obtain ⟨hb₃, pn, hr₃, hgn⟩ := readVec_sound readName_sound hns
      exact ⟨hb₃.trans (hb₂.trans hb₁), [0x7e] ++ pt ++ pn,
        by simp [hr₁, hr₂, hr₃], .sharedAll hgt hgn⟩
    · exact sound_map readExternType_sound _ (fun _ _ ht => Tail.single ht) h
  · exact sound_map readExternType_sound _ (fun _ _ ht => Tail.single ht) h

theorem readGroup_sound : Sound (Group Forms.all) readGroup := by
  intro c a c' h
  obtain ⟨m, cm, hm, h⟩ := run_bind_ok h
  obtain ⟨n, cn, hn, h⟩ := run_bind_ok h
  obtain ⟨hb₁, pm, hr₁, hg₁⟩ := readName_sound hm
  obtain ⟨hb₂, pn, hr₂, hg₂⟩ := readName_sound hn
  obtain ⟨hb₃, pt, hr₃, hg₃⟩ := readTail_sound m n h
  exact ⟨hb₃.trans (hb₂.trans hb₁), pm ++ pn ++ pt,
    by simp [hr₁, hr₂, hr₃], .mk hg₁ hg₂ hg₃⟩

theorem readImports_sound : Sound (ImportBody Forms.all) readImports :=
  sound_map (readVec_sound readGroup_sound) List.flatten (fun _ _ hg => .mk hg)

/-- The section of rank `r` (`sectionRank`) holds the fields of `s` read so far. -/
def SecOK (s : Sections) : Nat → Bytes → Prop
  | 1, b => TypeSec Forms.all b s.types
  | 2, b => ImportSec Forms.all b s.imports
  | 3, b => FuncSec b s.funcTypes
  | 4, b => TableSec Forms.all b s.tables
  | 5, b => Section 5 (Vec (MemType Forms.all)) b s.memories
  | 6, b => TagSec Forms.all b s.tags
  | 7, b => GlobalSec Forms.all b s.globals
  | 8, b => ExportSec b s.exports
  | 9, b => StartSec b s.start
  | 10, b => ElemSec Forms.all b s.elems
  | 11, b => DataCntSec Forms.all b s.dataCount
  | 12, b => CodeSec Forms.all b s.code
  | 13, b => DataSec Forms.all b s.data
  | _, _ => False

/-- `p` is the module after its header, up to the section of rank `r` and the custom
sections after it, in the layout of `Module.mk`. -/
def Prefix (s : Sections) : Nat → Bytes → Prop
  | 0, p => Customs p
  | r + 1, p => ∃ q b c, p = q ++ b ++ c ∧ Prefix s r q ∧ SecOK s (r + 1) b ∧ Customs c

theorem SecOK.empty : ∀ k, 0 < k → k ≤ 13 → SecOK {} k []
  | 1, _, _ | 2, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 7, _, _ | 8, _, _ | 10, _, _ | 12, _, _
  | 13, _, _ => Section.empty
  | 6, _, _ => TagSec.absent
  | 9, _, _ => StartSec.mk (xs := []) Section.empty
  | 11, _, _ => DataCntSec.absent
  | 0, h, _ => absurd h (Nat.lt_irrefl 0)
  | _ + 14, _, h => absurd h (by omega)

theorem Customs.append_sec {p x : Bytes} (h : Customs p) (hx : CustomSec x) : Customs (p ++ x) := by
  induction h with
  | nil => simpa using Customs.cons hx Customs.nil
  | cons hb _ ih => simpa [List.append_assoc] using Customs.cons hb ih

theorem Prefix.custom {s : Sections} {x : Bytes} (hx : CustomSec x) :
    ∀ {r p}, Prefix s r p → Prefix s r (p ++ x)
  | 0, _, h => Customs.append_sec h hx
  | _ + 1, _, ⟨q, b, c, e, hq, hb, hc⟩ =>
    ⟨q, b, c ++ x, by simp [e, List.append_assoc], hq, hb, Customs.append_sec hc hx⟩

theorem Prefix.congr {s s' : Sections} :
    ∀ {r p}, Prefix s r p → (∀ k, k ≤ r → SecOK s' k = SecOK s k) → Prefix s' r p
  | 0, _, h, _ => h
  | r + 1, _, ⟨q, b, c, e, hq, hb, hc⟩, hk =>
    ⟨q, b, c, e, hq.congr fun k h => hk k (Nat.le_succ_of_le h), (hk (r + 1) (Nat.le_refl _)) ▸ hb, hc⟩

/-- Absent sections fill the ranks after `L`. -/
theorem Prefix.pad {s : Sections} {L : Nat} {p : Bytes} (h : Prefix s L p)
    (he : ∀ k, L < k → k ≤ 13 → SecOK s k []) : ∀ n, L ≤ n → n ≤ 13 → Prefix s n p
  | n, hL, h13 => by
    rcases Nat.eq_or_lt_of_le hL with rfl | hlt
    · exact h
    · obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact ⟨p, [], [], by simp, h.pad he n (by omega) (by omega), he _ hlt h13, Customs.nil⟩

/-- A section of rank `r` after the section of rank `L < r`. -/
theorem Prefix.sec {s s' : Sections} {L r : Nat} {p x : Bytes} (h : Prefix s L p)
    (he : ∀ k, L < k → k ≤ 13 → SecOK s k []) (hr : L < r) (h13 : r ≤ 13) (hx : SecOK s' r x)
    (hs : ∀ k, k ≠ r → SecOK s' k = SecOK s k) : Prefix s' r (p ++ x) := by
  obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  exact ⟨p, x, [], by simp, (h.pad he r (by omega) (by omega)).congr fun k hk => hs k (by omega),
    hx, Customs.nil⟩

theorem sectionRank_le (id : Nat) : sectionRank id ≤ 13 := by
  unfold sectionRank; split <;> omega

/-- The other ranks see the same fields. -/
local macro "agree" : tactic => `(tactic| (
  intro k hk
  funext x
  unfold SecOK
  split <;> first | rfl | exact absurd rfl hk))

/-- The contents of one non-custom section: `pre`, behind the id byte and a length `lb`. -/
theorem readSectionBody_ok {b : UInt8} {s s' : Sections} {c c' : Cursor}
    (h : (readSectionBody b.toNat s).run c = .ok (s', c')) :
    c'.bytes = c.bytes ∧ ∃ pre, c.rest = pre ++ c'.rest ∧
      (∀ lb, U32 lb pre.length → SecOK s' (sectionRank b.toNat) ([b] ++ lb ++ pre)) ∧
      ∀ k, k ≠ sectionRank b.toNat → SecOK s' k = SecOK s k := by
  unfold readSectionBody at h
  split at h
  case h_1 hid =>
    obtain rfl : b = 1 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readRecType_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_2 hid =>
    obtain rfl : b = 2 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readImports_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_3 hid =>
    obtain rfl : b = 3 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readIdx_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_4 hid =>
    obtain rfl : b = 4 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readTable_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_5 hid =>
    obtain rfl : b = 5 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readMemType_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_6 hid =>
    obtain rfl : b = 6 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readGlobal_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_7 hid =>
    obtain rfl : b = 7 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readExport_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_8 hid =>
    obtain rfl : b = 8 := UInt8.toNat_inj.mp hid
    obtain ⟨x, c₁, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readIdx_sound hx
    exact ⟨hb, pre, hr, fun lb hl => StartSec.mk (Section.mk hl rfl (Start.mk hg)), by agree⟩
  case h_9 hid =>
    obtain rfl : b = 9 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readElem_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_10 hid =>
    obtain rfl : b = 10 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readCode_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_11 hid =>
    obtain rfl : b = 11 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readData_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_12 hid =>
    obtain rfl : b = 12 := UInt8.toNat_inj.mp hid
    obtain ⟨n, c₁, hn, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readU_sound 32 hn
    exact ⟨hb, pre, hr, fun lb hl => DataCntSec.present rfl (Section.mk hl rfl (DataCnt.mk hg)),
      by agree⟩
  case h_13 hid =>
    obtain rfl : b = 13 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readTag_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => TagSec.present rfl (Section.mk hl rfl hg), by agree⟩
  case h_14 => exact (decodeError_ok h).elim


theorem rest_of_remaining {c c₁ : Cursor} {r : Nat} (h : remaining.run c = .ok (r, c₁)) :
    c.rest.length = r ∧ c = c₁ := by
  rw [remaining_run] at h; cases h; exact ⟨rfl, rfl⟩

/-- The section loop: the bytes it consumes extend a layout prefix. -/
theorem readModule_go_ok (fuel : Nat) : ∀ {last : Nat} {s s' : Sections} {c c' : Cursor},
    (readModule.go fuel last s).run c = .ok (s', c') → last ≤ 13 →
    (∀ k, last < k → k ≤ 13 → SecOK s k []) →
    c'.bytes = c.bytes ∧ ∃ pre last', c.rest = pre ++ c'.rest ∧ last' ≤ 13 ∧
      (∀ k, last' < k → k ≤ 13 → SecOK s' k []) ∧ ∀ p, Prefix s last p → Prefix s' last' (p ++ pre) := by
  induction fuel with
  | zero =>
    intro last s s' c c' h h13 he
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    exact ⟨rfl, [], last, by simp, h13, he, fun p hp => by simpa using hp⟩
  | succ fuel ih =>
    intro last s s' c c' h h13 he
    unfold readModule.go at h
    obtain ⟨r, c₁, hr, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := rest_of_remaining hr
    try dsimp only at h
    split at h
    · obtain ⟨rfl, rfl⟩ := run_pure_ok h
      exact ⟨rfl, [], last, by simp, h13, he, fun p hp => by simpa using hp⟩
    obtain ⟨b, c₂, hb, h⟩ := run_bind_ok h
    obtain ⟨size, c₃, hsize, h⟩ := run_bind_ok h
    obtain ⟨r₀, c₄, h₀, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := rest_of_remaining h₀
    obtain ⟨hb₁, hr₁⟩ := readByte_ok hb
    obtain ⟨hb₂, lb, hr₂, hl⟩ := readU_sound 32 hsize
    try dsimp only at h
    split at h
    case isFalse => obtain ⟨_, _, he, _⟩ := run_bind_ok h; exact (decodeError_ok he).elim
    try dsimp only at h
    split at h
    · rename_i hid
      obtain ⟨u, c₅, hc, h⟩ := run_bind_ok h
      obtain ⟨hb₃, pc, hr₃, hlen, hcu⟩ := readCustom_sound size hc
      obtain ⟨hb₄, pre, last', hr₄, h13', he', hp'⟩ := ih h h13 he
      obtain rfl : b = 0 := UInt8.toNat_inj.mp (by simpa using hid)
      refine ⟨hb₄.trans (hb₃.trans (hb₂.trans hb₁)), ([0] ++ lb ++ pc) ++ pre, last',
        by simp [hr₁, hr₂, hr₃, hr₄], h13', he', fun p hp => ?_⟩
      simpa [List.append_assoc] using hp' _ (hp.custom ⟨[()], Section.mk hl hlen.symm hcu⟩)
    try dsimp only at h
    split at h
    case isFalse => obtain ⟨_, _, he, _⟩ := run_bind_ok h; exact (decodeError_ok he).elim
    rename_i hlt
    obtain ⟨s₁, c₅, hs₁, h⟩ := run_bind_ok h
    obtain ⟨r₁, c₆, h₁, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := rest_of_remaining h₁
    try dsimp only at h
    split at h
    case isFalse => obtain ⟨_, _, he, _⟩ := run_bind_ok h; exact (decodeError_ok he).elim
    rename_i hsz
    obtain ⟨hb₃, pc, hr₃, hsec, hagree⟩ := readSectionBody_ok hs₁
    have hpc : pc.length = size := by
      have hsz : c₃.rest.length - c₅.rest.length = size := by simpa using hsz
      rw [hr₃, List.length_append] at hsz
      omega
    have he₁ : ∀ k, sectionRank b.toNat < k → k ≤ 13 → SecOK s₁ k [] := fun k hk hk13 =>
      (hagree k (by omega)) ▸ he k (by omega) hk13
    obtain ⟨hb₄, pre, last', hr₄, h13', he', hp'⟩ := ih h (sectionRank_le _) he₁
    refine ⟨hb₄.trans (hb₃.trans (hb₂.trans hb₁)), ([b] ++ lb ++ pc) ++ pre, last',
      by simp [hr₁, hr₂, hr₃, hr₄], h13', he', fun p hp => ?_⟩
    simpa [List.append_assoc] using
      hp' _ (hp.sec he hlt (sectionRank_le _) (hsec lb (hpc ▸ hl)) hagree)


/-- A complete layout is a module. -/
theorem Prefix.module {s : Sections} {p : Bytes} (h : Prefix s 13 p)
    (hf : s.funcTypes.length = s.code.length)
    (hcount : ∀ n ∈ s.dataCount, n = s.data.length)
    (hd : s.dataCount.isSome ∨ codesDataIdxs s.code = []) :
    Encodes (magic ++ version ++ p)
      { types := s.types, imports := s.imports, tags := s.tags, globals := s.globals,
        memories := s.memories, tables := s.tables, funcs := zipFuncs s.funcTypes s.code, data := s.data, elems := s.elems,
        start := s.start, exports := s.exports } := by
  obtain ⟨q, b₁₃, c₁₃, rfl, h, t₁₃, k₁₃⟩ := h
  obtain ⟨q, b₁₂, c₁₂, rfl, h, t₁₂, k₁₂⟩ := h
  obtain ⟨q, b₁₁, c₁₁, rfl, h, t₁₁, k₁₁⟩ := h
  obtain ⟨q, b₁₀, c₁₀, rfl, h, t₁₀, k₁₀⟩ := h
  obtain ⟨q, b₉, c₉, rfl, h, t₉, k₉⟩ := h
  obtain ⟨q, b₈, c₈, rfl, h, t₈, k₈⟩ := h
  obtain ⟨q, b₇, c₇, rfl, h, t₇, k₇⟩ := h
  obtain ⟨q, b₆, c₆, rfl, h, t₆, k₆⟩ := h
  obtain ⟨q, b₅, c₅, rfl, h, t₅, k₅⟩ := h
  obtain ⟨q, b₄, c₄, rfl, h, t₄, k₄⟩ := h
  obtain ⟨q, b₃, c₃, rfl, h, t₃, k₃⟩ := h
  obtain ⟨q, b₂, c₂, rfl, h, t₂, k₂⟩ := h
  obtain ⟨c₀, b₁, c₁, rfl, k₀, t₁, k₁⟩ := h
  have := Module.mk (F := Forms.all) k₀ t₁ k₁ t₂ k₂ t₃ k₃ t₄ k₄ t₅ k₅ t₆ k₆ t₇ k₇ t₈ k₈ t₉ k₉ t₁₀
    k₁₀ t₁₁ k₁₁ t₁₂ k₁₂ t₁₃ k₁₃ hcount hd hf
  simpa only [List.append_assoc] using this

/-- The whole input from any cursor: `readModule` succeeds only at the end of the input. -/
theorem readModule_sound {c c' : Cursor} {m : Wasm.Extensions.SharedMemory.Module} (h : readModule.run c = .ok (m, c')) :
    Encodes c.rest m := by
  unfold readModule at h
  obtain ⟨u, c₁, hh, h⟩ := run_bind_ok h
  obtain ⟨c₂, c₃, hg, h⟩ := run_bind_ok h
  obtain ⟨rfl, rfl⟩ : c₁ = c₂ ∧ c₁ = c₃ := by cases hg; exact ⟨rfl, rfl⟩
  obtain ⟨s, c₄, hs, h⟩ := run_bind_ok h
  obtain ⟨r, c₅, hr, h⟩ := run_bind_ok h
  obtain ⟨rfl, rfl⟩ := rest_of_remaining hr
  dsimp only at h
  split at h
  case isFalse => obtain ⟨_, _, he, _⟩ := run_bind_ok h; exact (decodeError_ok he).elim
  rename_i hend
  split at h
  case isFalse => obtain ⟨_, _, he, _⟩ := run_bind_ok h; exact (decodeError_ok he).elim
  rename_i hf
  split at h
  case isFalse => obtain ⟨_, _, he, _⟩ := run_bind_ok h; exact (decodeError_ok he).elim
  rename_i hcount
  split at h
  case isFalse => obtain ⟨_, _, he, _⟩ := run_bind_ok h; exact (decodeError_ok he).elim
  rename_i hd
  obtain ⟨rfl, -⟩ := run_pure_ok h
  obtain ⟨-, pre, hr₁, rfl⟩ := readHeader_sound hh
  obtain ⟨-, pg, last, hr₂, h13, he, hp⟩ :=
    readModule_go_ok _ hs (Nat.zero_le _) fun k hk h13 => SecOK.empty k hk h13
  have hnil : c₄.rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hend)
  rw [hr₁, hr₂, hnil, List.append_nil]
  have hp := (hp [] Customs.nil).pad he 13 h13 (Nat.le_refl _)
  rw [List.nil_append] at hp
  have hcount' : ∀ n ∈ s.dataCount, n = s.data.length := by
    cases hc : s.dataCount with
    | none => simp
    | some n => simpa [hc] using hcount
  exact hp.module (by simpa using hf) hcount' (by simpa using hd)

theorem decodeModule_sound {b : ByteArray} {m : Wasm.Extensions.SharedMemory.Module} (h : decodeModule b = .ok m) :
    Encodes b.data.toList m := by
  unfold decodeModule at h
  rw [StateT.run'_eq] at h
  cases hr : readModule.run ⟨b, 0⟩ with
  | error e => rw [hr] at h; cases h
  | ok p =>
    rw [hr] at h
    cases h
    simpa [Cursor.rest] using readModule_sound hr


end Silmaril.Wasm.Binary.Extensions.SharedMemory.Decode
