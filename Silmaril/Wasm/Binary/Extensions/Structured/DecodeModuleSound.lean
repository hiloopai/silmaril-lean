module

public import Silmaril.Wasm.Binary.Extensions.Structured.DecodeModule
public import Silmaril.Wasm.Binary.Extensions.SharedMemory.DecodeSound

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.Structured.DecodeModule

open Core Core.Decode

theorem readCode_sound {Body : Type} {E : Bytes → Body → Prop}
    (reader : DecodeM Body) (hreader : Sound E reader) :
    Sound (Code Forms.all E) (readCode reader) := by
  intro c a c' h
  obtain ⟨size, c₁, hsize, h⟩ := run_bind_ok h
  obtain ⟨r₀, c₂, h₀, h⟩ := run_bind_ok h
  obtain ⟨rfl, rfl⟩ : c₁.rest.length = r₀ ∧ c₁ = c₂ := by
    rw [remaining_run] at h₀; cases h₀; exact ⟨rfl, rfl⟩
  split at h
  · obtain ⟨gs, c₃, hgs, h⟩ := run_bind_ok h
    dsimp only at h
    split at h
    · rename_i htot
      obtain ⟨body, c₄, hbody, h⟩ := run_bind_ok h
      obtain ⟨r₁, c₅, h₁, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ : c₄.rest.length = r₁ ∧ c₄ = c₅ := by
        rw [remaining_run] at h₁; cases h₁; exact ⟨rfl, rfl⟩
      split at h
      · rename_i hlen
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        obtain ⟨hb₁, p₁, hr₁, hg₁⟩ := readU_sound 32 hsize
        obtain ⟨hb₂, p₂, hr₂, hg₂⟩ := readVec_sound readLocals_sound hgs
        obtain ⟨hb₃, p₃, hr₃, hg₃⟩ := hreader hbody
        have hlen : c₁.rest.length - c₄.rest.length = size := by simpa using hlen
        rw [hr₂, hr₃] at hlen
        refine ⟨hb₃.trans (hb₂.trans hb₁), p₁ ++ (p₂ ++ p₃), by simp [hr₁, hr₂, hr₃], ?_⟩
        have hfl : (gs.flatMap fun p => List.replicate p.1 p.2) =
            (gs.map fun p => List.replicate p.1 p.2).flatten := List.flatMap_def
        rw [hfl]
        refine Code.mk hg₁ (by simp at hlen ⊢; omega) (Func.mk (vec_map (fun p : Nat × Wasm.ValType => List.replicate p.1 p.2) (fun _ _ h => h) hg₂) hg₃ ?_)
        rw [← hfl]
        have := foldl_locals gs 0
        simp only [maxLocals] at htot
        omega
      · obtain ⟨_, _, he, _⟩ := run_bind_ok h
        exact (decodeError_ok he).elim
    · obtain ⟨_, _, he, _⟩ := run_bind_ok h
      exact (decodeError_ok he).elim
  · obtain ⟨_, _, he, _⟩ := run_bind_ok h
    exact (decodeError_ok he).elim

variable {Body : Type} {E : Bytes → Body → Prop}

/-- The section of rank `r` (`sectionRank`) holds the fields of `s` read so far. -/
def SecOK (E : Bytes → Body → Prop) (s : Sections Body) : Nat → Bytes → Prop
  | 1, b => TypeSec Forms.all b s.types
  | 2, b => SharedMemory.ImportSec Forms.all b s.imports
  | 3, b => FuncSec b s.funcTypes
  | 4, b => TableSec Forms.all b s.tables
  | 5, b => Section 5 (Vec (SharedMemory.MemType Forms.all)) b s.memories
  | 6, b => TagSec Forms.all b s.tags
  | 7, b => GlobalSec Forms.all b s.globals
  | 8, b => ExportSec b s.exports
  | 9, b => StartSec b s.start
  | 10, b => ElemSec Forms.all b s.elems
  | 11, b => DataCntSec Forms.all b s.dataCount
  | 12, b => CodeSec Forms.all E b s.code
  | 13, b => DataSec Forms.all b s.data
  | _, _ => False

/-- `p` is the module after its header, up to the section of rank `r` and the custom
sections after it, in the layout of `Module.mk`. -/
def Prefix (E : Bytes → Body → Prop) (s : Sections Body) : Nat → Bytes → Prop
  | 0, p => Customs p
  | r + 1, p => ∃ q b c, p = q ++ b ++ c ∧ Prefix E s r q ∧ SecOK E s (r + 1) b ∧ Customs c

theorem SecOK.empty (E : Bytes → Body → Prop) : ∀ k, 0 < k → k ≤ 13 → SecOK E {} k []
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

theorem Prefix.custom {s : Sections Body} {x : Bytes} (hx : CustomSec x) :
    ∀ {r p}, Prefix E s r p → Prefix E s r (p ++ x)
  | 0, _, h => Customs.append_sec h hx
  | _ + 1, _, ⟨q, b, c, e, hq, hb, hc⟩ =>
    ⟨q, b, c ++ x, by simp [e, List.append_assoc], hq, hb, Customs.append_sec hc hx⟩

theorem Prefix.congr {s s' : Sections Body} :
    ∀ {r p}, Prefix E s r p → (∀ k, k ≤ r → SecOK E s' k = SecOK E s k) → Prefix E s' r p
  | 0, _, h, _ => h
  | r + 1, _, ⟨q, b, c, e, hq, hb, hc⟩, hk =>
    ⟨q, b, c, e, hq.congr fun k h => hk k (Nat.le_succ_of_le h), (hk (r + 1) (Nat.le_refl _)) ▸ hb, hc⟩

/-- Absent sections fill the ranks after `L`. -/
theorem Prefix.pad {s : Sections Body} {L : Nat} {p : Bytes} (h : Prefix E s L p)
    (he : ∀ k, L < k → k ≤ 13 → SecOK E s k []) : ∀ n, L ≤ n → n ≤ 13 → Prefix E s n p
  | n, hL, h13 => by
    rcases Nat.eq_or_lt_of_le hL with rfl | hlt
    · exact h
    · obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact ⟨p, [], [], by simp, h.pad he n (by omega) (by omega), he _ hlt h13, Customs.nil⟩

/-- A section of rank `r` after the section of rank `L < r`. -/
theorem Prefix.sec {s s' : Sections Body} {L r : Nat} {p x : Bytes} (h : Prefix E s L p)
    (he : ∀ k, L < k → k ≤ 13 → SecOK E s k []) (hr : L < r) (h13 : r ≤ 13) (hx : SecOK E s' r x)
    (hs : ∀ k, k ≠ r → SecOK E s' k = SecOK E s k) : Prefix E s' r (p ++ x) := by
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
theorem readSectionBody_ok (reader : DecodeM Body) (hreader : Sound E reader) {b : UInt8} {s s' : Sections Body} {c c' : Cursor}
    (h : (readSectionBody reader b.toNat s).run c = .ok (s', c')) :
    c'.bytes = c.bytes ∧ ∃ pre, c.rest = pre ++ c'.rest ∧
      (∀ lb, U32 lb pre.length → SecOK E s' (sectionRank b.toNat) ([b] ++ lb ++ pre)) ∧
      ∀ k, k ≠ sectionRank b.toNat → SecOK E s' k = SecOK E s k := by
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
    obtain ⟨hb, pre, hr, hg⟩ := SharedMemory.Decode.readImports_sound hxs
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
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound SharedMemory.Decode.readMemType_sound hxs
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
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound (readCode_sound reader hreader) hxs
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
theorem readModule_go_ok (reader : DecodeM Body) (hreader : Sound E reader) (fuel : Nat) : ∀ {last : Nat} {s s' : Sections Body} {c c' : Cursor},
    (readModule.go reader fuel last s).run c = .ok (s', c') → last ≤ 13 →
    (∀ k, last < k → k ≤ 13 → SecOK E s k []) →
    c'.bytes = c.bytes ∧ ∃ pre last', c.rest = pre ++ c'.rest ∧ last' ≤ 13 ∧
      (∀ k, last' < k → k ≤ 13 → SecOK E s' k []) ∧ ∀ p, Prefix E s last p → Prefix E s' last' (p ++ pre) := by
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
    obtain ⟨hb₃, pc, hr₃, hsec, hagree⟩ := readSectionBody_ok reader hreader hs₁
    have hpc : pc.length = size := by
      have hsz : c₃.rest.length - c₅.rest.length = size := by simpa using hsz
      rw [hr₃, List.length_append] at hsz
      omega
    have he₁ : ∀ k, sectionRank b.toNat < k → k ≤ 13 → SecOK E s₁ k [] := fun k hk hk13 =>
      (hagree k (by omega)) ▸ he k (by omega) hk13
    obtain ⟨hb₄, pre, last', hr₄, h13', he', hp'⟩ := ih h (sectionRank_le _) he₁
    refine ⟨hb₄.trans (hb₃.trans (hb₂.trans hb₁)), ([b] ++ lb ++ pc) ++ pre, last',
      by simp [hr₁, hr₂, hr₃, hr₄], h13', he', fun p hp => ?_⟩
    simpa [List.append_assoc] using
      hp' _ (hp.sec he hlt (sectionRank_le _) (hsec lb (hpc ▸ hl)) hagree)


/-- A complete layout is a module. -/
theorem Prefix.module (dataIdxs : Body → List DataIdx) {s : Sections Body} {p : Bytes} (h : Prefix E s 13 p)
    (hf : s.funcTypes.length = s.code.length)
    (hcount : ∀ n ∈ s.dataCount, n = s.data.length)
    (hd : s.dataCount.isSome ∨ codesDataIdxs dataIdxs s.code = []) :
    Module Forms.all E dataIdxs (magic ++ version ++ p)
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
theorem readModule_sound (reader : DecodeM Body) (hreader : Sound E reader)
    (dataIdxs : Body → List DataIdx) {c c' : Cursor} {m : Wasm.Extensions.Structured.FunctionModule Body} (h : (readModule reader dataIdxs).run c = .ok (m, c')) :
    Module Forms.all E dataIdxs c.rest m := by
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
    readModule_go_ok reader hreader _ hs (Nat.zero_le _) fun k hk h13 => SecOK.empty E k hk h13
  have hnil : c₄.rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hend)
  rw [hr₁, hr₂, hnil, List.append_nil]
  have hp := (hp [] Customs.nil).pad he 13 h13 (Nat.le_refl _)
  rw [List.nil_append] at hp
  have hcount' : ∀ n ∈ s.dataCount, n = s.data.length := by
    cases hc : s.dataCount with
    | none => simp
    | some n => simpa [hc] using hcount
  exact hp.module dataIdxs (by simpa using hf) hcount' (by simpa using hd)

theorem decodeModule_sound (reader : DecodeM Body) (hreader : Sound E reader)
    (dataIdxs : Body → List DataIdx) {b : ByteArray} {m : Wasm.Extensions.Structured.FunctionModule Body} (h : decodeModule reader dataIdxs b = .ok m) :
    Module Forms.all E dataIdxs b.data.toList m := by
  unfold decodeModule at h
  rw [StateT.run'_eq] at h
  cases hr : (readModule reader dataIdxs).run ⟨b, 0⟩ with
  | error e => rw [hr] at h; cases h
  | ok p =>
    rw [hr] at h
    cases h
    simpa [Cursor.rest] using readModule_sound reader hreader dataIdxs hr


end Silmaril.Wasm.Binary.Extensions.Structured.DecodeModule
