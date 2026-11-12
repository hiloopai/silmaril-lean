module

public import Silmaril.Elf.Link.Dyn.Crt.Defs
public import Silmaril.Elf.Link.Dyn.Proc.Thms
public import Silmaril.Elf.Link.Dyn.Image.Thms

/-! # The C runtime: layout facts, addresses and the image invariant

* `rel_ok`, `relAddr`: a rip-relative displacement computed by `rel` reaches its target;
* `Layout.Facts`, `Layout.facts`: what `Layout.ok` gives, as separate facts;
* `img_add`: offsets inside the image are image addresses;
* `CrtMem.keep`: the runtime's image facts survive every step that keeps the image.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Crt

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn.Proc

theorem rel_ok (x y : Nat) (hx : x < 2 ^ 31) (hy : y < 2 ^ 31) :
    BitVec.ofNat 64 x + (rel x y).signExtend 64 = BitVec.ofNat 64 y := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_add, BitVec.toInt_signExtend_of_le (by decide)]
  simp only [rel, BitVec.toInt_ofInt, BitVec.toInt_ofNat']
  have h1 : ((y : Int) - x).bmod (2 ^ 32) = (y : Int) - x :=
    Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  have h2 : (x : Int).bmod (2 ^ 64) = x :=
    Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  have h3 : (y : Int).bmod (2 ^ 64) = y :=
    Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  rw [h1, h2, h3, show (x : Int) + (y - x) = y by omega, h3]

/-- **A rip-relative operand reaches its target.** -/
theorem relAddr (b : Word) {x y : Nat} (hx : x < 2 ^ 31) (hy : y < 2 ^ 31) :
    b + BitVec.ofNat 64 x + (rel x y).signExtend 64 = b + BitVec.ofNat 64 y := by
  rw [BitVec.add_assoc, rel_ok x y hx hy]

/-- **What `Layout.ok` gives.** -/
structure Layout.Facts (L : Layout) : Prop where
  lInit : listingOk L.cInit (initL L) = true
  lStart : listingOk L.cStart (startL L) = true
  lDereg : listingOk L.cDereg (deregL L) = true
  lReg : listingOk L.cReg (regL L) = true
  lDtors : listingOk L.cDtors (dtorsL L) = true
  lFdummy : listingOk L.cFdummy (fdummyL L) = true
  lFini : listingOk L.cFini finiL = true
  lPlt : listingOk L.cPlt (pltL L) = true
  size : L.size < 2 ^ 31
  nInit : L.cInit.length = 27
  nStart : L.cStart.length = 37
  nDereg : L.cDereg.length = 41
  nReg : L.cReg.length = 57
  nDtors : L.cDtors.length = 57
  nFdummy : L.cFdummy.length = 9
  nFini : L.cFini.length = 13
  nPlt : L.cPlt.length = pltJ L + 6
  nMain : 0 < L.cMain.length
  nRo : 0 < L.cRo.length
  bInit : L.init + 27 ≤ L.size
  bStart : L.start + 37 ≤ L.size
  bDereg : L.dereg + 41 ≤ L.size
  bReg : L.reg + 57 ≤ L.size
  bDtors : L.dtors + 57 ≤ L.size
  bFdummy : L.fdummy + 9 ≤ L.size
  bFini : L.fini + 13 ≤ L.size
  bPlt : L.plt + pltJ L + 6 ≤ L.size
  bMain : L.main + L.cMain.length ≤ L.size
  bRo : L.ro + L.cRo.length ≤ L.size
  bLsm : L.gotLsm + 8 ≤ L.size
  bDereg' : L.gotDereg + 8 ≤ L.size
  bGmon : L.gotGmon + 8 ≤ L.size
  bReg' : L.gotReg + 8 ≤ L.size
  bCxa : L.gotCxa + 8 ≤ L.size
  bTmc : L.cmpl + 1 ≤ L.size
  bDso : L.dso + 8 ≤ L.size
  aInit : L.init + 27 ≤ L.tmc
  aStart : L.start + 37 ≤ L.tmc
  aDereg : L.dereg + 41 ≤ L.tmc
  aReg : L.reg + 57 ≤ L.tmc
  aDtors : L.dtors + 57 ≤ L.tmc
  aFdummy : L.fdummy + 9 ≤ L.tmc
  aFini : L.fini + 13 ≤ L.tmc
  aPlt : L.plt + pltJ L + 6 ≤ L.tmc
  aMain : L.main + L.cMain.length ≤ L.tmc
  aRo : L.ro + L.cRo.length ≤ L.tmc
  aLsm : L.gotLsm + 8 ≤ L.tmc
  aDereg' : L.gotDereg + 8 ≤ L.tmc
  aGmon : L.gotGmon + 8 ≤ L.tmc
  aReg' : L.gotReg + 8 ≤ L.tmc
  aCxa : L.gotCxa + 8 ≤ L.tmc
  aDso : L.dso + 8 ≤ L.tmc
  tc : L.tmc ≤ L.cmpl

theorem Layout.facts {L : Layout} (h : L.ok = true) : L.Facts := by
  simp only [Layout.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    Bool.and_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- An offset inside the image is an image address. -/
theorem img_add {L : Layout} {b : Word} (hb : b.toNat + L.size < 2 ^ 64) {n : Nat}
    (hn : n < L.size) : Img L b (b + BitVec.ofNat 64 n).toNat := by
  rw [addr_toNat (by omega)]; exact ⟨by omega, by omega⟩

/-- A read inside the image is kept by a step that keeps the image. -/
theorem keeps_range {L : Layout} {b : Word} (hb : b.toNat + L.size < 2 ^ 64) {m m' : Memory}
    (h : Keeps (Img L b) m m') {off len : Nat} (hr : off + len ≤ L.size) {acc : Access} :
    m'.readWith acc (b + BitVec.ofNat 64 off).toNat len =
      m.readWith acc (b + BitVec.ofNat 64 off).toNat len := by
  rw [addr_toNat (by omega)]
  exact h.readWith (fun k hk => ⟨by omega, by omega⟩)

theorem keeps_loaded {L : Layout} {b : Word} (hb : b.toNat + L.size < 2 ^ 64) {m m' : Memory}
    (h : Keeps (Img L b) m m') {off : Nat} {code : List Byte} (hr : off + code.length ≤ L.size)
    (hl : Loaded m (b + BitVec.ofNat 64 off) code) : Loaded m' (b + BitVec.ofNat 64 off) code := by
  unfold Loaded Memory.fetchBytes at hl ⊢
  rw [keeps_range hb h hr]; exact hl

theorem keeps_loadN {L : Layout} {b : Word} (hb : b.toNat + L.size < 2 ^ 64) {m m' : Memory}
    (h : Keeps (Img L b) m m') {off : Nat} (hr : off + 8 ≤ L.size) :
    loadN m' (b + BitVec.ofNat 64 off) 8 = loadN m (b + BitVec.ofNat 64 off) 8 := by
  simp only [loadN, Memory.readBytes]
  rw [keeps_range hb h hr]

/-- What the library keeps includes the image. -/
theorem keeps_img {L : Layout} {b : Word} {W : World} (hW : W.InImage = Img L b) {m m' : Memory}
    (h : Keeps W.Kept m m') : Keeps (Img L b) m m' :=
  Keeps.mono h (fun a ha => Or.inl (by rw [hW]; exact ha))

/-- Permissions of kept addresses are unchanged. -/
theorem Keeps.checkSpan {P : Nat → Prop} {m m' : Memory} (h : Keeps P m m') {acc : Access}
    {a len : Nat} (hP : ∀ k < len, P (a + k)) : m'.checkSpan acc a len = m.checkSpan acc a len := by
  unfold Memory.checkSpan
  congr 1
  simp only [List.all_eq, decide_eq_decide]
  constructor <;> intro hall k hk
  · rw [← (h (a + k) (hP k (List.mem_range.mp hk))).2 acc]; exact hall k hk
  · rw [(h (a + k) (hP k (List.mem_range.mp hk))).2 acc]; exact hall k hk

theorem Keeps.permitted {P : Nat → Prop} {m m' : Memory} (h : Keeps P m m') {acc : Access}
    {a len : Nat} (hP : ∀ k < len, P (a + k)) (hp : m.Permitted acc a len) :
    m'.Permitted acc a len := by
  unfold Memory.Permitted at hp ⊢; rw [Keeps.checkSpan h hP]; exact hp

/-- **The runtime's image facts survive every step that keeps the image.** -/
theorem CrtMem.keep {L : Layout} (F : L.Facts) {b lsmA cxaA : Word} {cv : Byte}
    (hb : b.toNat + L.size < 2 ^ 64) {m m' : Memory} (hm : CrtMem L b lsmA cxaA cv m)
    (h : Keeps (Img L b) m m') : CrtMem L b lsmA cxaA cv m' where
  init := keeps_loaded hb h (by rw [F.nInit]; exact F.bInit) hm.init
  start := keeps_loaded hb h (by rw [F.nStart]; exact F.bStart) hm.start
  dereg := keeps_loaded hb h (by rw [F.nDereg]; exact F.bDereg) hm.dereg
  reg := keeps_loaded hb h (by rw [F.nReg]; exact F.bReg) hm.reg
  dtors := keeps_loaded hb h (by rw [F.nDtors]; exact F.bDtors) hm.dtors
  fdummy := keeps_loaded hb h (by rw [F.nFdummy]; exact F.bFdummy) hm.fdummy
  fini := keeps_loaded hb h (by rw [F.nFini]; exact F.bFini) hm.fini
  plt := keeps_loaded hb h (by rw [F.nPlt]; have := F.bPlt; omega) hm.plt
  main := keeps_loaded hb h F.bMain hm.main
  rodata := by
    have hd := hm.rodata
    unfold Memory.readBytes at hd ⊢
    rw [keeps_range hb h F.bRo]; exact hd
  lsm := (keeps_loadN hb h F.bLsm).trans hm.lsm
  gDereg := (keeps_loadN hb h F.bDereg').trans hm.gDereg
  gGmon := (keeps_loadN hb h F.bGmon).trans hm.gGmon
  gReg := (keeps_loadN hb h F.bReg').trans hm.gReg
  cxa := (keeps_loadN hb h F.bCxa).trans hm.cxa
  dso := (keeps_loadN hb h F.bDso).trans hm.dso
  done := by
    have hd := hm.done
    unfold Memory.readBytes at hd ⊢
    rw [keeps_range hb h F.bTmc]; exact hd
  wDone := by
    have hw := hm.wDone
    rw [addr_toNat (by have := F.bTmc; omega)] at hw ⊢
    exact Keeps.permitted h (fun k hk => ⟨by omega, by have := F.bTmc; omega⟩) hw

/-- **Setting `completed.0`** keeps every other image fact. -/
theorem CrtMem.store_done {L : Layout} (F : L.Facts) {b lsmA cxaA : Word} {cv : Byte}
    (hb : b.toNat + L.size < 2 ^ 64) {m m' : Memory} (hm : CrtMem L b lsmA cxaA cv m)
    (hs : Silmaril.X86.Ext.storeN m (b + BitVec.ofNat 64 L.cmpl) 1 1#64 = some m') :
    CrtMem L b lsmA cxaA 1#8 m' := by
  have S := Silmaril.X86.Ext.Stored.of_storeN hs
  have ht : (b + BitVec.ofNat 64 L.cmpl).toNat = b.toNat + L.cmpl := addr_toNat (by have := F.bTmc; omega)
  have htc := F.tc
  have hlen : (Silmaril.X86.Ext.leBytes 1#64 1).length = 1 := by simp [Silmaril.X86.Ext.leBytes]
  have dis : ∀ off len, off + len ≤ L.tmc → ∀ acc, m'.readWith acc (b + BitVec.ofNat 64 off).toNat len =
      m.readWith acc (b + BitVec.ofNat 64 off).toNat len := fun off len h acc =>
    S.readWith_disjoint acc _ _ (Or.inl (by rw [addr_toNat (by have := F.bTmc; omega), ht]; omega))
  have ld : ∀ {off : Nat} {code : List Byte}, off + code.length ≤ L.tmc →
      Loaded m (b + BitVec.ofNat 64 off) code → Loaded m' (b + BitVec.ofNat 64 off) code := by
    intro off code h hl
    unfold Loaded Memory.fetchBytes at hl ⊢; rw [dis _ _ h]; exact hl
  have ln : ∀ {off : Nat} {v : Word}, off + 8 ≤ L.tmc → loadN m (b + BitVec.ofNat 64 off) 8 = some v →
      loadN m' (b + BitVec.ofNat 64 off) 8 = some v := by
    intro off v h hl
    simp only [loadN, Memory.readBytes] at hl ⊢; rw [dis _ _ h]; exact hl
  refine ⟨ld (by rw [F.nInit]; exact F.aInit) hm.init, ld (by rw [F.nStart]; exact F.aStart) hm.start,
    ld (by rw [F.nDereg]; exact F.aDereg) hm.dereg, ld (by rw [F.nReg]; exact F.aReg) hm.reg,
    ld (by rw [F.nDtors]; exact F.aDtors) hm.dtors, ld (by rw [F.nFdummy]; exact F.aFdummy) hm.fdummy,
    ld (by rw [F.nFini]; exact F.aFini) hm.fini, ld (by rw [F.nPlt]; have := F.aPlt; omega) hm.plt,
    ld F.aMain hm.main, by unfold Memory.readBytes; rw [dis _ _ F.aRo]; exact hm.rodata,
    ln F.aLsm hm.lsm, ln F.aDereg' hm.gDereg, ln F.aGmon hm.gGmon, ln F.aReg' hm.gReg,
    ln F.aCxa hm.cxa, ln F.aDso hm.dso, ?_, S.permitted hm.wDone⟩
  have hp : m.Permitted .read (b + BitVec.ofNat 64 L.cmpl).toNat (Silmaril.X86.Ext.leBytes 1#64 1).length := by
    rw [hlen]; exact Memory.readWith_permitted hm.done
  have := S.readWith_self hp
  rw [hlen] at this
  unfold Memory.readBytes
  rw [this]; decide

end Silmaril.Elf.Link.Dyn.Crt
