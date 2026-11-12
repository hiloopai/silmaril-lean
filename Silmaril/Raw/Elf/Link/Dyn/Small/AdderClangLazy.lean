module

public import Silmaril.Raw.Elf.Link.Dyn.Small.AdderClangMain

/-! # The adder (clang) under lazy binding: the world, the certificate, the image facts

`adder-clang` has no `DF_BIND_NOW`, so `ld.so` may bind its two `JUMP_SLOT`s lazily
(`LD_BIND_NOW` unset): each slot then holds its PLT entry's `push $j` and `GOT[2]` the resolver.
A first call goes `printf@plt → push $j → PLT0 → push GOT[1] → jmp *GOT[2]` into the resolver
contract (`Proc.resolveStep`), which binds the slot and enters the function.

* `adderClangWorldL`: the world with the resolver `res` and the slots `(0x4000, printf)`,
  `(0x4008, __isoc99_scanf)` (`DT_JMPREL` order);
* `adderClang_slots_lazy`: **the lazy binding certificate** (`decide +kernel`, sound by
  `slots_of_known`);
* `PltL`: what the PLT needs (the three entries' code, `GOT[1]`, `GOT[2] = res`, the two slots
  holding their `push`, both slots readable and writable), from the loader relation
  (`pltL_of_loaded`);
* `CrtMem.keepH`: the runtime's image facts survive a step that keeps the image except a
  range (`ImgH`) none of them reads (`Layout.avoids`): a bound slot;
* `must_resolveJ`: the resolver step for slot `j` of a slot list.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Small

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn retOf)
open Silmaril.Elf.Link.DynElf.Elf
open Silmaril.Elf.Link.Dyn.Glibc
open Silmaril.Elf.Link.Dyn.Hello
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Crt
open Silmaril.Elf.Link.Dyn.Stdio

/-! ## The world -/

/-- The `DT_JMPREL` slots and their eager values: `printf` (index 0), `__isoc99_scanf` (1). -/
def adderClangJmp (lb : Word) : List (Nat × Word) := [(0x4000, printfAt lb), (0x4008, scanfAt lb)]

/-- The process world of `adderClang` under lazy binding, with the resolver at `res`. -/
def adderClangWorldL (b lb gate res : Word) (rel : Bool) : World :=
  crtWorld adderClangLayout b gate (some (res, adderClangJmp lb))
    [(lsmAt lb, .libcStartMain), (cxaAt lb, .cxaFinalize),
     (scanfAt lb, .named (Silmaril.Elf.Link.DynElf.nm "__isoc99_scanf")),
     (printfAt lb, .named (Silmaril.Elf.Link.DynElf.nm "printf"))] rel
    (stdioNamed (Img adderClangLayout b) rel)

theorem adderClangL_scanf (b lb gate res : Word) (rel : Bool) (s : PState)
    (r : Silmaril.X86.RelIsa.Res PState) :
    fnStep (adderClangWorldL b lb gate res rel) (.named (Silmaril.Elf.Link.DynElf.nm "__isoc99_scanf")) s r ↔
      scanfStep (Img adderClangLayout b) s r := by
  simp only [fnStep, adderClangWorldL, crtWorld, stdioNamed]
  rw [ite_eq_left trivial]

theorem adderClangL_printf (b lb gate res : Word) (rel : Bool) (s : PState)
    (r : Silmaril.X86.RelIsa.Res PState) :
    fnStep (adderClangWorldL b lb gate res rel) (.named (Silmaril.Elf.Link.DynElf.nm "printf")) s r ↔
      printfStepWith .rdi .rsi (Img adderClangLayout b) rel s r := by
  simp only [fnStep, adderClangWorldL, crtWorld, stdioNamed]
  rw [ite_eq_right (by decide), ite_eq_left trivial]

/-- Where the loader put things, for `adderClang` under lazy binding: as eagerly, and the
resolver outside the image and distinct from the gate and the bound functions. -/
structure AdderPlacedL (b lb gate res : Word) : Prop where
  base : AdderPlaced adderClangLayout b lb gate
  res_out : ¬ Img adderClangLayout b res.toNat
  res_gate : res ≠ gate
  res_lsm : res ≠ lsmAt lb
  res_cxa : res ≠ cxaAt lb
  res_sc : res ≠ scanfAt lb
  res_pf : res ≠ printfAt lb

theorem adderClangL_env {b lb gate res : Word} {rel : Bool} (P : AdderPlacedL b lb gate res) :
    CrtEnv adderClangLayout (adderClangWorldL b lb gate res rel) b (lsmAt lb) (cxaAt lb) where
  hW := rfl
  hb := P.base.base.hb
  gate_out := P.base.base.gate_out
  cxa_out := P.base.base.cxa_out
  cxa_gate := P.base.base.cxa_gate
  cxa_res := fun _ _ h => by
    simp only [adderClangWorldL, crtWorld, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact Ne.symm P.res_cxa
  cxa_fn := by simp [adderClangWorldL, crtWorld]
  cxa_ne := P.base.base.cxa_ne
  lsm_out := P.base.base.lsm_out
  lsm_gate := P.base.base.lsm_gate
  lsm_res := fun _ _ h => by
    simp only [adderClangWorldL, crtWorld, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact Ne.symm P.res_lsm
  lsm_fn := by simp [adderClangWorldL, crtWorld]

/-! ## The lazy binding certificate -/

/-- Lazy binding: `GOT[1]` unconstrained, `GOT[2]` the resolver, the jump slots their PLT
entries' `push`. -/
def adderClangSlotsLazy : List (Nat × Val) :=
  [(0x3ff0, .any), (0x3ff8, .resolver), (0x3dd0, .addr 0 4416), (0x3dd8, .addr 0 4352),
   (0x4018, .addr 0 16408), (0x3fc0, .addr 1 0x2a200), (0x3fc8, .abs 0), (0x3fd0, .abs 0),
   (0x3fd8, .abs 0), (0x3fe0, .addr 1 0x472c0), (0x4000, .addr 0 0x1036), (0x4008, .addr 0 0x1046)]

theorem adderClang_bindNow : adderClangInfo.bindNow = false := by decide +kernel

theorem adderClang_slots_K_lazy :
    slotsWith (resolveK [exeFacts adderClangRefs, libcFactsS, ldFactsS]) true adderClangFile
      adderClangInfo = some adderClangSlotsLazy := by decide +kernel

theorem adderClang_img_lazy : adderClangLayout.imageOk adderClangFile adderClangInfo adderClangTextPh
    adderClangRoPh adderClangRwPh adderClangSlotsLazy 0x2a200 0x472c0 = true := by decide +kernel

theorem adderClang_slots_lazy {Fc Fl : Blob} (hc : ChunksOf Fc libcChunksS)
    (hl : ChunksOf Fl ldChunksS) :
    slots [adderClangFile, Fc, Fl] true adderClangFile adderClangInfo = some adderClangSlotsLazy := by
  have := slots_of_known (ks := [⟨adderClangFile, adderClangInfo, exeFacts adderClangRefs⟩,
      ⟨Fc, libcInfo, libcFactsS⟩, ⟨Fl, ldInfo, ldFactsS⟩])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact exeKnown_ok adderClang_info adderClang_refs
      · exact libcKnownS_ok hc
      · exact ldKnownS_ok hl) adderClang_slots_K_lazy
  simpa using this

/-! ## The PLT under lazy binding -/

/-- `PLT0`, `printf@plt`, `__isoc99_scanf@plt`. -/
def adderClangPltL : List (Nat × List Byte) :=
  [(0x1020, [0xff, 0x35, 0xca, 0x2f, 0x00, 0x00, 0xff, 0x25, 0xcc, 0x2f, 0x00, 0x00]),
   (0x1030, [0xff, 0x25, 0xca, 0x2f, 0x00, 0x00, 0x68, 0x00, 0x00, 0x00, 0x00, 0xe9, 0xe0, 0xff, 0xff, 0xff]),
   (0x1040, [0xff, 0x25, 0xc2, 0x2f, 0x00, 0x00, 0x68, 0x01, 0x00, 0x00, 0x00, 0xe9, 0xd0, 0xff, 0xff, 0xff])]

/-- What the lazy PLT needs of memory, with `printf`'s slot unbound. -/
structure Plt0 (b res : Word) (mem : Memory) : Prop where
  code : ∀ c ∈ adderClangPltL, Loaded mem (b + BitVec.ofNat 64 c.1) c.2
  got1 : ∃ w, loadN mem (b + 0x3ff0#64) 8 = some w
  got2 : loadN mem (b + 0x3ff8#64) 8 = some res
  slot0 : loadN mem (b + 0x4000#64) 8 = some (b + 0x1036#64)
  rw0 : mem.Permitted .read (b + 0x4000#64).toNat 8 ∧ mem.Permitted .write (b + 0x4000#64).toNat 8

/-- … and `scanf`'s slot unbound as well (the state at entry). -/
structure PltL (b res : Word) (mem : Memory) : Prop extends Plt0 b res mem where
  slot1 : loadN mem (b + 0x4008#64) 8 = some (b + 0x1046#64)
  rw1 : mem.Permitted .read (b + 0x4008#64).toNat 8 ∧ mem.Permitted .write (b + 0x4008#64).toNat 8

theorem pltL_code0 : plainIn adderClangFile adderClangInfo adderClangTextPh adderClangSlotsLazy .execute
    0x1020 [0xff, 0x35, 0xca, 0x2f, 0x00, 0x00, 0xff, 0x25, 0xcc, 0x2f, 0x00, 0x00] = true := by
  decide +kernel
theorem pltL_code1 : plainIn adderClangFile adderClangInfo adderClangTextPh adderClangSlotsLazy .execute
    0x1030 [0xff, 0x25, 0xca, 0x2f, 0x00, 0x00, 0x68, 0x00, 0x00, 0x00, 0x00, 0xe9, 0xe0, 0xff, 0xff, 0xff] =
    true := by
  decide +kernel
theorem pltL_code2 : plainIn adderClangFile adderClangInfo adderClangTextPh adderClangSlotsLazy .execute
    0x1040 [0xff, 0x25, 0xc2, 0x2f, 0x00, 0x00, 0x68, 0x01, 0x00, 0x00, 0x00, 0xe9, 0xd0, 0xff, 0xff, 0xff] =
    true := by
  decide +kernel
theorem pltL_got2 : slotIn adderClangInfo adderClangRwPh adderClangSlotsLazy 0x3ff8 .resolver = true := by
  decide +kernel
theorem pltL_slot0 : slotIn adderClangInfo adderClangRwPh adderClangSlotsLazy 0x4000 (.addr 0 0x1036) =
    true := by decide +kernel
theorem pltL_slot1 : slotIn adderClangInfo adderClangRwPh adderClangSlotsLazy 0x4008 (.addr 0 0x1046) =
    true := by decide +kernel

theorem adderClang_rwPh : adderClangRwPh ∈ adderClangInfo.phs := by decide +kernel
theorem relro_4000 : ∀ k < 8, inRelro adderClangInfo (0x4000 + k) = false := by decide +kernel
theorem relro_4008 : ∀ k < 8, inRelro adderClangInfo (0x4008 + k) = false := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The lazy PLT's facts from the loader relation.** -/
theorem pltL_of_loaded {Fc Fl : Blob} (hc : ChunksOf Fc libcChunksS) (hl : ChunksOf Fl ldChunksS)
    {b lb ldb res : Word} {ifn : Word → Option Word} {mem : Memory}
    (h : ExeLoaded [adderClangFile, Fc, Fl] [b, lb, ldb] ifn true res mem) : PltL b res mem := by
  obtain ⟨f', b', i', D', T, hf, hb, hi', -, hD', hT, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  rw [adderClang_info, Option.some.injEq] at hi'
  subst hi'
  rw [adderClang_slots_lazy hc hl, Option.some.injEq] at hD'
  subst hD'
  have hcode : ∀ c ∈ adderClangPltL,
      plainIn adderClangFile adderClangInfo adderClangTextPh adderClangSlotsLazy .execute c.1 c.2 = true := by
    intro c hc
    simp only [adderClangPltL, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact pltL_code0
    · exact pltL_code1
    · exact pltL_code2
  have h2 := pltL_got2
  have h3 := pltL_slot0
  have h4 := pltL_slot1
  have rw0 := himg.permittedRW adderClang_rwPh rfl (v := 0x4000) (len := 8) (by decide) (by decide)
    (by decide) (by decide) (by decide) relro_4000
  have rw1 := himg.permittedRW adderClang_rwPh rfl (v := 0x4008) (len := 8) (by decide) (by decide)
    (by decide) (by decide) (by decide) relro_4008
  obtain ⟨w, hw⟩ := himg.loadSome adderClang_rwPh rfl (s := 0x3ff0) (by decide) (by decide) (by decide)
  exact ⟨⟨fun c hc' => plainIn_read himg hT (hcode c hc'), ⟨w, by simpa using hw⟩,
    by simpa using slotIn_load himg hT h2 (by simp [Val.word]),
    by simpa using slotIn_load himg hT h3 (by simp [Val.word]), by simpa using rw0⟩,
    by simpa using slotIn_load himg hT h4 (by simp [Val.word]), by simpa using rw1⟩

/-! ## Keeping the image except a range -/

/-- The image except `[b + lo, b + hi)`. -/
def ImgH (L : Layout) (b : Word) (lo hi : Nat) (a : Nat) : Prop :=
  Img L b a ∧ ¬ (b.toNat + lo ≤ a ∧ a < b.toNat + hi)

theorem keeps_rangeH {L : Layout} {b : Word} (hb : b.toNat + L.size < 2 ^ 64) {lo hi : Nat}
    {m m' : Memory} (h : Keeps (ImgH L b lo hi) m m') {off len : Nat} (hr : off + len ≤ L.size)
    (hav : off + len ≤ lo ∨ hi ≤ off) {acc : Access} :
    m'.readWith acc (b + BitVec.ofNat 64 off).toNat len =
      m.readWith acc (b + BitVec.ofNat 64 off).toNat len := by
  rw [addr_toNat (by omega)]
  exact h.readWith (fun k hk => ⟨⟨by omega, by omega⟩, by rintro ⟨h1, h2⟩; omega⟩)

theorem keeps_loadedH {L : Layout} {b : Word} (hb : b.toNat + L.size < 2 ^ 64) {lo hi : Nat}
    {m m' : Memory} (h : Keeps (ImgH L b lo hi) m m') {off : Nat} {code : List Byte}
    (hr : off + code.length ≤ L.size) (hav : off + code.length ≤ lo ∨ hi ≤ off)
    (hl : Loaded m (b + BitVec.ofNat 64 off) code) : Loaded m' (b + BitVec.ofNat 64 off) code := by
  unfold Loaded Memory.fetchBytes at hl ⊢
  rw [keeps_rangeH hb h hr hav]; exact hl

theorem keeps_loadNH {L : Layout} {b : Word} (hb : b.toNat + L.size < 2 ^ 64) {lo hi : Nat}
    {m m' : Memory} (h : Keeps (ImgH L b lo hi) m m') {off : Nat} (hr : off + 8 ≤ L.size)
    (hav : off + 8 ≤ lo ∨ hi ≤ off) :
    loadN m' (b + BitVec.ofNat 64 off) 8 = loadN m (b + BitVec.ofNat 64 off) 8 := by
  simp only [loadN, Memory.readBytes]
  rw [keeps_rangeH hb h hr hav]

/-- Every range the runtime's image facts read avoids `[lo, hi)`. -/
def _root_.Silmaril.Elf.Link.Dyn.Crt.Layout.avoids (L : Layout) (lo hi : Nat) : Bool :=
  [(L.init, L.cInit.length), (L.start, L.cStart.length), (L.dereg, L.cDereg.length),
   (L.reg, L.cReg.length), (L.dtors, L.cDtors.length), (L.fdummy, L.cFdummy.length),
   (L.fini, L.cFini.length), (L.plt, L.cPlt.length), (L.main, L.cMain.length),
   (L.ro, L.cRo.length), (L.gotLsm, 8), (L.gotDereg, 8), (L.gotGmon, 8), (L.gotReg, 8),
   (L.gotCxa, 8), (L.dso, 8), (L.cmpl, 1)].all fun e => decide (e.1 + e.2 ≤ lo ∨ hi ≤ e.1)

/-- **The runtime's image facts survive a step that keeps the image except a range they do
not read.** -/
theorem _root_.Silmaril.Elf.Link.Dyn.Crt.CrtMem.keepH {L : Layout} (F : L.Facts) {b lsmA cxaA : Word} {cv : Byte}
    (hb : b.toNat + L.size < 2 ^ 64) {lo hi : Nat} (hav : L.avoids lo hi = true) {m m' : Memory}
    (hm : CrtMem L b lsmA cxaA cv m) (h : Keeps (ImgH L b lo hi) m m') :
    CrtMem L b lsmA cxaA cv m' := by
  simp only [Layout.avoids, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hav
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hav
  exact {
    init := keeps_loadedH hb h (by rw [F.nInit]; exact F.bInit) a1 hm.init
    start := keeps_loadedH hb h (by rw [F.nStart]; exact F.bStart) a2 hm.start
    dereg := keeps_loadedH hb h (by rw [F.nDereg]; exact F.bDereg) a3 hm.dereg
    reg := keeps_loadedH hb h (by rw [F.nReg]; exact F.bReg) a4 hm.reg
    dtors := keeps_loadedH hb h (by rw [F.nDtors]; exact F.bDtors) a5 hm.dtors
    fdummy := keeps_loadedH hb h (by rw [F.nFdummy]; exact F.bFdummy) a6 hm.fdummy
    fini := keeps_loadedH hb h (by rw [F.nFini]; exact F.bFini) a7 hm.fini
    plt := keeps_loadedH hb h (by rw [F.nPlt]; have := F.bPlt; omega) a8 hm.plt
    main := keeps_loadedH hb h F.bMain a9 hm.main
    rodata := by
      have hd := hm.rodata
      unfold Memory.readBytes at hd ⊢
      rw [keeps_rangeH hb h F.bRo a10]; exact hd
    lsm := (keeps_loadNH hb h F.bLsm a11).trans hm.lsm
    gDereg := (keeps_loadNH hb h F.bDereg' a12).trans hm.gDereg
    gGmon := (keeps_loadNH hb h F.bGmon a13).trans hm.gGmon
    gReg := (keeps_loadNH hb h F.bReg' a14).trans hm.gReg
    cxa := (keeps_loadNH hb h F.bCxa a15).trans hm.cxa
    dso := (keeps_loadNH hb h F.bDso a16).trans hm.dso
    done := by
      have hd := hm.done
      unfold Memory.readBytes at hd ⊢
      rw [keeps_rangeH hb h F.bTmc a17]; exact hd
    wDone := by
      have hw := hm.wDone
      rw [addr_toNat (by have := F.bTmc; omega)] at hw ⊢
      exact Keeps.permitted h (fun k hk => ⟨⟨by omega, by have := F.bTmc; omega⟩,
        by rintro ⟨h1, h2⟩; omega⟩) hw }

theorem adderClang_avoids : adderClangLayout.avoids 0x4000 0x4010 = true := by decide +kernel

theorem Keeps.imgH {L : Layout} {b : Word} {lo hi : Nat} {m m' : Memory}
    (h : Keeps (Img L b) m m') : Keeps (ImgH L b lo hi) m m' := Keeps.mono h fun _ h => h.1

/-- The PLT facts with only `scanf`'s slot written. -/
theorem Plt0.keepH {b res : Word} (hb : b.toNat + adderClangLayout.size < 2 ^ 64) {m m' : Memory}
    (hp : Plt0 b res m) (h : Keeps (ImgH adderClangLayout b 0x4008 0x4010) m m') : Plt0 b res m' where
  code := fun c hc => by
    have hall : ∀ c ∈ adderClangPltL, c.1 + c.2.length ≤ adderClangLayout.size ∧
        (c.1 + c.2.length ≤ 0x4008 ∨ 0x4010 ≤ c.1) := by decide +kernel
    exact keeps_loadedH hb h (hall c hc).1 (hall c hc).2 (hp.code c hc)
  got1 := by
    obtain ⟨w, hw⟩ := hp.got1
    exact ⟨w, (keeps_loadNH (off := 0x3ff0) hb h (by decide) (by decide)).trans hw⟩
  got2 := (keeps_loadNH (off := 0x3ff8) hb h (by decide) (by decide)).trans hp.got2
  slot0 := (keeps_loadNH (off := 0x4000) hb h (by decide) (by decide)).trans hp.slot0
  rw0 := by
    have hA : (b + 0x4000#64).toNat = b.toNat + 0x4000 := addr_toNat (by simp [adderClangLayout] at hb; omega)
    rw [hA]
    exact ⟨Keeps.permitted h (fun k hk => ⟨⟨by omega, by simp [adderClangLayout]; omega⟩,
      by rintro ⟨h1, h2⟩; omega⟩) (by have := hp.rw0.1; rwa [hA] at this),
      Keeps.permitted h (fun k hk => ⟨⟨by omega, by simp [adderClangLayout]; omega⟩,
      by rintro ⟨h1, h2⟩; omega⟩) (by have := hp.rw0.2; rwa [hA] at this)⟩

theorem PltL.keep {b res : Word} (hb : b.toNat + adderClangLayout.size < 2 ^ 64) {m m' : Memory}
    (hp : PltL b res m) (h : Keeps (Img adderClangLayout b) m m') : PltL b res m' :=
  { Plt0.keepH hb hp.toPlt0 (Keeps.imgH h) with
    slot1 := (keeps_loadN (off := 0x4008) hb h (by decide)).trans hp.slot1
    rw1 := by
      have hA : (b + 0x4008#64).toNat = b.toNat + 0x4008 := addr_toNat (by simp [adderClangLayout] at hb; omega)
      have r1 := hp.rw1
      rw [hA] at r1 ⊢
      exact ⟨Keeps.permitted h (fun k hk => ⟨by omega, by simp [adderClangLayout]; omega⟩) r1.1,
        Keeps.permitted h (fun k hk => ⟨by omega, by simp [adderClangLayout]; omega⟩) r1.2⟩ }

/-! ## The resolver for slot `j` -/

theorem must_resolveJ {W : World} {Q : PState → Prop} {s : PState} (hd : s.g.done = none)
    (hout : ¬ W.InImage s.m.core.rip.toNat) (hg : s.m.core.rip ≠ W.gate) {res : Word}
    {sl : List (Nat × Word)} (hl : W.lazy = some (res, sl)) (hrip : s.m.core.rip = res)
    (hsl : sl.length ≤ 2 ^ 64) {j : Nat} {e : Nat × Word} (he : sl[j]? = some e)
    (hj : loadN s.m.memory (s.m.core.read .rsp + 8#64) 8 = some (BitVec.ofNat 64 j))
    (hpre : SlotRW W e s) (k : ∀ t, ResPost W e s t → MustQ W Q t) : MustQ W Q s := by
  refine must_contract hd hout (pre := SlotRW W e s) (post := ResPost W e s) (fun r => ?_) hpre k
  rw [extStep_res hg hl hrip]
  constructor
  · intro h; exact h j hj e he
  · intro h j' hj' e' he'
    have hjl : j < sl.length := (List.getElem?_eq_some_iff.mp he).1
    have hjl' : j' < sl.length := (List.getElem?_eq_some_iff.mp he').1
    have hjj : j' = j := by
      rw [hj, Option.some.injEq] at hj'
      have := congrArg BitVec.toNat hj'
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      omega
    subst hjj
    rw [he, Option.some.injEq] at he'
    subst he'
    exact h

end Silmaril.Elf.Link.Dyn.Small
