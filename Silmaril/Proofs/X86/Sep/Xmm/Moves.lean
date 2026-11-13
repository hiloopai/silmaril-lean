module

public import Silmaril.Proofs.X86.Sep.Xmm.Lift
public import Silmaril.X86.Sep.Thms
/-!
# Proofs: triples for the `Sse9` register moves

Behind `Silmaril/Machine/X86/Sep/Xmm/Thms.lean`.

* `XSTriple.of_step_local`: a triple from one step that changes nothing outside the
  precondition's fragment (the XMM analogue of `Sep.Triple.of_local`).
* `xstriple_xwrite`: **the generic rule for an SSE form that advances RIP and writes one XMM
  register**, with read-only integer resources `G` and read-only XMM resources `X`: from
  `rip ↦ pc ∗ code ∗ G`, `X` and `xmmAny d` to `rip ↦ pc + len ∗ code ∗ G`, `X` and
  `xmm d ↦ v`, provided the instruction, decoded from the code bytes by `Sse9.decodeL`,
  executes to that write whenever `G` and `X` are contained in the state.
* Instances: `pxor x, x` and `xorps x, x` (zeroing), `movups`/`movaps`/`movdqu`/`movdqa
  xmm, xmm`, `movq xmm, r64` (`66 REX.W 0F 6E`), `movq xmm, xmm` (`F3 0F 7E`), and the
  unaligned 128-bit loads `movups`/`movdqu xmm, [base + disp]`.
-/

@[expose] public section

namespace Silmaril.X86.Sep.Xmm

open Silmaril.X86 (State MState Word Byte Reg XReg)
open Silmaril.Machine (RegisterFile)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86.Sse9 (XState XFile Xmm Instr XRM Move exec decodeL)
open Silmaril.X86.Sep

/-! ## Partial-map helpers -/

namespace PMap

variable {α β : Type}

theorem reval_eq_of_agree {f s s' : PMap α β} (hl : Le f s)
    (agree : ∀ a, (f a).isSome → s' a = s a) : reval f s' = f := by
  funext a
  simp only [reval]
  cases e : f a with
  | none => rfl
  | some v => simp [agree a (by simp [e]), hl a v e]

/-- A piece that does not own `a₀` keeps its values when only `a₀` changes. -/
theorem reval_eq_of_none {f s s' : PMap α β} {a₀ : α} (hl : Le f s) (h₀ : f a₀ = none)
    (agree : ∀ a, a ≠ a₀ → s' a = s a) : reval f s' = f :=
  reval_eq_of_agree hl fun a ha => agree a fun e => by subst e; simp [h₀] at ha

theorem none_of_disjoint {f g : PMap α β} (hd : Disjoint f g) {a : α} {v : β}
    (h : f a = some v) : g a = none := by
  rcases hd a with e | e
  · simp [h] at e
  · exact e

theorem disjoint_reval_left {f g s : PMap α β} (hd : Disjoint f g) : Disjoint (reval f s) g := by
  intro a
  rcases hd a with e | e
  · left; simp [reval, e]
  · right; exact e

theorem eq_union_reval {f g s s' : PMap α β} (he : s = union f g) (htot : ∀ a, (s' a).isSome)
    (hsame : ∀ a, f a = none → s' a = s a) : s' = union (reval f s') g := by
  funext a
  cases e : f a with
  | none =>
    rw [union_of_none (by simp [reval, e]), hsame a e, he, union_of_none e]
  | some v =>
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (htot a)
    rw [union_of_some (v := w) (by simp [reval, e, hw]), hw]

end PMap

theorem frag_single (l : Loc) (v : Val) : Frag.single l v = PMap.single l v := rfl

theorem toFrag_isSome' (m : MState) (l : Loc) : (toFrag m l).isSome := by
  cases l <;> rfl

/-- Setting `rip` changes only the `rip` location. -/
theorem toFrag_setRip (m : MState) (r : Word) {l : Loc} (hl : l ≠ .rip) :
    toFrag ⟨{ m.core with rip := r }, m.memory⟩ l = toFrag m l := by
  cases l with
  | rip => exact absurd rfl hl
  | _ => rfl

/-! ## Triples from one local step -/

/-- **A triple from one step** that changes nothing outside the precondition's fragment. -/
theorem XSTriple.of_step_local {M : Silmaril.X86.SegVC.Isa XState} {P Q : XSProp}
    (h : ∀ x h₁, P h₁ → XFrag.Le h₁ (toXFrag x) →
      ∃ x', M.step x = some x' ∧ Q (XFrag.reval h₁ (toXFrag x')) ∧
        (∀ l, h₁.1 l = none → toFrag x'.m l = toFrag x.m l) ∧
        (∀ r, h₁.2 r = none → x'.xmm r = x.xmm r))
    (n : Nat) : XSTriple M n P Q := by
  intro F x ⟨h₁, h₂, hd, he, hp, hf⟩
  have hl : XFrag.Le h₁ (toXFrag x) := by rw [he]; exact XFrag.le_union_left h₁ h₂
  obtain ⟨x', hs, hq, hsame₁, hsame₂⟩ := h x h₁ hp hl
  refine xsafeN_of_step hs ?_ n
  refine ⟨XFrag.reval h₁ (toXFrag x'), h₂,
    ⟨PMap.disjoint_reval_left hd.1, PMap.disjoint_reval_left hd.2⟩, ?_, hq, hf⟩
  exact Prod.ext
    (PMap.eq_union_reval (congrArg Prod.fst he) (toFrag_isSome' x'.m) hsame₁)
    (PMap.eq_union_reval (congrArg Prod.snd he) (fun _ => rfl)
      fun r hr => by simp [toXFrag, XMap.all, hsame₂ r hr])

/-! ## The generic XMM-write rule -/

/-- **An SSE form that advances RIP and writes the XMM register `d`.** -/
theorem xstriple_xwrite {pc : Word} {c : List Byte} {i : Sse9.Instr} {d : XReg} {v : Sse9.Xmm}
    {G : SProp} {X : XSProp} (hc : c ≠ []) (hdec : decodeL c = some (i, c.length))
    (hx : ∀ (x : XState) (g : Frag) (xh : XFrag), x.m.core.rip = pc → G g →
      Frag.Le g (toFrag x.m) → X xh → XFrag.Le xh (toXFrag x) →
      exec i x.m.core x.xmm x.m.memory (pc + BitVec.ofNat 64 c.length) =
        .ok { x.m.core with rip := pc + BitVec.ofNat 64 c.length }
          (RegisterFile.write x.xmm d v) x.m.memory)
    (n : Nat) :
    XSTriple Silmaril.X86.Sse9.isa n
      (lift (ripPt pc ∗ codePt pc.toNat c ∗ G) ∗ₓ X ∗ₓ xmmAny d)
      (lift (ripPt (pc + BitVec.ofNat 64 c.length) ∗ codePt pc.toNat c ∗ G) ∗ₓ X ∗ₓ
        xmmPt d v) := by
  apply XSTriple.of_step_local
  intro x h₁ hp hl
  obtain ⟨A, B, hA, hB, hlA, hlB, hdAB, rfl⟩ := xsep_le hp hl
  obtain ⟨XH, D, hXH, hD, hlXH, -, hdXD, rfl⟩ := xsep_le hB hlB
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨u, hD1, hD2⟩ := hD
  obtain ⟨rp, rest, hrp, hrest, hlrp, hlrest, hdr, hAe⟩ := sep_le hA1 hlA.1
  obtain ⟨cp, g, hcp, hg, hlcp, hlg, hdcg, hreste⟩ := sep_le hrest hlrest
  have hrip : x.m.core.rip = pc := ripPt_le hrp hlrp
  subst hrip
  have hfetch := fetchBytes_of_codePt hc hcp hlcp
  have hexec := hx x g XH rfl hg hlg hXH hlXH
  have hs := Silmaril.X86.Sse9.step_of_fetch_sse hfetch hdec hexec
  -- the new state, and what changed
  let x' : XState := ⟨⟨{ x.m.core with rip := x.m.core.rip + BitVec.ofNat 64 c.length },
    x.m.memory⟩, RegisterFile.write x.xmm d v⟩
  have agree₁ : ∀ l, l ≠ .rip → (toXFrag x').1 l = (toXFrag x).1 l :=
    fun l hl => toFrag_setRip x.m _ hl
  have agree₂ : ∀ r, r ≠ d → (toXFrag x').2 r = (toXFrag x).2 r := fun r hr => by
    simp [toXFrag, XMap.all, x', RegisterFile.write_other _ _ _ _ hr]
  -- domain facts
  have hrp_rip : rp .rip = some (.word x.m.core.rip) := by rw [hrp]; simp [Frag.single]
  have hrest_rip : rest .rip = none := PMap.none_of_disjoint hdr hrp_rip
  rw [hreste, frag_union, PMap.union_eq_none] at hrest_rip
  have hA_rip : A.1 .rip = some (.word x.m.core.rip) := by
    rw [hAe, frag_union]; exact PMap.union_of_some hrp_rip
  have hB_rip : (XFrag.union XH D).1 .rip = none := PMap.none_of_disjoint hdAB.1 hA_rip
  have hD_d : D.2 d = some u := by rw [hD2]; exact PMap.single_apply_self d u
  have hXH_d : XH.2 d = none := PMap.none_of_disjoint hdXD.2.symm hD_d
  have hXH_rip : XH.1 .rip = none := (PMap.union_eq_none.mp hB_rip).1
  refine ⟨x', hs, ?_, ?_, ?_⟩
  · -- the postcondition on the re-valued fragment
    refine ⟨XFrag.reval A (toXFrag x'), XFrag.reval (XFrag.union XH D) (toXFrag x'),
      XFrag.reval_disjoint hdAB _, XFrag.reval_union _ _ _, ⟨?_, ?_⟩,
      XFrag.reval XH (toXFrag x'), XFrag.reval D (toXFrag x'), XFrag.reval_disjoint hdXD _,
      XFrag.reval_union _ _ _, ?_, ?_⟩
    · -- integer part
      show (ripPt _ ∗ codePt _ c ∗ G) (PMap.reval A.1 (toXFrag x').1)
      rw [hAe, frag_union, PMap.reval_union]
      refine ⟨_, _, PMap.reval_disjoint hdr _, (frag_union _ _).symm, ?_, ?_⟩
      · show PMap.reval rp (toXFrag x').1 = Frag.single .rip (.word _)
        rw [hrp, frag_single, PMap.reval_single (s := (toXFrag x').1) _ _
          (.word (x.m.core.rip + BitVec.ofNat 64 c.length)) rfl]
        rfl
      · rw [hreste, frag_union, PMap.reval_union]
        rw [PMap.reval_eq_of_none hlcp hrest_rip.1 agree₁,
          PMap.reval_eq_of_none hlg hrest_rip.2 agree₁]
        exact ⟨cp, g, hdcg, (frag_union _ _).symm, hcp, hg⟩
    · show PMap.reval A.2 (toXFrag x').2 = PMap.empty
      rw [hA2, PMap.reval_empty]
    · -- the read-only XMM resources
      have e : XFrag.reval XH (toXFrag x') = XH :=
        Prod.ext (PMap.reval_eq_of_none hlXH.1 hXH_rip agree₁)
          (PMap.reval_eq_of_none hlXH.2 hXH_d agree₂)
      rw [e]; exact hXH
    · -- the written register
      refine ⟨?_, ?_⟩
      · show PMap.reval D.1 (toXFrag x').1 = Frag.empty
        rw [hD1, frag_empty, PMap.reval_empty]
      · show PMap.reval D.2 (toXFrag x').2 = PMap.single d v
        rw [hD2, PMap.reval_single (s := (toXFrag x').2) _ _ v (by simp [toXFrag, XMap.all, x'])]
  · intro l hl
    by_cases e : l = .rip
    · subst e
      have : (XFrag.union A (XFrag.union XH D)).1 .rip = some (.word x.m.core.rip) :=
        PMap.union_of_some hA_rip
      rw [this] at hl; cases hl
    · exact agree₁ l e
  · intro r hr
    by_cases e : r = d
    · subst e
      have : (XFrag.union A (XFrag.union XH D)).2 r = some u := by
        show PMap.union A.2 (PMap.union XH.2 D.2) r = some u
        rw [hA2, PMap.empty_union, PMap.union_of_none hXH_d, hD_d]
      rw [this] at hr; cases hr
    · simp [x', RegisterFile.write_other _ _ _ _ e]

/-! ## Reading XMM atoms off the machine -/

theorem xmmPt_le {r : XReg} {w : Sse9.Xmm} {h : XFrag} {x : XState} (hp : xmmPt r w h)
    (hl : XFrag.Le h (toXFrag x)) : x.xmm r = w := by
  have e := hl.2 r w (by rw [hp.2]; exact PMap.single_apply_self r w)
  simpa [toXFrag, XMap.all] using e

/-- An integer assertion that holds of a machine state, with one XMM register beside it. -/
theorem xholds_lift_xmmPt {P : SProp} {m : MState} (xs : XFile) (r : XReg) (hp : Holds P m) :
    XHolds (lift P ∗ₓ xmmPt r (xs r)) ⟨m, xs⟩ := by
  obtain ⟨h, hp, hl⟩ := hp
  refine ⟨XFrag.union (h, PMap.empty) (PMap.empty, PMap.single r (xs r)),
    ⟨_, _, ⟨PMap.disjoint_empty_right h, PMap.disjoint_empty_left _⟩, rfl, ⟨hp, rfl⟩,
      ⟨frag_empty, rfl⟩⟩, ?_⟩
  refine ⟨?_, ?_⟩
  · show PMap.Le (PMap.union h PMap.empty) (toFrag m)
    rw [PMap.union_empty]; exact hl
  · intro r' v e
    show some (xs r') = some v
    simp only [XFrag.union, PMap.empty_union, PMap.single] at e
    split at e
    · subst_vars; cases e; rfl
    · cases e

/-! ## Instances of the rule -/

open Silmaril.X86.Sse9 (exec_pxor_self exec_xorps_self)

variable {pc : Word} {c : List Byte} {d : XReg} (n : Nat)

/-- **`pxor xmm, xmm`** (the zeroing idiom) writes `0`. -/
theorem xstriple_pxor_self (hc : c ≠ []) (hdec : decodeL c = some (.pxor d (.reg d), c.length)) :
    XSTriple Silmaril.X86.Sse9.isa n
      (lift (ripPt pc ∗ codePt pc.toNat c) ∗ₓ xmmAny d)
      (lift (ripPt (pc + BitVec.ofNat 64 c.length) ∗ codePt pc.toNat c) ∗ₓ xmmPt d 0) := by
  have h := xstriple_xwrite (pc := pc) (d := d) (G := emp) (X := xemp) (v := 0) hc hdec
    (fun x _ _ _ _ _ _ _ => exec_pxor_self d x.m.core x.xmm x.m.memory _) n
  rwa [sep_emp, xemp_sep, xemp_sep] at h

/-- **`xorps xmm, xmm`** writes `0`. -/
theorem xstriple_xorps_self (hc : c ≠ []) (hdec : decodeL c = some (.xorps d (.reg d), c.length)) :
    XSTriple Silmaril.X86.Sse9.isa n
      (lift (ripPt pc ∗ codePt pc.toNat c) ∗ₓ xmmAny d)
      (lift (ripPt (pc + BitVec.ofNat 64 c.length) ∗ codePt pc.toNat c) ∗ₓ xmmPt d 0) := by
  have h := xstriple_xwrite (pc := pc) (d := d) (G := emp) (X := xemp) (v := 0) hc hdec
    (fun x _ _ _ _ _ _ _ => exec_xorps_self d x.m.core x.xmm x.m.memory _) n
  rwa [sep_emp, xemp_sep, xemp_sep] at h

/-- **`movups`/`movaps`/`movdqu`/`movdqa xmm, xmm`** (load form `0F 10`/`0F 28`/`F3 0F 6F`/
`66 0F 6F`) copies the source register. -/
theorem xstriple_load_reg (k : Move) {s : XReg} {w : Sse9.Xmm} (hc : c ≠ [])
    (hdec : decodeL c = some (.load k d (.reg s), c.length)) :
    XSTriple Silmaril.X86.Sse9.isa n
      (lift (ripPt pc ∗ codePt pc.toNat c) ∗ₓ xmmPt s w ∗ₓ xmmAny d)
      (lift (ripPt (pc + BitVec.ofNat 64 c.length) ∗ codePt pc.toNat c) ∗ₓ xmmPt s w ∗ₓ
        xmmPt d w) := by
  have h := xstriple_xwrite (pc := pc) (d := d) (G := emp) (X := xmmPt s w) (v := w) hc hdec
    (fun x _ xh _ _ _ hX hlX => by
      simp [exec, Silmaril.X86.Sse9.misaligned, Silmaril.X86.Sse9.readX,
        xmmPt_le hX hlX]) n
  rwa [sep_emp] at h

/-- **`movq xmm, xmm`** (`F3 0F 7E`) copies the low quadword and zeroes the upper one. -/
theorem xstriple_movqLoad_reg {s : XReg} {w : Sse9.Xmm} (hc : c ≠ [])
    (hdec : decodeL c = some (.movqLoad d (.reg s), c.length)) :
    XSTriple Silmaril.X86.Sse9.isa n
      (lift (ripPt pc ∗ codePt pc.toNat c) ∗ₓ xmmPt s w ∗ₓ xmmAny d)
      (lift (ripPt (pc + BitVec.ofNat 64 c.length) ∗ codePt pc.toNat c) ∗ₓ xmmPt s w ∗ₓ
        xmmPt d ((w.setWidth 64).setWidth 128)) := by
  have h := xstriple_xwrite (pc := pc) (d := d) (G := emp) (X := xmmPt s w) (v := (w.setWidth 64).setWidth 128)
    hc hdec (fun x _ xh _ _ _ hX hlX => by simp [exec, xmmPt_le hX hlX]) n
  rwa [sep_emp] at h

/-- **`movd xmm, r32` / `movq xmm, r64`** (`66 REX.W? 0F 6E`) zero-extends the register. -/
theorem xstriple_movToX_reg (sz : Silmaril.X86.Ext.Sz) {r : Reg} {a : Word} (hc : c ≠ [])
    (hdec : decodeL c = some (.movToX sz d (.reg r), c.length)) :
    XSTriple Silmaril.X86.Sse9.isa n
      (lift (ripPt pc ∗ codePt pc.toNat c ∗ regPt r a) ∗ₓ xemp ∗ₓ xmmAny d)
      (lift (ripPt (pc + BitVec.ofNat 64 c.length) ∗ codePt pc.toNat c ∗ regPt r a) ∗ₓ xemp ∗ₓ
        xmmPt d ((a.setWidth sz.bits).setWidth 128)) :=
  xstriple_xwrite hc hdec (fun x g _ _ hg hlg _ _ => by
    simp [exec, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.Sz.read, regPt_le hg hlg]) n

/-- **`movups`/`movdqu xmm, [base + disp]`**: an unaligned 128-bit load of sixteen readable
bytes, little-endian. -/
theorem xstriple_load_mem (k : Move) (hk : k.aligned = false) {b : Reg} {a : Word}
    {disp : BitVec 32} {bs : List Byte} (hlen : bs.length = 16) (hc : c ≠ [])
    (hdec : decodeL c = some
      (.load k d (.mem (Silmaril.X86.Ext.Mem.ofReg b none disp)), c.length)) :
    XSTriple Silmaril.X86.Sse9.isa n
      (lift (ripPt pc ∗ codePt pc.toNat c ∗ regPt b a ∗
        bytesPtRO (a + disp.signExtend 64).toNat bs) ∗ₓ xemp ∗ₓ xmmAny d)
      (lift (ripPt (pc + BitVec.ofNat 64 c.length) ∗ codePt pc.toNat c ∗ regPt b a ∗
        bytesPtRO (a + disp.signExtend 64).toNat bs) ∗ₓ xemp ∗ₓ
        xmmPt d (BitVec.ofNat 128 (Silmaril.X86.Ext.leValue bs))) :=
  xstriple_xwrite hc hdec (fun x g _ _ hg hlg _ _ => by
    obtain ⟨g₁, g₂, hg₁, hg₂, hl₁, hl₂, -, -⟩ := sep_le hg hlg
    have hb := regPt_le hg₁ hl₁
    have hne : bs ≠ [] := by intro e; simp [e] at hlen
    have hr := readBytes_of_bytesPtRO hne hg₂ hl₂
    rw [hlen] at hr
    have haddr : ∀ next, (Silmaril.X86.Ext.Mem.ofReg b none disp).addr x.m.core next =
        a + disp.signExtend 64 := fun next => by
      simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, hb]
    simp only [exec, hk, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      Silmaril.X86.Sse9.readX, Silmaril.X86.Sse9.load128, haddr, hr, Option.map_some]) n

end Silmaril.X86.Sep.Xmm
