module

public import Silmaril.Machine.Abi.CSpecFfi.Defs
public import Silmaril.X86.Sep.CSpec.Thms
public import Silmaril.X86.Sep.Plan.Thms
public import Silmaril.X86.Safe.Open9.Thms
public import Silmaril.Machine.Abi.CtypeBridge.Thms
/-!
# Proofs: `CSpec` → FFI export (CP-12)

Behind `Silmaril/Machine/Abi/CSpecFfi/Thms.lean`; imports only headers.

* Total triples: `XTriple.xsafeN`, `SatT.sat`, `XTriple.frame`, `XTriple.conseq`,
  `xtriple_of_triple`, `satT_toC_of_sat`.
* C types: `ofCtypes_plan_ok`, `ofCtypes_proto`, `ofScalarFn_shape`, `ofScalarFn_sub_toC`,
  `toC_sub_ofScalarFn`.
* FFI: `ffiXState_withX`, `exists_compl`, `resultAt_of_retPt`, `realizes_of_satT`,
  `ofSignature_realizes`.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.CSpecFfi

open Silmaril.X86 (Reg XReg Word Byte MState)
open Silmaril.C.Api (Scalar)
open Silmaril.Cerberus.Mem.Concrete (Tags)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86.Sse9 (XState)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Xmm
open Silmaril.X86.Sep.Plan
open Silmaril.X86.Sep.CSpec
open Silmaril.Machine.SystemV.Abi (Object Profile CallPlan objectOfCtype)
open Silmaril.Machine.Abi.CtypeBridge (Scalar.toCtype Proto.ctypes Proto.resultCtype sigOf)
open Silmaril.Machine.Abi.CSpecFfi (withX xExecute setLow128)
open Silmaril.Machine.Abi.CallFootprint (FfiRealizesCall)

/-! ## Total triples -/

theorem xentails_of_eq' {P Q : XSProp} (e : P = Q) : P ⊢ₓ Q := e ▸ xentails_refl P

section Total

variable {M : Silmaril.X86.SegVC.Isa XState}

theorem XTriple.xsafeN {P Q : XSProp} (h : XTriple M P Q) (n : Nat) :
    XSTriple M n P Q := by
  intro F x hx
  obtain ⟨x', hr, hq⟩ := h F x hx
  exact xsafeN_of_reaches hr hq n

/-- **Total satisfaction gives partial satisfaction.** -/
theorem SatT.sat {C : XSProp} {entry : Word} {S : CSpec} (h : S.SatT M C entry) :
    S.Sat M C entry :=
  fun n x fr ha hs => XTriple.xsafeN (h x fr ha hs) n

theorem XTriple.frame {P Q : XSProp} (h : XTriple M P Q) (R : XSProp) :
    XTriple M (P ∗ₓ R) (Q ∗ₓ R) := by
  intro F x hx
  rw [xsep_assoc] at hx
  obtain ⟨x', hr, hq⟩ := h (R ∗ₓ F) x hx
  exact ⟨x', hr, by rw [xsep_assoc]; exact hq⟩

theorem XTriple.conseq {P P' Q Q' : XSProp} (hp : P' ⊢ₓ P) (h : XTriple M P Q)
    (hq : Q ⊢ₓ Q') : XTriple M P' Q' := by
  intro F x hx
  obtain ⟨x', hr, hq'⟩ := h F x (xsep_mono hp (xentails_refl F) _ hx)
  exact ⟨x', hr, xsep_mono hq (xentails_refl F) _ hq'⟩

/-- **Track A's total triples are total triples of every XMM machine extending `Open9`.** -/
theorem xtriple_of_triple [ExtendsOpen9X M] {P Q : SProp}
    (h : Triple Silmaril.X86.Open.isa P Q) :
    XTriple M (lift P) (lift Q) := by
  intro F x hx
  obtain ⟨a, b, hd, he, ⟨ha, ha2⟩, hb⟩ := hx
  have hb2 : b.2 = XMap.all x.xmm := by
    have e := congrArg Prod.snd he
    simp only [toXFrag, XFrag.union, ha2, PMap.empty_union] at e
    exact e.symm
  let F' : SProp := fun g => F (g, XMap.all x.xmm)
  have hpre : (P ∗ F') (toFrag x.m) := by
    refine ⟨a.1, b.1, hd.1, (congrArg Prod.fst he).trans (frag_union a.1 b.1).symm, ha, ?_⟩
    show F (b.1, XMap.all x.xmm)
    rw [← hb2]
    exact hb
  obtain ⟨m', hr, ⟨c, d, hcd, hce, hc, hd'⟩⟩ := h F' x.m trivial hpre
  have hr9 : Reaches Silmaril.X86.Open9.step x.m m' :=
    Silmaril.X86.Open9.reaches_of_open hr
  refine ⟨⟨m', x.xmm⟩, reaches_of_open9X (M := M) x.xmm hr9, ?_⟩
  refine ⟨(c, PMap.empty), (d, XMap.all x.xmm), ⟨hcd, PMap.disjoint_empty_left _⟩, ?_,
    ⟨hc, rfl⟩, hd'⟩
  refine Prod.ext (hce.trans (frag_union c d)) ?_
  show XMap.all x.xmm = PMap.union PMap.empty (XMap.all x.xmm)
  rw [PMap.empty_union]

/-- **Every `FnSpec` proof is a total `CSpec` proof** on every XMM machine extending `Open9`
(the total form of CP-10b's `sat_toC_of_sat`). -/
theorem satT_toC_of_sat [ExtendsOpen9X M] {S : FnSpec} {C : SProp} {entry : Word}
    (hS : S.Sat Silmaril.X86.Open.isa C entry) : S.toC.SatT M ↑ₓC entry := by
  intro x fr hA hst
  have h := XTriple.frame (xtriple_of_triple (M := M) (hS x fr.sp fr.ret hA hst))
    (xmmsAny allXRegs)
  refine XTriple.conseq ?_ h ?_
  · rw [toC_pre S x entry fr, lift_sep]
    exact xentails_of_eq' (by ac_rfl)
  · rw [lift_sep, xsep_assoc]
    exact xsep_mono (xentails_refl _) (toC_post S x fr)

end Total

/-! ## Specs from C types -/

theorem ofCtypes_plan_ok {profile : Profile} {tags : Tags} {Arg : Type} {args res named variadic
    bytes sret stack pre post} (x : Arg) {os : List Object} {ro : Option Object}
    (hos : (args x).mapM (objectOfCtype tags) = .ok os)
    (hro : (res x).mapM (objectOfCtype tags) = .ok ro) :
    ((ofCtypes profile tags Arg args res named variadic bytes sret stack pre post).shape x).plan =
      planOr (Silmaril.Machine.SystemV.Abi.plan profile os ro named variadic) := by
  simp only [ofCtypes, ofPlan, hos, hro, objectsOr, resultOr]

/-- **`ofCtypes` on a fragment prototype has the convention's plan**: the `callPlan` of the
typed FFI signature `sigOf profile p`. -/
theorem ofCtypes_proto (profile : Profile) (tags : Tags) (p : Silmaril.Machine.Abi.SystemV.Proto) {Arg : Type}
    {bytes sret stack pre post} (x : Arg) :
    ((ofCtypes profile tags Arg (fun _ => Proto.ctypes p) (fun _ => Proto.resultCtype p)
      (Proto.ctypes p).length false bytes sret stack pre post).shape x).plan =
      (sigOf profile p).callPlan := by
  have hc := Silmaril.Machine.Abi.CtypeBridge.ctypePlan_eq_callPlan profile tags p
  have hos := Silmaril.Machine.Abi.CtypeBridge.mapM_toCtype tags p.signature.arguments
  have hro := Silmaril.Machine.Abi.CtypeBridge.optionMapM_toCtype tags p.signature.result
  rw [ofCtypes_plan_ok x hos hro]
  simp only [Silmaril.Machine.Abi.CtypeBridge.ctypePlan, Proto.ctypes, Proto.resultCtype, hos, hro]
    at hc
  simp only [Proto.ctypes, List.length_map]
  have hc' : Silmaril.Machine.SystemV.Abi.plan profile
      (p.signature.arguments.map Silmaril.Machine.Abi.SystemV.Kind.object)
      (p.signature.result.map Silmaril.Machine.Abi.SystemV.Kind.object) p.signature.arguments.length false =
      .ok (sigOf profile p).callPlan := by
    simpa [bind, Except.bind, List.length_map] using hc
  rw [hc']
  rfl

theorem argRegs_length : argRegs.length = 6 := rfl

theorem wordBytes_length (w : Word) : (wordBytes w).length = 8 := by
  simp [wordBytes, byteSlice]

theorem forall₂_wordBytes : ∀ (ws : List Word) (os : List Object), ws.length = os.length →
    (∀ o ∈ os, o.size = 8) →
    List.Forall₂ (fun (b : List Byte) (o : Object) => b.length = o.size) (ws.map wordBytes) os
  | [], [], _, _ => .nil
  | w :: ws, o :: os, hl, ho => by
    refine .cons ?_ (forall₂_wordBytes ws os (by simpa using hl)
      (fun o' h => ho o' (List.mem_cons_of_mem _ h)))
    rw [wordBytes_length, ho o (List.mem_cons_self ..)]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem map_object_replicate {ks : List Scalar}
    (h64 : ∀ k ∈ ks, Silmaril.Machine.Abi.SystemV.Kind.object k = int64Object) :
    ks.map Silmaril.Machine.Abi.SystemV.Kind.object = List.replicate ks.length int64Object := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.map_cons, List.length_cons, List.replicate_succ]
    rw [h64 k (List.mem_cons_self ..), ih (fun k' h => h64 k' (List.mem_cons_of_mem _ h))]

theorem ok_of_toOption {α : Type} {e : Except String α} {a : α} (h : e.toOption = some a) :
    e = .ok a := by
  cases e with
  | error _ => cases h
  | ok b => cases h; rfl

theorem ofScalarFn_planOk (S : FnSpec) (ks : List Scalar) (r : Scalar)
    (h64 : ∀ k ∈ ks, Silmaril.Machine.Abi.SystemV.Kind.object k = int64Object)
    (hr : Silmaril.Machine.Abi.SystemV.Kind.object r = int64Object) (hks : ks.length ≤ 6)
    (hlen : ∀ x, (S.args x).length = ks.length) (x : S.Arg) :
    Silmaril.Machine.SystemV.Abi.plan {} (ks.map Silmaril.Machine.Abi.SystemV.Kind.object)
      (some (Silmaril.Machine.Abi.SystemV.Kind.object r)) ks.length false = .ok (intPlan (S.args x)) := by
  have h := intPlan_eq_plan (S.args x) (by rw [hlen x]; exact hks)
  rw [hlen x] at h
  rw [map_object_replicate h64, hr]
  exact ok_of_toOption h

section Scalar

variable (tags : Tags) (S : FnSpec) (ks : List Scalar) (r : Scalar)
  (h64 : ∀ k ∈ ks, Silmaril.Machine.Abi.SystemV.Kind.object k = int64Object)
  (hr : Silmaril.Machine.Abi.SystemV.Kind.object r = int64Object) (hks : ks.length ≤ 6)
  (hlen : ∀ x, (S.args x).length = ks.length)

include h64 hr hks hlen

/-- **`ofScalarFn` has `FnSpec.toC`'s shape.** -/
theorem ofScalarFn_shape (x : S.Arg) :
    (ofScalarFn tags S ks r).shape x = intShape (S.args x) := by
  have hos := Silmaril.Machine.Abi.CtypeBridge.mapM_toCtype tags ks
  have hro := Silmaril.Machine.Abi.CtypeBridge.optionMapM_toCtype tags (some r)
  simp only [Option.map_some] at hro
  simp only [ofScalarFn, ofCtypes, ofPlan, hos, hro, objectsOr, resultOr]
  rw [ofScalarFn_planOk S ks r h64 hr hks hlen x]
  simp only [planOr, intShape]
  congr 1
  have hz : (argRegs.zip (S.args x)).map Prod.snd = S.args x :=
    List.map_snd_zip (by rw [argRegs_length, hlen x]; exact hks)
  rw [show (fun p : Reg × Word => wordBytes p.2) = wordBytes ∘ Prod.snd from rfl,
    ← List.map_map, hz]

theorem ofScalarFn_pure (x : S.Arg) :
    (Silmaril.Machine.SystemV.Abi.plan {}
        (objectsOr ((ks.map Scalar.toCtype).mapM (objectOfCtype tags)))
        (resultOr ((some (Scalar.toCtype r)).mapM (objectOfCtype tags))) ks.length
        false).toOption.isSome = true ∧
      List.Forall₂ (fun (b : List Byte) (o : Object) => b.length = o.size)
        ((S.args x).map wordBytes) (objectsOr ((ks.map Scalar.toCtype).mapM (objectOfCtype tags))) := by
  have hos := Silmaril.Machine.Abi.CtypeBridge.mapM_toCtype tags ks
  have hro := Silmaril.Machine.Abi.CtypeBridge.optionMapM_toCtype tags (some r)
  simp only [Option.map_some] at hro
  rw [hos, hro]
  simp only [objectsOr, resultOr]
  refine ⟨?_, ?_⟩
  · rw [ofScalarFn_planOk S ks r h64 hr hks hlen x]; rfl
  · refine forall₂_wordBytes _ _ (by rw [hlen x, List.length_map]) ?_
    intro o ho
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ho
    rw [h64 k hk]; rfl

omit h64 hr hks hlen in
theorem ofScalarFn_classified :
    Classified tags (ks.map Scalar.toCtype) (some (Scalar.toCtype r)) := by
  have hos := Silmaril.Machine.Abi.CtypeBridge.mapM_toCtype tags ks
  have hro := Silmaril.Machine.Abi.CtypeBridge.optionMapM_toCtype tags (some r)
  simp only [Option.map_some] at hro
  refine ⟨?_, ?_⟩
  · rw [hos]; rfl
  · rw [hro]; rfl

/-- `ofScalarFn ⊑ FnSpec.toC`. -/
theorem ofScalarFn_sub_toC : (ofScalarFn tags S ks r).Sub S.toC := by
  refine ⟨fun y => ⟨y, ofScalarFn_shape tags S ks r h64 hr hks hlen y, Nat.le_refl _,
    fun fr => ⟨xemp, ?_, fun rb => ?_⟩⟩⟩
  · intro h hp
    refine ⟨h, XFrag.empty, XFrag.disjoint_empty_right h, (XFrag.union_empty h).symm, ?_, rfl⟩
    show (⌜_⌝ₓ ∗ₓ ⌜_⌝ₓ ∗ₓ ↑ₓ(S.pre y)) h
    refine (xspure_sep_apply _ _ _).2 ⟨ofScalarFn_pure tags S ks r h64 hr hks hlen y, ?_⟩
    exact (xspure_sep_apply _ _ _).2 ⟨ofScalarFn_classified tags ks r, hp⟩
  · rw [xsep_emp]; exact xentails_refl _

/-- `FnSpec.toC ⊑ ofScalarFn`. -/
theorem toC_sub_ofScalarFn : S.toC.Sub (ofScalarFn tags S ks r) := by
  refine ⟨fun y => ⟨y, (ofScalarFn_shape tags S ks r h64 hr hks hlen y).symm, Nat.le_refl _,
    fun fr => ⟨xemp, ?_, fun rb => ?_⟩⟩⟩
  · intro h hp
    have hp' : (⌜_⌝ₓ ∗ₓ ⌜_⌝ₓ ∗ₓ ↑ₓ(S.pre y)) h := hp
    obtain ⟨-, hp'⟩ := (xspure_sep_apply _ _ _).1 hp'
    obtain ⟨-, hp'⟩ := (xspure_sep_apply _ _ _).1 hp'
    exact ⟨h, XFrag.empty, XFrag.disjoint_empty_right h, (XFrag.union_empty h).symm, hp', rfl⟩
  · rw [xsep_emp]; exact xentails_refl _

end Scalar

/-! ## The FFI run -/

open Silmaril.Machine.SystemV.Abi (Ffi.State Ffi.Call Ffi.Signature)

theorem setLow128_setWidth (old : BitVec 512) (v : BitVec 128) :
    (setLow128 old v).setWidth 128 = v := by
  unfold setLow128
  ext i hi
  simp only [BitVec.getElem_setWidth]
  rw [BitVec.getLsbD_append]
  simp [hi, BitVec.getLsbD_eq_getElem]

theorem xregOfIdx_toNat (r : XReg) : xregOfIdx r.toBitVec.toNat = r := by
  simp [xregOfIdx]

/-- `withX` and the projection `ffiXState` are inverse on the XMM machine state. -/
theorem ffiXState_withX (s : Ffi.State) (x : XState) : ffiXState (withX s x) = x := by
  cases x with
  | mk m xmm =>
    simp only [ffiXState, withX]
    congr 1
    funext r
    have hlt : r.toBitVec.toNat < 16 := r.toBitVec.isLt
    simp only [hlt, ite_true, xregOfIdx_toNat, setLow128_setWidth]

/-- The complement of a part of a fragment. -/
theorem exists_compl {hP s : XFrag} (hl : XFrag.Le hP s) :
    ∃ hF, XFrag.Disjoint hP hF ∧ s = XFrag.union hP hF ∧
      ∀ l, hP.1 l = none → hF.1 l = s.1 l := by
  refine ⟨(fun l => if hP.1 l = none then s.1 l else none,
    fun r => if hP.2 r = none then s.2 r else none), ⟨?_, ?_⟩, ?_, ?_⟩
  · intro l; by_cases h : hP.1 l = none
    · exact .inl h
    · exact .inr (by simp [h])
  · intro r; by_cases h : hP.2 r = none
    · exact .inl h
    · exact .inr (by simp [h])
  · refine Prod.ext (funext fun l => ?_) (funext fun r => ?_)
    · simp only [XFrag.union, PMap.union]
      cases h : hP.1 l with
      | none => simp
      | some v => exact (hl.1 l v h)
    · simp only [XFrag.union, PMap.union]
      cases h : hP.2 r with
      | none => simp
      | some v => exact (hl.2 r v h)
  · intro l h; simp [h]

/-- Locations outside `hP` keep their values when the complement is the frame. -/
theorem agree_of_frame {hP hF hQ s s' : XFrag}
    (hs' : s' = XFrag.union hQ hF) (hd : XFrag.Disjoint hQ hF)
    (hF1 : ∀ l, hP.1 l = none → hF.1 l = s.1 l) (htot : ∀ l, (s.1 l).isSome) (l : Silmaril.X86.Sep.Loc)
    (hl : hP.1 l = none) : s'.1 l = s.1 l := by
  have e := hF1 l hl
  subst hs'
  simp only [XFrag.union, PMap.union]
  rcases hd.1 l with h | h
  · rw [h, e]
  · rw [e] at h; have := htot l; rw [h] at this; cases this

theorem toFrag_isSome (m : MState) (l : Silmaril.X86.Sep.Loc) : (toFrag m l).isSome := by
  cases l <;> rfl

/-- A lifted assertion read off an XMM machine state. -/
theorem holds_of_xle_lift {P : SProp} {h : XFrag} {x : XState} (hp : (↑ₓP) h)
    (hl : XFrag.Le h (toXFrag x)) : Holds P x.m := ⟨h.1, hp.1, hl.1⟩

/-- **The result placement gives the ABI model's `ResultAt`.** -/
theorem resultAt_of_retPt {sig : Ffi.Signature} {call : Ffi.Call} {final : Ffi.State}
    {u : Nat → Nat → Prop} (hshape : ResultShaped sig)
    (hsret : Silmaril.Machine.SystemV.Abi.Ffi.SretAt sig call u)
    (v : Silmaril.Machine.SystemV.Abi.Ffi.ResultValue sig.result) (rb : List Byte)
    (hrb : ResultBytes sig.result v rb)
    (hret : XHolds (retPt sig.callPlan.result (call.resultStorage.map (BitVec.ofNat 64)) rb)
      (ffiXState final)) :
    Silmaril.Machine.SystemV.Abi.Ffi.ResultAt sig call final v := by
  rcases sig with ⟨profile, arguments, result, namedCount, variadic, callPlan, planned⟩
  simp only [ResultShaped, Silmaril.Machine.SystemV.Abi.Ffi.SretAt] at hshape hsret hret ⊢
  unfold Silmaril.Machine.SystemV.Abi.Ffi.ResultAt
  cases result with
  | none =>
    simp only
    cases hcp : callPlan.result <;> simp only [hcp] at hshape ⊢
  | some spec =>
    simp only
    obtain ⟨e, he, rfl⟩ := hrb
    refine ⟨e, he, ?_⟩
    cases hcp : callPlan.result with
    | void => simp only [hcp] at hshape
    | direct cs =>
      simp only [hcp, retPt] at hret ⊢
      exact ((chunksPt_iff_chunksAt final e cs).1 hret).2
    | indirect size align =>
      simp only [hcp] at hshape hsret hret ⊢
      obtain ⟨address, hstore, hlt, hfit, -, -, -⟩ := hsret
      rw [hstore] at hret
      simp only [Option.map_some, retPt] at hret
      obtain ⟨h, hp, hl⟩ := hret
      have hP := holds_of_xle_lift (P := regPt .rax _ ∗ bytesPt _ _ ∗ ⌜_⌝) hp hl
      obtain ⟨g, hg, hgl⟩ := hP
      obtain ⟨a1, b1, ha1, hb1, hla1, hlb1, -, -⟩ := sep_le hg hgl
      obtain ⟨a2, b2, ha2, hb2, hla2, -, -, -⟩ := sep_le hb1 hlb1
      have hlen : (toSepBytes e).length = size := hb2.2
      have hrax := regPt_le ha1 hla1
      have hn : (BitVec.ofNat 64 address).toNat = address := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlt
      refine ⟨address, hstore, ⟨?_, ?_⟩, ?_⟩
      · have : (toSepBytes e).length = e.length := by simp [toSepBytes]
        omega
      · have hne : toSepBytes e ≠ [] := by
          intro h0; rw [h0] at hlen; simp at hlen; omega
        have hrd := readBytes_of_bytesPt hne ha2 hla2
        rw [hn] at hrd
        have : (toSepBytes e).length = e.length := by simp [toSepBytes]
        rw [this] at hrd
        exact hrd
      · show ((ffiXState final).m.core.read .rax).toNat = address
        rw [hrax, hn]

/-! ## The export -/

section Export

variable {M : Silmaril.X86.SegVC.Isa XState}

/-- Read a part of the postcondition off the final state. -/
theorem post_parts {S : CSpec} {C : XSProp} {x : S.Arg} {fr : Frame} {hq : XFrag} {x' : XState}
    (hqq : (C ∗ₓ S.Post x fr) hq) (hl : XFrag.Le hq (toXFrag x')) :
    ∃ rb, Holds (CtlOut (S.stack x) fr) x'.m ∧
      XHolds (retPt (S.shape x).plan.result (S.shape x).sret rb) x' ∧
      XHolds (S.post x fr rb) x' := by
  obtain ⟨-, b, -, hb, -, hlb, -, -⟩ := xsep_le hqq hl
  obtain ⟨rb, hrb⟩ := hb
  obtain ⟨e, p, he, hp, hle, hlp, -, -⟩ := xsep_le hrb hlb
  obtain ⟨c, r, hc, hr, hlc, hlr, -, -⟩ := xsep_le he hle
  obtain ⟨r1, -, hr1, -, hlr1, -, -, -⟩ := xsep_le hr hlr
  exact ⟨rb, holds_of_xle_lift hc hlc, ⟨r1, hr1, hlr1⟩, ⟨p, hp, hlp⟩⟩

/-- **The export from total satisfaction** (any `CSpec`): obligations are an entry split for
each admitted call, and that the postcondition gives the ABI model's `ResultAt`. -/
theorem realizes_of_satT {S : CSpec} {C : XSProp} {entry : Word} (hS : S.SatT M C entry)
    (sig : Ffi.Signature)
    (result : Silmaril.Machine.SystemV.Abi.Ffi.Values sig.arguments → Ffi.Call →
      Silmaril.Machine.SystemV.Abi.Ffi.ResultValue sig.result)
    (unaliased : Silmaril.Machine.SystemV.Abi.Ffi.Values sig.arguments → Nat → Nat → Prop)
    (domain : Silmaril.Machine.SystemV.Abi.Ffi.Values sig.arguments → Ffi.Call → Prop)
    (hentry : ∀ a call, Silmaril.Machine.SystemV.Abi.Ffi.Entry sig a call (unaliased a) →
      domain a call → ∃ x hP, EntrySplit S C entry call x hP ∧
        ∀ x', XHolds (S.Post x (callFrame call)) x' →
          Silmaril.Machine.SystemV.Abi.Ffi.ResultAt sig call (withX call.initial x') (result a call)) :
    FfiRealizesCall sig result (fun _ call => entryWrites S C entry call) unaliased domain
      (xExecute M) := by
  intro a call hE hD
  obtain ⟨x, hP, hsplit, hval⟩ := hentry a call hE hD
  obtain ⟨hpre, hle, havoid, hroom, halign⟩ := hsplit
  obtain ⟨hF, hdisj, heq, hFval⟩ := exists_compl hle
  obtain ⟨x', hr, hQ⟩ := hS x (callFrame call) halign hroom (fun h => h = hF)
    (ffiXState call.initial) ⟨hP, hF, hdisj, heq, hpre, rfl⟩
  obtain ⟨hq, hf, hdq, heq', hqq, hfe⟩ := hQ
  rw [hfe] at heq' hdq
  have hagree : ∀ l, hP.1 l = none → toFrag x'.m l = toFrag call.initial.machine l :=
    agree_of_frame (s' := toXFrag x') heq' hdq hFval
      (fun l => toFrag_isSome (ffiXState call.initial).m l)
  have hlq : XFrag.Le hq (toXFrag x') := heq' ▸ XFrag.le_union_left hq hF
  obtain ⟨rb, hctl, -, -⟩ := post_parts hqq hlq
  obtain ⟨g, hg, hgl⟩ := hctl
  obtain ⟨g1, g2, hg1, hg2, hlg1, hlg2, -, -⟩ := sep_le hg hgl
  obtain ⟨g3, -, hg3, -, hlg3, -, -, -⟩ := sep_le hg2 hlg2
  have hrip := ripPt_le hg1 hlg1
  have hrsp := regPt_le hg3 hlg3
  have hfin : (withX call.initial x').machine = x'.m := rfl
  refine ⟨withX call.initial x', ⟨x', hr, rfl⟩, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · rw [hfin, hrip]; rfl
  · rw [hfin, hrsp]; rfl
  · intro reg hreg
    have := hagree (.reg reg) (havoid.2 reg hreg)
    simp only [toFrag, Option.some.injEq, Silmaril.X86.Sep.Val.word.injEq] at this
    rw [hfin]; exact this
  · exact hE.direction
  · exact hE.x87Mode
  · rfl
  · rfl
  · rfl
  · obtain ⟨hpost⟩ : Nonempty (XHolds (S.Post x (callFrame call)) x') := by
      obtain ⟨-, b, -, hb, -, hlb, -, -⟩ := xsep_le hqq hlq
      exact ⟨⟨b, hb, hlb⟩⟩
    exact hval x' hpost
  · refine ⟨?_, fun l hl => ?_⟩
    · have := hagree .regions havoid.1
      simp only [toFrag, Option.some.injEq, Silmaril.X86.Sep.Val.regions.injEq] at this
      exact this
    · have hn : hP.1 (.mem l) = none := by
        cases h : hP.1 (.mem l) with
        | none => rfl
        | some _ => exact absurd ⟨x, hP, ⟨hpre, hle, havoid, hroom, halign⟩, by simp [h]⟩ hl
      have := hagree (.mem l) hn
      simp only [toFrag, Option.some.injEq, Silmaril.X86.Sep.Val.cell.injEq] at this
      exact (congrArg Silmaril.X86.Sep.Cell.byte this :)

/-- **`ofSignature_realizes`**: a total proof of `ofSignature sig …` exports as
`FfiRealizesCall` for `sig`, with the spec's entry condition as domain and its owned bytes as
footprint, on the XMM machine's FFI run. -/
theorem ofSignature_realizes {sig : Ffi.Signature} {stack : Nat}
    {result : Silmaril.Machine.SystemV.Abi.Ffi.Values sig.arguments → Ffi.Call →
      Silmaril.Machine.SystemV.Abi.Ffi.ResultValue sig.result}
    {pre : SigArg sig → Frame → XSProp} {post : SigArg sig → Frame → List Byte → XSProp}
    {C : XSProp} {entry : Word} (hS : (ofSignature sig stack result pre post).SatT M C entry)
    (hshape : ResultShaped sig)
    (unaliased : Silmaril.Machine.SystemV.Abi.Ffi.Values sig.arguments → Nat → Nat → Prop) :
    FfiRealizesCall sig result
      (fun _ call => entryWrites (ofSignature sig stack result pre post) C entry call) unaliased
      (SigDomain sig stack result pre post C entry) (xExecute M) := by
  refine realizes_of_satT hS sig result unaliased _ ?_
  rintro a call hE ⟨x, hP, rfl, rfl, hsplit⟩
  refine ⟨x, hP, hsplit, fun x' hpost => ?_⟩
  obtain ⟨h, hh, hl⟩ := hpost
  obtain ⟨rb, -, hret, hu⟩ := post_parts (C := xtrue) (S := ofSignature sig stack result pre post)
    ⟨XFrag.empty, h, XFrag.disjoint_empty_left h, (XFrag.empty_union h).symm, trivial, hh⟩ hl
  obtain ⟨hu0, hu1, hlu⟩ := hu
  obtain ⟨pa, pb, hpure, -, -, -, -, -⟩ := xsep_le hu1 hlu
  refine resultAt_of_retPt hshape hE.sret (result x.values x.call) rb hpure.2 ?_
  rw [ffiXState_withX]
  exact hret

end Export

end Silmaril.Proofs.Machine.Abi.CSpecFfi
