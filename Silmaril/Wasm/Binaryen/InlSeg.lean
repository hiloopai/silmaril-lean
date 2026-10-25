module

public import Silmaril.Wasm.Binaryen.InlTop
public import Silmaril.Wasm.Binaryen.InlineSim

@[expose] public section

/-! # The inlining simulation: entering the inlined block

When the left side's site call enters the callee (`call_ref` on the fetched callee,
pending as `LG.seg`), the right side enters the inlined block: it takes the block,
stores the arguments into the added locals (`InlSim.sets_run`) and re-zeroes the
callee's vars (`zeros_run`). Then the right frame's added locals are the left callee
frame's locals, and the bodies are related by the relocation (`g_seg`).
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile}

/-- A local index from a natural number (`0` on overflow). -/
def lidx (n : Nat) : LocalIdx := (Idx.ofNat? n).getD ⟨⟨0, by decide⟩⟩

theorem lidx_toNat {n : Nat} (h : n < 2 ^ 32) : (lidx n).toNat = n := by
  unfold lidx Idx.ofNat?
  split
  · rfl
  · contradiction

/-- The re-zeroing stores: each zero constant followed by its `local.set`. -/
def zerosI : List Instr → List LocalIdx → List Instr
  | z :: zs, x :: xs => z :: .localSet x :: zerosI zs xs
  | _, _ => []

/-- The facts about the callee and the inlined block that entering it needs. -/
structure PrmC (p : Prm) where
  np : Nat
  nl : Nat
  zs : List Instr
  zvs : List Val
  ty_eq : p.mi.types[p.ty.toNat]? = some p.df
  ext_eq : p.ext = np + nl
  np_eq : ∀ ps rs, Expand p.df (.func ps rs) → ps.length = np
  zs_len : zs.length = nl
  zs_val : List.Forall₂ (fun z v => (Admin.plain z).val? = some v) zs zvs
  defaults : p.cf.locals.map (fun t => defaultVal? ((liftVal t).substAll (p.mi.types.map .dt))) =
    zvs.map some
  SBL_eq : p.SBL = ((List.range np).map fun j => lidx (p.base + j)).reverse.map .localSet ++
    zerosI zs ((List.range nl).map fun j => lidx (p.base + np + j)) ++
    InlineTy.xformL p.base 0 p.cf.body
  ret : InlineTy.retGoodL 0 p.cf.body

/-! ## The stores of the zeros -/

theorem zeros_run {s : Store H} {M : ModuleInst} {k : Nat} {R : List Admin} :
    ∀ (zs : List Instr) (vs : List Val) (xs : List LocalIdx) (fl : List (Option Val)) (b : Nat),
    zs.length = xs.length → List.Forall₂ (fun z v => (Admin.plain z).val? = some v) zs vs →
    (∀ j x, xs[j]? = some x → x.toNat = b + j) → (∀ j < xs.length, b + j < fl.length) →
    ∃ fl', Steps P Det.noHost ⟨s, ⟨fl, M⟩, [.label k [] (expression (zerosI zs xs) ++ R)]⟩
        ⟨s, ⟨fl', M⟩, [.label k [] R]⟩ ∧ fl'.length = fl.length ∧
      (∀ j < vs.length, fl'[b + j]? = some vs[j]?) ∧
      (∀ i, (i < b ∨ b + vs.length ≤ i) → fl'[i]? = fl[i]?)
  | [], [], xs, fl, b, _, .nil, _, _ =>
    ⟨fl, by simpa [zerosI, expression] using .refl, rfl, fun j hj => by simp at hj,
      fun _ _ => rfl⟩
  | z :: zs, v :: vs, x :: xs, fl, b, hl, .cons hz hzs, hx, hb => by
    have hx0 : x.toNat = b := by simpa using hx 0 x rfl
    have hxlt : x.toNat < fl.length := by have := hb 0 (by simp); omega
    have hz' : Admin.plain z = v.toAdmin := Admin.eq_of_val? hz
    have hst : Step P Det.noHost
        ⟨s, ⟨fl, M⟩, [.label k [] (expression (zerosI (z :: zs) (x :: xs)) ++ R)]⟩
        ⟨s, ⟨fl.set x.toNat (some v), M⟩, [.label k [] (expression (zerosI zs xs) ++ R)]⟩ := by
      refine .ctxtLabel ?_
      have h₀ : Step P Det.noHost ⟨s, ⟨fl, M⟩, [v.toAdmin, .plain (.localSet x)]⟩
          ⟨s, ⟨fl.set x.toNat (some v), M⟩, []⟩ := .variable (.localSet hxlt)
      have e₁ : expression (zerosI (z :: zs) (x :: xs)) ++ R =
          vals [] ++ [v.toAdmin, .plain (.localSet x)] ++ (expression (zerosI zs xs) ++ R) := by
        simp [zerosI, expression, hz']
      have e₂ : expression (zerosI zs xs) ++ R =
          vals [] ++ [] ++ (expression (zerosI zs xs) ++ R) := by simp
      rw [e₁, e₂]
      by_cases hne : ([] : List Val) ≠ [] ∨ expression (zerosI zs xs) ++ R ≠ []
      · exact .ctxtInstrs h₀ hne
      · simp only [ne_eq, not_or, not_not] at hne
        rw [hne.2]
        simpa using h₀
    obtain ⟨fl', hsteps, hlen, hmid, hout⟩ := zeros_run zs vs xs (fl.set x.toNat (some v)) (b + 1)
      (by simpa using hl) hzs
      (fun j y hy => by have := hx (j + 1) y (by simpa using hy); omega)
      (fun j hj => by have := hb (j + 1) (by simp; omega); simp; omega)
    refine ⟨fl', Relation.ReflTransGen.head hst hsteps, by rw [hlen, List.length_set], ?_, ?_⟩
    · intro j hj
      rcases j with _ | j
      · rw [Nat.add_zero, hout b (.inl (by omega)), ← hx0, List.getElem?_set_self hxlt]; rfl
      · have := hmid j (by simp at hj; omega)
        rw [show b + (j + 1) = b + 1 + j by omega, this]
        rfl
    · intro i hi
      have hi' : i < b ∨ b + vs.length + 1 ≤ i := by
        rcases hi with hi | hi
        · exact .inl hi
        · right; simp only [List.length_cons] at hi; omega
      rw [hout i (by omega), List.getElem?_set_ne (by omega)]
  | [], _ :: _, _, _, _, _, h, _, _ => by cases h
  | _ :: _, [], _, _, _, _, h, _, _ => by cases h
  | _ :: _, _ :: _, [], _, _, hl, _, _, _ => by simp at hl

/-! ## Entering the block -/

theorem getElem?_range_map_lidx {b n j : Nat} {x : LocalIdx} (hb : n = 0 ∨ b + n ≤ 2 ^ 32)
    (h : ((List.range n).map fun j => lidx (b + j))[j]? = some x) : x.toNat = b + j := by
  rw [List.getElem?_map] at h
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hlt, hkj⟩ := List.getElem?_eq_some_iff.mp hk
  rw [List.getElem_range] at hkj
  subst hkj
  simp only [List.length_range] at hlt
  exact lidx_toNat (by omega)

theorem g_seg (hok : PrmOk p) (hC : PrmC p) {s t : Store H} {fo : Frame} {E : List (Option Val)}
    (_hm : fo.module = p.mi) (hl : fo.locals.length = p.base) (he : E.length = p.ext)
    {vs₂ : List Val} {c₀ : Config H}
    (hh : Det.Head P s fo (vs₂ ++ [.ref (.func p.af)]) (.callRefType p.df) c₀) (hSR : SR p s t) :
    ∃ (c₀' : Config H) (E' : List (Option Val)),
      Relation.TransGen (Step P Det.noHost)
        ⟨t, ⟨fo.locals ++ E, p.mi⟩, vals vs₂ ++ [.plain (.block (.typeIdx p.ty) p.SBL)]⟩ c₀' ∧
      SR p c₀.store c₀'.store ∧ E'.length = p.ext ∧ c₀.frame = fo ∧
      c₀'.frame = ⟨fo.locals ++ E', p.mi⟩ ∧ LG p E' c₀.code c₀'.code := by
  obtain ⟨hg, hf, rfl⟩ := hSR
  have hSR : SR p s (withFuncs s (newFuncs p s.funcs)) := ⟨hg, hf, rfl⟩
  generalize hargs : vs₂ ++ [Val.ref (.func p.af)] = args at hh
  cases hh with
  | callRefFunc ha hc hfi he' hn hcode =>
    rename_i vs a fi ps rs code
    subst ha
    obtain ⟨rfl, ha2⟩ := List.append_inj' hargs rfl
    have ha3 : a = p.af := by simp at ha2; exact ha2.symm
    subst ha3
    rw [hf] at hfi
    cases hfi
    simp only [fO, FuncCode.wasm.injEq] at hcode
    subst hcode
    have hnp := hC.np_eq ps rs he'
    have hext := hC.ext_eq
    have hbound := hok.bound
    have hnv : vs₂.length = hC.np := by rw [← hnp]; exact hn
    -- the block
    have he'' : Expand p.df (.func ps rs) := he'
    have hbt : ModuleInst.blockType? p.mi (.typeIdx p.ty) = some (ps.toList, rs.toList) := by
      simp [ModuleInst.blockType?, hC.ty_eq, DefType.funcType?, Expand.iff.mp he'']
    have h₁ : Step P Det.noHost
        ⟨withFuncs s (newFuncs p s.funcs), ⟨fo.locals ++ E, p.mi⟩,
          vals vs₂ ++ [.plain (.block (.typeIdx p.ty) p.SBL)]⟩
        ⟨withFuncs s (newFuncs p s.funcs), ⟨fo.locals ++ E, p.mi⟩,
          [.label rs.toList.length [] (vals vs₂ ++ expression p.SBL)]⟩ :=
      (Det.Head.block (P := P) (f := ⟨fo.locals ++ E, p.mi⟩) hbt hn).toStep
    -- the stores of the arguments
    set xs : List LocalIdx := (List.range hC.np).map fun j => lidx (p.base + j) with hxs
    set xz : List LocalIdx := (List.range hC.nl).map fun j => lidx (p.base + hC.np + j) with hxz
    set R : List Admin := expression (zerosI hC.zs xz) ++
      expression (InlineTy.xformL p.base 0 p.cf.body) with hR
    have hcode : vals vs₂ ++ expression p.SBL =
        vals vs₂ ++ expression (xs.reverse.map .localSet) ++ R := by
      rw [hC.SBL_eq, ← hxs, ← hxz, hR]
      simp only [expression, List.map_append, List.append_assoc]
    obtain ⟨fl₁, hs₁, hlen₁, hmid₁, hout₁⟩ := InlSim.sets_run (P := P) (host := Det.noHost)
      (s := withFuncs s (newFuncs p s.funcs)) (M := p.mi) (k := rs.toList.length) (base := p.base)
      (R := R) vs₂ xs (fo.locals ++ E) (by simp [hxs, hnv])
      (fun j x hx => getElem?_range_map_lidx (by omega) hx)
      (fun j hj => by simp [hxs] at hj; simp; omega)
    obtain ⟨fl₂, hs₂, hlen₂, hmid₂, hout₂⟩ := zeros_run (P := P)
      (s := withFuncs s (newFuncs p s.funcs)) (M := p.mi) (k := rs.toList.length)
      (R := expression (InlineTy.xformL p.base 0 p.cf.body)) hC.zs hC.zvs xz fl₁
      (p.base + hC.np) (by simp [hxz, hC.zs_len]) hC.zs_val
      (fun j x hx => getElem?_range_map_lidx (by omega) hx)
      (fun j hj => by simp [hxz] at hj; rw [hlen₁]; simp; omega)
    -- the callee frame
    set F := Frame.forCall (fO (H := H) p).module vs₂ p.cf.locals with hF
    have hFl : F.locals = vs₂.map some ++ hC.zvs.map some := by
      simp only [hF, Frame.forCall, fO]
      rw [hC.defaults]
    have hzl : hC.zvs.length = hC.nl := by
      rw [← hC.zs_len]; exact (List.Forall₂.length_eq hC.zs_val).symm
    have hfl₂ : fl₂ = fo.locals ++ F.locals := by
      apply List.ext_getElem?
      intro i
      rw [hFl]
      have hl₁ : fl₁.length = p.base + p.ext := by rw [hlen₁]; simp [hl, he]
      by_cases h1 : i < p.base
      · rw [hout₂ i (.inl (by omega)), hout₁ i (.inl h1), List.getElem?_append_left (by omega),
          List.getElem?_append_left (by omega)]
      · by_cases h2 : i < p.base + hC.np
        · have h' := hmid₁ (i - p.base) (by omega)
          have ei : p.base + (i - p.base) = i := by omega
          rw [ei] at h'
          have hj : i - p.base < vs₂.length := by omega
          rw [hout₂ i (.inl h2), h', List.getElem?_append_right (by omega), hl,
            List.getElem?_append_left (by simp; omega), List.getElem?_map,
            List.getElem?_eq_getElem hj]
          rfl
        · by_cases h3 : i < p.base + hC.np + hC.nl
          · have h' := hmid₂ (i - (p.base + hC.np)) (by omega)
            have ei : p.base + hC.np + (i - (p.base + hC.np)) = i := by omega
            rw [ei] at h'
            have hj : i - (p.base + hC.np) < hC.zvs.length := by omega
            have ei2 : i - p.base - (vs₂.map some).length = i - (p.base + hC.np) := by
              simp [hnv]; omega
            rw [h', List.getElem?_append_right (by omega), hl,
              List.getElem?_append_right (by simp; omega), ei2, List.getElem?_map,
              List.getElem?_eq_getElem hj]
            rfl
          · have hn₂ : fl₂.length ≤ i := by rw [hlen₂, hl₁]; omega
            have hn₃ : (fo.locals ++ (vs₂.map some ++ hC.zvs.map some)).length ≤ i := by
              simp only [List.length_append, List.length_map, hl, hnv, hzl]; omega
            rw [List.getElem?_eq_none hn₂, List.getElem?_eq_none hn₃]
    refine ⟨⟨withFuncs s (newFuncs p s.funcs), ⟨fl₂, p.mi⟩,
      [.label rs.toList.length [] (expression (InlineTy.xformL p.base 0 p.cf.body))]⟩,
      F.locals, ?_, SR.mono hSR rfl, ?_, rfl, by rw [hfl₂], ?_⟩
    · refine .head' h₁ ?_
      rw [hcode]
      exact hs₁.trans (by simpa [hR] using hs₂)
    · rw [hFl]; simp [hnv, hzl, hext]
    · exact .head (.site (by simp [hF, Frame.forCall, fO]) rfl (.a (LI.of_xformL hC.ret))) .nil
  | callRefNull hc =>
    have := congrArg List.getLast? hargs
    simp at this
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss

end Silmaril.Wasm.Binaryen.InlR
