module

public import Silmaril.Proofs.Wasm.Component.Reference.SplitLink

/-!
# `Soft` steps go back through code maps

`Linking.Split.ren_soft_back` replays a `Soft` step (a profile choice or a bubble, under the
context rules) of a renamed part configuration as a step of the part. The importer of a
`Linked2` is mapped into the shared store by a renaming *after* a relocation
(`linkC`: `ρ.code ∘ (sh s₀).code`), which is not a renaming. This file generalises the
replay to every code map that changes references and frames only (`CMap`: a map of
references and one of frames, extended structurally to administrative code; values,
labels, handlers and plain instructions are kept), provided the map creates no exception
reference and keeps module instances without tables and memories (`CMap.Ok`):

* `CMap.soft_back`: a `Soft` step of a mapped configuration is the image of a `Soft` step of
  the source, in the same stores; the source code stays good;
* `renMap`, `shiftMap`, `CMap.comp` with `code_ren`, `code_shift`, `code_comp`: renamings,
  shifts and their composites are code maps;
* `link_soft_back`: a `Soft` step of the image `linkC s₀ ρ σ c` of an importer configuration
  related by `ImpRel` is the image of a `Soft` step of `c`, with `ImpRel` kept (same renaming,
  ownership and shared store).

New; the inversion lemmas and the case analysis follow `Linking.Split.Back` with the renaming
replaced by the code map.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.SingleThreaded.Det
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel noHost Flat numericStep_flat
  vectorStep_flat TableStep.not_mod MemoryStep.not_mod Flat.codeGood num_toAdmin_plain)
open Silmaril.Proofs.Wasm.Game.Choice (Soft ChoiceFam)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **A code map**: a map of references and a map of frames, extended structurally to values
and administrative code. -/
structure CMap where
  /-- The map of references. -/
  ref : Ref → Ref
  /-- The map of frames. -/
  frame : Frame → Frame

namespace CMap

variable (M : CMap)

/-- The map of a value. -/
def val : Val → Val
  | .ref r => .ref (M.ref r)
  | v => v

/-- The map of administrative code. -/
def code : List Admin → List Admin
  | [] => []
  | .ref r :: l => .ref (M.ref r) :: code l
  | .label n c b :: l => .label n c (code b) :: code l
  | .handler n cs b :: l => .handler n cs (code b) :: code l
  | .frame n f b :: l => .frame n (M.frame f) (code b) :: code l
  | a :: l => a :: code l

@[simp] theorem code_nil : M.code [] = [] := by simp [code]
@[simp] theorem code_plain (i : Instr) (l : List Admin) :
    M.code (.plain i :: l) = .plain i :: M.code l := by simp [code]
@[simp] theorem code_ref (r : Ref) (l : List Admin) :
    M.code (.ref r :: l) = .ref (M.ref r) :: M.code l := by simp [code]
@[simp] theorem code_callRefType (d : DefType) (l : List Admin) :
    M.code (.callRefType d :: l) = .callRefType d :: M.code l := by simp [code]
@[simp] theorem code_returnCallRefType (d : DefType) (l : List Admin) :
    M.code (.returnCallRefType d :: l) = .returnCallRefType d :: M.code l := by simp [code]
@[simp] theorem code_trap (l : List Admin) : M.code (.trap :: l) = .trap :: M.code l := by
  simp [code]
@[simp] theorem code_label (n : Nat) (c : List Instr) (b l : List Admin) :
    M.code (.label n c b :: l) = .label n c (M.code b) :: M.code l := by simp [code]
@[simp] theorem code_handler (n : Nat) (cs : List Catch) (b l : List Admin) :
    M.code (.handler n cs b :: l) = .handler n cs (M.code b) :: M.code l := by simp [code]
@[simp] theorem code_frame (n : Nat) (f : Frame) (b l : List Admin) :
    M.code (.frame n f b :: l) = .frame n (M.frame f) (M.code b) :: M.code l := by simp [code]

@[simp] theorem code_append (l₁ l₂ : List Admin) :
    M.code (l₁ ++ l₂) = M.code l₁ ++ M.code l₂ := by
  induction l₁ with
  | nil => simp
  | cons a as ih => cases a <;> simp [ih]

@[simp] theorem code_cons_toAdmin (v : Val) (l : List Admin) :
    M.code (v.toAdmin :: l) = (M.val v).toAdmin :: M.code l := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, val]

@[simp] theorem code_vals (vs : List Val) : M.code (vals vs) = vals (vs.map M.val) := by
  induction vs with
  | nil => simp [vals]
  | cons v vs ih => simp [ih]

theorem code_cons (a : Admin) (l : List Admin) : M.code (a :: l) = M.code [a] ++ M.code l := by
  cases a <;> simp

theorem code_length (l : List Admin) : (M.code l).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => cases a <;> simp [ih]

/-! ### Inverting the map of code -/

variable {M}

theorem code_eq_append {l A B : List Admin} (h : M.code l = A ++ B) :
    ∃ A₀ B₀, l = A₀ ++ B₀ ∧ M.code A₀ = A ∧ M.code B₀ = B := by
  have hlen : l.length = A.length + B.length := by
    rw [← M.code_length l, h, List.length_append]
  have hl : l = l.take A.length ++ l.drop A.length := (List.take_append_drop _ _).symm
  rw [hl, M.code_append] at h
  have hA : (M.code (l.take A.length)).length = A.length := by
    rw [M.code_length, List.length_take]
    omega
  obtain ⟨h1, h2⟩ := List.append_inj h hA
  exact ⟨_, _, hl, h1, h2⟩

theorem code_single {l : List Admin} {y : Admin} (h : M.code l = [y]) :
    ∃ x, l = [x] ∧ M.code [x] = [y] := by
  have hl : l.length = 1 := by rw [← M.code_length l, h]; rfl
  match l, hl with
  | [x], _ => exact ⟨x, rfl, h⟩

theorem single_val {x : Admin} {v : Val} (hx : M.code [x] = [v.toAdmin]) :
    ∃ w, x = w.toAdmin ∧ M.val w = v := by
  rcases x with i | r | _ | _ | _ | _ | _ | _ <;>
    simp only [code_plain, code_ref, code_callRefType, code_returnCallRefType,
      code_label, code_handler, code_frame, code_trap, code_nil,
      List.cons.injEq, and_true] at hx
  · exact ⟨v, hx, by rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp_all [Val.toAdmin, val]⟩
  · refine ⟨.ref r, rfl, ?_⟩
    rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp_all [Val.toAdmin, val]
  all_goals (rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at hx)

theorem code_eq_vals {l : List Admin} {vs : List Val} (h : M.code l = vals vs) :
    ∃ vs₀, l = vals vs₀ ∧ vs₀.map M.val = vs := by
  induction vs generalizing l with
  | nil => exact ⟨[], List.eq_nil_of_length_eq_zero (by rw [← M.code_length l, h]; rfl), rfl⟩
  | cons v vs ih =>
    obtain ⟨A, B, rfl, hA, hB⟩ := code_eq_append (A := [v.toAdmin]) (B := vals vs) h
    obtain ⟨x, rfl, hx⟩ := code_single hA
    obtain ⟨vs₀, rfl, hvs⟩ := ih hB
    obtain ⟨w, rfl, hw⟩ := single_val hx
    exact ⟨w :: vs₀, rfl, by simp [hw, hvs]⟩

theorem single_trap {x : Admin} (h : M.code [x] = [.trap]) : x = .trap := by
  rcases x with i | r | _ | _ | _ | _ | _ | _ <;> simp_all

theorem single_plain {x : Admin} {i : Instr} (h : M.code [x] = [.plain i]) : x = .plain i := by
  rcases x with i | r | _ | _ | _ | _ | _ | _ <;> simp_all

theorem single_ref {x : Admin} {r : Ref} (h : M.code [x] = [.ref r]) :
    ∃ r₀, x = .ref r₀ ∧ M.ref r₀ = r := by
  rcases x with i | r | _ | _ | _ | _ | _ | _ <;> simp_all

theorem single_label {x : Admin} {n : Nat} {c : List Instr} {b : List Admin}
    (h : M.code [x] = [.label n c b]) : ∃ b₀, x = .label n c b₀ ∧ M.code b₀ = b := by
  rcases x with i | r | _ | _ | _ | _ | _ | _ <;> simp_all

theorem single_handler {x : Admin} {n : Nat} {cs : List Catch} {b : List Admin}
    (h : M.code [x] = [.handler n cs b]) : ∃ b₀, x = .handler n cs b₀ ∧ M.code b₀ = b := by
  rcases x with i | r | _ | _ | _ | _ | _ | _ <;> simp_all

theorem single_frame {x : Admin} {n : Nat} {f : Frame} {b : List Admin}
    (h : M.code [x] = [.frame n f b]) :
    ∃ f₀ b₀, x = .frame n f₀ b₀ ∧ M.frame f₀ = f ∧ M.code b₀ = b := by
  rcases x with i | r | _ | _ | _ | _ | _ | _ <;> simp_all

/-! ### Flat code -/

theorem flat_map {l : List Admin} (h : Flat l) (M : CMap) : M.code l = l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hl : Flat l := fun b hb => h b (List.mem_cons_of_mem _ hb)
    rcases h a (List.mem_cons_self) with ⟨i, rfl⟩ | rfl <;> simp [ih hl]

theorem single_flat {a : Admin} {A : List Admin} (h : M.code [a] = A) (hA : Flat A) :
    [a] = A := by
  obtain ⟨y, rfl⟩ : ∃ y, A = [y] := by
    have hl : A.length = 1 := by rw [← h, code_length]; rfl
    match A, hl with
    | [y], _ => exact ⟨y, rfl⟩
  rcases hA y List.mem_cons_self with ⟨i, rfl⟩ | rfl
  · rw [single_plain h]
  · rw [single_trap h]

theorem code_flat_inv {X l : List Admin} (h : M.code X = l) (hl : Flat l) : X = l := by
  induction X generalizing l with
  | nil => simpa using h.symm
  | cons a X ih =>
    show a :: X = l
    have h' : M.code [a] ++ M.code X = l := (M.code_cons a X).symm.trans h
    have hA : Flat (M.code [a]) := fun b hb => hl b (h' ▸ List.mem_append_left _ hb)
    have hB : Flat (M.code X) := fun b hb => hl b (h' ▸ List.mem_append_right _ hb)
    have hXB : X = M.code X := ih rfl hB
    have haA : [a] = M.code [a] := single_flat rfl hA
    calc a :: X = [a] ++ X := rfl
      _ = M.code [a] ++ M.code X := by rw [← haA, ← hXB]
      _ = l := h'

/-! ### `Soft` steps of a mapped configuration -/

/-- **The conditions of the replay** for sources good for `O`: the map creates no exception
reference, and the image of a good frame runs in a module instance without tables, memories,
element or data segments. -/
structure Ok (M : CMap) (O : Own) : Prop where
  exn : ∀ r a, M.ref r = .exn a → ∃ b, r = .exn b
  mod : ∀ F, O.FrameGood F → ∃ O' : Own, O'.ModGood (M.frame F).module

/-- The conclusion of `soft_back`. -/
def Back (P : Profile) (M : CMap) (O : Own) (p σ : Store H) (F : Frame) (X : List Admin)
    (d : Config H) : Prop :=
  ∃ X', Soft P ⟨p, F, X⟩ ⟨p, F, X'⟩ ∧ d = ⟨σ, M.frame F, M.code X'⟩ ∧ O.CodeGood X'

theorem back_choice {P : Profile} {O : Own} {p σ : Store H} {k : Fam}
    {F : Frame} {X : List Admin} {d : Config H} (hM : M.Ok O) (hk : ChoiceFam k)
    (h : FamRel P k σ (M.frame F) (M.code X) d) (hf : O.FrameGood F) :
    Back P M O p σ F X d := by
  obtain ⟨O', hm⟩ := hM.mod F hf
  cases k with
  | numeric =>
    obtain ⟨out, hn, rfl⟩ := h
    obtain ⟨hl, ho⟩ := numericStep_flat hn
    have hX : M.code X = X := (code_flat_inv rfl hl).symm
    rw [hX] at hn
    exact ⟨out, .choice (k := .numeric) trivial ⟨out, hn, rfl⟩, by rw [flat_map ho M],
      ho.codeGood O⟩
  | vector =>
    obtain ⟨out, hn, rfl⟩ := h
    obtain ⟨hl, ho⟩ := vectorStep_flat hn
    have hX : M.code X = X := (code_flat_inv rfl hl).symm
    rw [hX] at hn
    exact ⟨out, .choice (k := .vector) trivial ⟨out, hn, rfl⟩, by rw [flat_map ho M],
      ho.codeGood O⟩
  | table => exact (TableStep.not_mod (O := O') h hm).elim
  | memory => exact (MemoryStep.not_mod (O := O') h hm).elim
  | _ => exact hk.elim

/-- The bubbling instruction of a mapped good code is a `TRAP`: good code holds no exception
reference, and the map creates none. -/
theorem bubble_trap {O : Own} {A T : List Admin} (hM : M.Ok O) (h : M.code A = T)
    (hT : IsBubble T) (hc : O.CodeGood A) : A = [.trap] ∧ T = [.trap] := by
  rcases hT with rfl | ⟨a, rfl⟩
  · obtain ⟨x, rfl, hx⟩ := code_single h
    exact ⟨by rw [single_trap hx], rfl⟩
  · exfalso
    obtain ⟨A₃, A₄, rfl, h3, -⟩ := code_eq_append (A := [.ref (.exn a)]) h
    obtain ⟨x, rfl, hx⟩ := code_single h3
    obtain ⟨r₀, rfl, hr₀⟩ := single_ref hx
    obtain ⟨b, rfl⟩ := hM.exn r₀ a hr₀
    exact Own.not_codeGood_throwing (a := b) hc (by simp)

/-- The mapped code of a bubble. -/
theorem bubble_inv {O : Own} {X : List Admin} {pp q : List Val} {T u r : List Admin}
    (hM : M.Ok O) (hcode : M.code X = vals (pp ++ q) ++ T ++ (u ++ r)) (hT : IsBubble T)
    (hc : O.CodeGood X) :
    ∃ vp vq U R, X = vals (vp ++ vq) ++ [.trap] ++ (U ++ R) ∧ T = [.trap] ∧
      vp.map M.val = pp ∧ vq.map M.val = q ∧ M.code U = u ∧ M.code R = r := by
  obtain ⟨A, B, rfl, hA, hB⟩ := code_eq_append hcode
  obtain ⟨A₁, A₂, rfl, hA₁, hA₂⟩ := code_eq_append hA
  obtain ⟨U, R, rfl, hU, hR⟩ := code_eq_append hB
  obtain ⟨vs₀, rfl, hvs⟩ := code_eq_vals hA₁
  obtain ⟨vp, vq, rfl, hvp, hvq⟩ := List.map_eq_append_iff.mp hvs
  have hc₂ : O.CodeGood A₂ := (O.codeGood_append.mp (O.codeGood_append.mp hc).1).2
  obtain ⟨rfl, rfl⟩ := bubble_trap hM hA₂ hT hc₂
  exact ⟨vp, vq, U, R, rfl, rfl, hvp, hvq, hU, hR⟩

theorem codeGood_bubble {O : Own} {vp vq : List Val} {U R : List Admin}
    (hc : O.CodeGood (vals (vp ++ vq) ++ [.trap] ++ (U ++ R))) :
    O.CodeGood (vals vp ++ [.trap] ++ R) := by
  have h1 := O.codeGood_append.mp hc
  have h3 : O.CodeGood (vals vp) := by
    have h4 := (O.codeGood_append.mp h1.1).1
    rw [vals_append] at h4
    exact (O.codeGood_append.mp h4).1
  exact O.codeGood_append.mpr ⟨O.codeGood_append.mpr ⟨h3, by simp⟩,
    (O.codeGood_append.mp h1.2).2⟩

theorem back_bubble {P : Profile} {O : Own} {p σ : Store H} {F : Frame}
    {X : List Admin} {d : Config H} (hM : M.Ok O) (h : Bubble σ (M.frame F) (M.code X) d)
    (hc : O.CodeGood X) : Back P M O p σ F X d := by
  obtain ⟨pp, q, T, u, r, hcode, hT, hqu, hd⟩ := h
  obtain ⟨vp, vq, U, R, hX, hT', hvp, hvq, hU, hR⟩ := bubble_inv hM hcode hT hc
  have hqU : vq ≠ [] ∨ U ≠ [] := by
    rcases hqu with hq | hu
    · exact .inl (fun h => hq (by rw [← hvq, h]; rfl))
    · exact .inr (fun h => hu (by rw [← hU, h, code_nil]))
  have hb : Bubble p F X ⟨p, F, vals vp ++ [.trap] ++ R⟩ := by
    rw [hX]
    exact ⟨vp, vq, [.trap], U, R, rfl, .inl rfl, hqU, rfl⟩
  have hgood : O.CodeGood (vals vp ++ [.trap] ++ R) := codeGood_bubble (hX ▸ hc)
  refine ⟨_, .bubble hb, ?_, hgood⟩
  rw [hd, hT', ← hvp, ← hR]
  simp

theorem back_instrs {P : Profile} {O : Own} {p σ s s' : Store H} {f f' : Frame}
    {vs : List Val} {is is' rest : List Admin}
    (ih : ∀ {F : Frame} {X : List Admin}, (⟨s, f, is⟩ : Config H) = ⟨σ, M.frame F, M.code X⟩ →
      O.FrameGood F → O.CodeGood X → Back P M O p σ F X ⟨s', f', is'⟩)
    {F : Frame} {X : List Admin}
    (hc : (⟨s, f, vals vs ++ is ++ rest⟩ : Config H) = ⟨σ, M.frame F, M.code X⟩)
    (hf : O.FrameGood F) (hX : O.CodeGood X) :
    Back P M O p σ F X ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  obtain ⟨rfl, rfl, hcode⟩ : s = σ ∧ f = M.frame F ∧ vals vs ++ is ++ rest = M.code X := by
    simpa only [Config.mk.injEq] using hc
  obtain ⟨A, R, rfl, hA, hR⟩ := code_eq_append hcode.symm
  obtain ⟨V, I, rfl, hV, hI⟩ := code_eq_append hA
  obtain ⟨vs₀, rfl, hvs⟩ := code_eq_vals hV
  have hgI : O.CodeGood I := (O.codeGood_append.mp (O.codeGood_append.mp hX).1).2
  obtain ⟨I', hstep, hd, hgI'⟩ := ih (by rw [hI]) hf hgI
  obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hd
  refine ⟨vals vs₀ ++ I' ++ R, .instrs hstep, ?_, ?_⟩
  · simp [hvs, hR]
  · obtain ⟨h1, h2⟩ := O.codeGood_append.mp hX
    exact O.codeGood_append.mpr ⟨O.codeGood_append.mpr ⟨(O.codeGood_append.mp h1).1, hgI'⟩, h2⟩

theorem back_label {P : Profile} {O : Own} {p σ s s' : Store H} {f f' : Frame}
    {n : Nat} {cont : List Instr} {is is' : List Admin}
    (ih : ∀ {F : Frame} {X : List Admin}, (⟨s, f, is⟩ : Config H) = ⟨σ, M.frame F, M.code X⟩ →
      O.FrameGood F → O.CodeGood X → Back P M O p σ F X ⟨s', f', is'⟩)
    {F : Frame} {X : List Admin}
    (hc : (⟨s, f, [.label n cont is]⟩ : Config H) = ⟨σ, M.frame F, M.code X⟩)
    (hf : O.FrameGood F) (hX : O.CodeGood X) :
    Back P M O p σ F X ⟨s', f', [.label n cont is']⟩ := by
  obtain ⟨rfl, rfl, hcode⟩ : s = σ ∧ f = M.frame F ∧ [.label n cont is] = M.code X := by
    simpa only [Config.mk.injEq] using hc
  obtain ⟨x, rfl, hx⟩ := code_single hcode.symm
  obtain ⟨I, rfl, hI⟩ := single_label hx
  obtain ⟨I', hstep, hd, hgI'⟩ := ih (by rw [hI]) hf ((O.codeGood_single_label ..).mp hX)
  obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hd
  exact ⟨[.label n cont I'], .label hstep, by simp, (O.codeGood_single_label ..).mpr hgI'⟩

theorem back_handler {P : Profile} {O : Own} {p σ s s' : Store H} {f f' : Frame}
    {n : Nat} {cs : List Catch} {is is' : List Admin}
    (ih : ∀ {F : Frame} {X : List Admin}, (⟨s, f, is⟩ : Config H) = ⟨σ, M.frame F, M.code X⟩ →
      O.FrameGood F → O.CodeGood X → Back P M O p σ F X ⟨s', f', is'⟩)
    {F : Frame} {X : List Admin}
    (hc : (⟨s, f, [.handler n cs is]⟩ : Config H) = ⟨σ, M.frame F, M.code X⟩)
    (hf : O.FrameGood F) (hX : O.CodeGood X) :
    Back P M O p σ F X ⟨s', f', [.handler n cs is']⟩ := by
  obtain ⟨rfl, rfl, hcode⟩ : s = σ ∧ f = M.frame F ∧ [.handler n cs is] = M.code X := by
    simpa only [Config.mk.injEq] using hc
  obtain ⟨x, rfl, hx⟩ := code_single hcode.symm
  obtain ⟨I, rfl, hI⟩ := single_handler hx
  obtain ⟨I', hstep, hd, hgI'⟩ := ih (by rw [hI]) hf ((O.codeGood_single_handler ..).mp hX)
  obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hd
  exact ⟨[.handler n cs I'], .handler hstep, by simp, (O.codeGood_single_handler ..).mpr hgI'⟩

theorem back_frame {P : Profile} {O : Own} {p σ s s' : Store H} {f fi fi' : Frame}
    {n : Nat} {is is' : List Admin}
    (ih : ∀ {F : Frame} {X : List Admin}, (⟨s, fi, is⟩ : Config H) = ⟨σ, M.frame F, M.code X⟩ →
      O.FrameGood F → O.CodeGood X → Back P M O p σ F X ⟨s', fi', is'⟩)
    {F : Frame} {X : List Admin}
    (hc : (⟨s, f, [.frame n fi is]⟩ : Config H) = ⟨σ, M.frame F, M.code X⟩)
    (hX : O.CodeGood X) :
    Back P M O p σ F X ⟨s', f, [.frame n fi' is']⟩ := by
  obtain ⟨rfl, rfl, hcode⟩ : s = σ ∧ f = M.frame F ∧ [.frame n fi is] = M.code X := by
    simpa only [Config.mk.injEq] using hc
  obtain ⟨x, rfl, hx⟩ := code_single hcode.symm
  obtain ⟨fi₀, I, rfl, hfi, hI⟩ := single_frame hx
  have hgx := (O.codeGood_single_frame ..).mp hX
  obtain ⟨I', hstep, hd, hgI'⟩ := ih (F := fi₀) (by rw [hfi, hI]) hgx.1 hgx.2
  obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hd
  exact ⟨[.frame n fi₀ I'], .frame hstep, by simp,
    (O.codeGood_single_frame ..).mpr ⟨hgx.1, hgI'⟩⟩

/-- **`Soft` steps of a mapped configuration go back** to `Soft` steps of the source, in the
same stores. -/
theorem soft_back {P : Profile} {O : Own} {p σ : Store H} (hM : M.Ok O) :
    ∀ {c d : Config H}, Soft P c d → ∀ {F : Frame} {X : List Admin},
      c = ⟨σ, M.frame F, M.code X⟩ → O.FrameGood F → O.CodeGood X → Back P M O p σ F X d := by
  intro c d hs
  induction hs with
  | choice hk h =>
    intro F X hc hf _
    obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hc
    exact back_choice hM hk h hf
  | bubble h =>
    intro F X hc _ hX
    obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hc
    exact back_bubble hM h hX
  | instrs _ ih => intro F X hc hf hX; exact back_instrs ih hc hf hX
  | label _ ih => intro F X hc hf hX; exact back_label ih hc hf hX
  | handler _ ih => intro F X hc hf hX; exact back_handler ih hc hf hX
  | frame _ ih => intro F X hc _ hX; exact back_frame ih hc hX

/-! ### Renamings, shifts and composites -/

/-- The composite of two code maps (`N` first). -/
def comp (M N : CMap) : CMap := ⟨M.ref ∘ N.ref, M.frame ∘ N.frame⟩

@[simp] theorem comp_ref (M N : CMap) (r : Ref) : (M.comp N).ref r = M.ref (N.ref r) := rfl
@[simp] theorem comp_frame (M N : CMap) (f : Frame) : (M.comp N).frame f = M.frame (N.frame f) :=
  rfl

theorem code_comp (M N : CMap) : ∀ l : List Admin, (M.comp N).code l = M.code (N.code l)
  | [] => by simp
  | .ref r :: l => by simp [code_comp M N l]
  | .label n c b :: l => by simp [code_comp M N b, code_comp M N l]
  | .handler n cs b :: l => by simp [code_comp M N b, code_comp M N l]
  | .frame n f b :: l => by simp [code_comp M N b, code_comp M N l]
  | .plain i :: l => by simp [code_comp M N l]
  | .callRefType d :: l => by simp [code_comp M N l]
  | .returnCallRefType d :: l => by simp [code_comp M N l]
  | .trap :: l => by simp [code_comp M N l]

end CMap

/-- A renaming as a code map. -/
def renMap (ρ : Ren) : CMap := ⟨ρ.ref, ρ.frame⟩

/-- A shift as a code map. -/
def shiftMap (δ : Shift) : CMap := ⟨δ.ref, δ.frame⟩

theorem code_ren (ρ : Ren) : ∀ l : List Admin, ρ.code l = (renMap ρ).code l
  | [] => by simp
  | .ref r :: l => by simp [code_ren ρ l, renMap]
  | .label n c b :: l => by simp [code_ren ρ b, code_ren ρ l]
  | .handler n cs b :: l => by simp [code_ren ρ b, code_ren ρ l]
  | .frame n f b :: l => by simp [code_ren ρ b, code_ren ρ l, renMap]
  | .plain i :: l => by simp [code_ren ρ l]
  | .callRefType d :: l => by simp [code_ren ρ l]
  | .returnCallRefType d :: l => by simp [code_ren ρ l]
  | .trap :: l => by simp [code_ren ρ l]

theorem code_shift (δ : Shift) : ∀ l : List Admin, δ.code l = (shiftMap δ).code l
  | [] => by simp
  | .ref r :: l => by simp [code_shift δ l, shiftMap]
  | .label n c b :: l => by simp [code_shift δ b, code_shift δ l]
  | .handler n cs b :: l => by simp [code_shift δ b, code_shift δ l]
  | .frame n f b :: l => by simp [code_shift δ b, code_shift δ l, shiftMap]
  | .plain i :: l => by simp [code_shift δ l]
  | .callRefType d :: l => by simp [code_shift δ l]
  | .returnCallRefType d :: l => by simp [code_shift δ l]
  | .trap :: l => by simp [code_shift δ l]

theorem ren_ref_eq_exn {ρ : Ren} {r : Ref} {a : Nat} (h : ρ.ref r = .exn a) : r = .exn a := by
  cases r <;> simp_all [Ren.ref]

theorem shift_ref_eq_exn {δ : Shift} {r : Ref} {a : Nat} (h : δ.ref r = .exn a) :
    ∃ b, r = .exn b := by
  cases r <;> simp_all [Shift.ref]

theorem ren_cmap_ok (ρ : Ren) (O : Own) : (renMap ρ).Ok O :=
  ⟨fun _ a h => ⟨a, ren_ref_eq_exn h⟩, fun _ hF => ⟨O, hF.1⟩⟩

theorem shift_cmap_ok (δ : Shift) (O : Own) : (shiftMap δ).Ok O :=
  ⟨fun _ _ h => shift_ref_eq_exn h, fun _ hF => ⟨shOwn δ O, modGood_shift δ hF.1⟩⟩

/-- **`Soft` steps of the importer's image go back**: a `Soft` step of `linkC s₀ ρ σ c`, for
`c` related by `ImpRel`, is the image of a `Soft` step of `c` (in its own store), and the
relation holds of the new configuration with the same renaming, ownership and shared store.
The step is replayed through `ρ` (into the relocated store), then through the shift. -/
theorem link_soft_back {P : Profile} (s₀ : Store H) {ρ : Ren} {O : Own} {σ : Store H}
    {c d : Config H} (hR : ImpRel s₀ ρ O σ c) (hs : Soft P (linkC s₀ ρ σ c) d) :
    ∃ X', Soft P c ⟨c.store, c.frame, X'⟩ ∧ d = linkC s₀ ρ σ ⟨c.store, c.frame, X'⟩ ∧
      ImpRel s₀ ρ O σ ⟨c.store, c.frame, X'⟩ := by
  obtain ⟨ρ₀, O₀, σ₀, hR₀, hf₀, hc₀⟩ := hR.good
  have e : linkC s₀ ρ σ c =
      ⟨σ, (renMap ρ).frame ((sh s₀).frame c.frame), (renMap ρ).code ((sh s₀).code c.code)⟩ := by
    simp only [linkC, ← code_ren]
    rfl
  obtain ⟨Y, hY, hdY, hgY⟩ := CMap.soft_back (p := reloc s₀ c.store) (ren_cmap_ok ρ O) (e ▸ hs)
    rfl hR.frame hR.code
  have e' : (⟨reloc s₀ c.store, (sh s₀).frame c.frame, (sh s₀).code c.code⟩ : Config H) =
      ⟨reloc s₀ c.store, (shiftMap (sh s₀)).frame c.frame, (shiftMap (sh s₀)).code c.code⟩ := by
    rw [code_shift]
    rfl
  obtain ⟨X', hX', hdX, -⟩ := CMap.soft_back (p := c.store) (shift_cmap_ok (sh s₀) O₀) hY e'
    hf₀ hc₀
  have hYX : Y = (sh s₀).code X' := by
    rw [code_shift]
    exact (Config.mk.inj hdX).2.2
  have hstep : Step P Silmaril.Proofs.Wasm.Game.Linking.Split.noHost c ⟨c.store, c.frame, X'⟩ :=
    hX'.step
  refine ⟨X', hX', ?_, ⟨SplitGood.step hstep hR.good, hR.rel, hR.frame, hYX ▸ hgY⟩⟩
  rw [hdY, hYX]
  simp only [linkC, ← code_ren]
  rfl

end Silmaril.Proofs.Wasm.Component.Reference
