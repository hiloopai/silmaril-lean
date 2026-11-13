module

public import Silmaril.Proofs.Wasm.Game.Linking.Split.Joint
public import Silmaril.Proofs.Wasm.Game.Machine.SoftAt

/-!
# Static linking, separation: backward simulation of the shared world

The split world (provider and consumer in their own stores) is a forward simulation of the
shared world (`Joint`): one step of a part is one step of the shared world. For an arbitrary
profile this file proves the converse for the steps that are not the forward image of a part
step, i.e. the `Soft` steps (profile choices and bubbles, `Choice.eq_or_soft`):

* `ren_soft_back`: a `Soft` step of a renamed part configuration is the renaming of a step of
  the part, in the same stores (numeric and vector operands and results hold no references, so
  renaming does not change them; tables and memories do not exist in parts; a bubbling
  exception would need an exception reference, which parts never hold);
* `soft_fill`: a `Soft` step of a top-level provider code that is not trapping, under the
  consumer's callout context, is a `Soft` step of the provider code;
* `reach_doomed'`: runs from a trapped shared configuration end in a trap, in the same store.

New (no source file).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Linking.Split

open Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.Choice Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-! ### Exception references -/

/-- The code holds no exception reference. -/
def NoExnRef (l : List Admin) : Prop := ∀ a, Ref.exn a ∉ codeRefs l

theorem Own.CodeGood.noExnRef {O : Own} {l : List Admin} (h : O.CodeGood l) : NoExnRef l :=
  fun a ha => h.1 (.exn a) ha

theorem Ren.codeRefs_code (ρ : Ren) : ∀ l : List Admin, codeRefs (ρ.code l) = (codeRefs l).map ρ.ref
  | [] => by simp
  | .ref r :: l => by simp [Ren.codeRefs_code ρ l]
  | .label n c b :: l => by simp [Ren.codeRefs_code ρ b, Ren.codeRefs_code ρ l]
  | .handler n cs b :: l => by simp [Ren.codeRefs_code ρ b, Ren.codeRefs_code ρ l]
  | .frame n f b :: l => by simp [Ren.codeRefs_code ρ b, Ren.codeRefs_code ρ l]
  | .plain i :: l => by simp [Ren.codeRefs_code ρ l]
  | .callRefType d :: l => by simp [Ren.codeRefs_code ρ l]
  | .returnCallRefType d :: l => by simp [Ren.codeRefs_code ρ l]
  | .trap :: l => by simp [Ren.codeRefs_code ρ l]

theorem Ren.ref_eq_exn {ρ : Ren} {r : Ref} {a : Nat} (h : ρ.ref r = .exn a) : r = .exn a := by
  cases r <;> simp_all [Ren.ref]

theorem NoExnRef.ren {l : List Admin} (h : NoExnRef l) (ρ : Ren) : NoExnRef (ρ.code l) := by
  intro a ha
  rw [Ren.codeRefs_code] at ha
  obtain ⟨r, hr, he⟩ := List.mem_map.mp ha
  exact h a (Ren.ref_eq_exn he ▸ hr)

/-- The references of a code with one instruction replaced. -/
theorem codeRefs_wrap {pre : List Val} {rest : List Admin} {x y : Admin} {B B' Y : List Admin}
    (hx : codeRefs [x] = codeRefs B) (hy : codeRefs [y] = codeRefs B')
    (ih : ∀ r ∈ codeRefs B', r ∈ codeRefs B ∨ r ∈ codeRefs Y) :
    ∀ r ∈ codeRefs (vals pre ++ [y] ++ rest),
      r ∈ codeRefs (vals pre ++ [x] ++ rest) ∨ r ∈ codeRefs Y := by
  intro r hr
  have h : (r ∈ codeRefs (vals pre) ∨ r ∈ codeRefs [y]) ∨ r ∈ codeRefs rest := by
    simpa only [codeRefs_append, List.mem_append] using hr
  have goal : ((r ∈ codeRefs (vals pre) ∨ r ∈ codeRefs [x]) ∨ r ∈ codeRefs rest) ∨
      r ∈ codeRefs Y := by
    rcases h with (h | h) | h
    · exact .inl (.inl (.inl h))
    · rcases ih r (hy ▸ h) with h' | h'
      · exact .inl (.inl (.inr (hx ▸ h')))
      · exact .inr h'
    · exact .inl (.inr h)
  simpa only [codeRefs_append, List.mem_append] using goal

theorem codeRefs_fill_sub (E : Ctx) (X Y : List Admin) :
    ∀ r ∈ codeRefs (E.fill Y), r ∈ codeRefs (E.fill X) ∨ r ∈ codeRefs Y := by
  induction E with
  | top pre rest =>
    intro r hr
    have h : (r ∈ codeRefs (vals pre) ∨ r ∈ codeRefs Y) ∨ r ∈ codeRefs rest := by
      simpa only [Ctx.fill, codeRefs_append, List.mem_append] using hr
    rcases h with (h | h) | h
    · exact .inl (by simp only [Ctx.fill, codeRefs_append, List.mem_append]; exact .inl (.inl h))
    · exact .inr h
    · exact .inl (by simp only [Ctx.fill, codeRefs_append, List.mem_append]; exact .inr h)
  | label pre n cont E rest ih => exact codeRefs_wrap (by simp) (by simp) ih
  | handler pre n cs E rest ih => exact codeRefs_wrap (by simp) (by simp) ih
  | frame pre n f E rest ih => exact codeRefs_wrap (by simp) (by simp) ih

theorem NoExnRef.fill {E : Ctx} {X Y : List Admin} (hX : NoExnRef (E.fill X))
    (hY : NoExnRef Y) : NoExnRef (E.fill Y) := fun a ha =>
  (codeRefs_fill_sub E X Y _ ha).elim (hX a) (hY a)

/-! ### Inverting the renaming of code -/

theorem Ren.code_cons (ρ : Ren) (a : Admin) (l : List Admin) :
    ρ.code (a :: l) = ρ.code [a] ++ ρ.code l := by
  cases a <;> simp

theorem Ren.code_length (ρ : Ren) (l : List Admin) : (ρ.code l).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => cases a <;> simp [ih]

theorem Ren.code_eq_append {ρ : Ren} {l A B : List Admin} (h : ρ.code l = A ++ B) :
    ∃ A₀ B₀, l = A₀ ++ B₀ ∧ ρ.code A₀ = A ∧ ρ.code B₀ = B := by
  have hlen : l.length = A.length + B.length := by
    rw [← ρ.code_length l, h, List.length_append]
  have hl : l = l.take A.length ++ l.drop A.length := (List.take_append_drop _ _).symm
  rw [hl, ρ.code_append] at h
  have hA : (ρ.code (l.take A.length)).length = A.length := by
    rw [ρ.code_length, List.length_take]
    omega
  obtain ⟨h1, h2⟩ := List.append_inj h hA
  exact ⟨_, _, hl, h1, h2⟩

theorem Ren.code_single {ρ : Ren} {l : List Admin} {y : Admin} (h : ρ.code l = [y]) :
    ∃ x, l = [x] ∧ ρ.code [x] = [y] := by
  have hl : l.length = 1 := by rw [← ρ.code_length l, h]; rfl
  match l, hl with
  | [x], _ => exact ⟨x, rfl, h⟩

theorem Ren.code_eq_vals {ρ : Ren} {l : List Admin} {vs : List Val} (h : ρ.code l = vals vs) :
    ∃ vs₀, l = vals vs₀ ∧ vs₀.map ρ.val = vs := by
  induction vs generalizing l with
  | nil => exact ⟨[], List.eq_nil_of_length_eq_zero (by rw [← ρ.code_length l, h]; rfl), rfl⟩
  | cons v vs ih =>
    obtain ⟨A, B, rfl, hA, hB⟩ := Ren.code_eq_append (A := [v.toAdmin]) (B := vals vs) h
    obtain ⟨x, rfl, hx⟩ := Ren.code_single hA
    obtain ⟨vs₀, rfl, hvs⟩ := ih hB
    have hx' : ∃ w, x = w.toAdmin ∧ ρ.val w = v := by
      rcases x with i | r | _ | _ | _ | _ | _ | _ <;>
        simp only [Ren.code_plain, Ren.code_ref, Ren.code_callRefType, Ren.code_returnCallRefType,
          Ren.code_label, Ren.code_handler, Ren.code_frame, Ren.code_trap, Ren.code_nil,
          List.cons.injEq, and_true] at hx
      · exact ⟨v, hx, by rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp_all [Val.toAdmin, Ren.val]⟩
      · refine ⟨.ref r, rfl, ?_⟩
        rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp_all [Val.toAdmin, Ren.val]
      all_goals (rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at hx)
    obtain ⟨w, rfl, hw⟩ := hx'
    exact ⟨w :: vs₀, rfl, by simp [hw, hvs]⟩

theorem Ren.single_trap {ρ : Ren} {x : Admin} (h : ρ.code [x] = [.trap]) : x = .trap := by
  rcases x with i | r | _ | _ | _ | _ | _ | _ <;> simp_all

theorem Ren.single_plain {ρ : Ren} {x : Admin} {i : Instr} (h : ρ.code [x] = [.plain i]) :
    x = .plain i := by
  rcases x with i | r | _ | _ | _ | _ | _ | _ <;> simp_all

theorem Ren.single_ref {ρ : Ren} {x : Admin} {r : Ref} (h : ρ.code [x] = [.ref r]) :
    ∃ r₀, x = .ref r₀ ∧ ρ.ref r₀ = r := by
  rcases x with i | r | _ | _ | _ | _ | _ | _ <;> simp_all

theorem Ren.single_label {ρ : Ren} {x : Admin} {n : Nat} {c : List Instr} {b : List Admin}
    (h : ρ.code [x] = [.label n c b]) : ∃ b₀, x = .label n c b₀ ∧ ρ.code b₀ = b := by
  rcases x with i | r | _ | _ | _ | _ | _ | _ <;> simp_all

theorem Ren.single_handler {ρ : Ren} {x : Admin} {n : Nat} {cs : List Catch} {b : List Admin}
    (h : ρ.code [x] = [.handler n cs b]) : ∃ b₀, x = .handler n cs b₀ ∧ ρ.code b₀ = b := by
  rcases x with i | r | _ | _ | _ | _ | _ | _ <;> simp_all

theorem Ren.single_frame {ρ : Ren} {x : Admin} {n : Nat} {f : Frame} {b : List Admin}
    (h : ρ.code [x] = [.frame n f b]) :
    ∃ f₀ b₀, x = .frame n f₀ b₀ ∧ ρ.frame f₀ = f ∧ ρ.code b₀ = b := by
  rcases x with i | r | _ | _ | _ | _ | _ | _ <;> simp_all

/-! ### Flat code -/

/-- Plain instructions and traps only: the operands and results of the pure families. -/
def Flat (l : List Admin) : Prop := ∀ a ∈ l, (∃ i, a = .plain i) ∨ a = .trap

theorem Flat.ren {l : List Admin} (h : Flat l) (ρ : Ren) : ρ.code l = l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hl : Flat l := fun b hb => h b (List.mem_cons_of_mem _ hb)
    rcases h a (List.mem_cons_self) with ⟨i, rfl⟩ | rfl <;> simp [ih hl]

theorem Ren.single_flat {ρ : Ren} {a : Admin} {A : List Admin} (h : ρ.code [a] = A)
    (hA : Flat A) : [a] = A := by
  obtain ⟨y, rfl⟩ : ∃ y, A = [y] := by
    have hl : A.length = 1 := by rw [← h, Ren.code_length]; rfl
    match A, hl with
    | [y], _ => exact ⟨y, rfl⟩
  rcases hA y List.mem_cons_self with ⟨i, rfl⟩ | rfl
  · rw [Ren.single_plain h]
  · rw [Ren.single_trap h]

theorem Ren.code_flat_inv {ρ : Ren} {X l : List Admin} (h : ρ.code X = l) (hl : Flat l) :
    X = l := by
  induction X generalizing l with
  | nil => simpa using h.symm
  | cons a X ih =>
    show a :: X = l
    have h' : ρ.code [a] ++ ρ.code X = l := (Ren.code_cons ρ a X).symm.trans h
    have hA : Flat (ρ.code [a]) := fun b hb => hl b (h' ▸ List.mem_append_left _ hb)
    have hB : Flat (ρ.code X) := fun b hb => hl b (h' ▸ List.mem_append_right _ hb)
    have hXB : X = ρ.code X := ih rfl hB
    have haA : [a] = ρ.code [a] := Ren.single_flat rfl hA
    calc a :: X = [a] ++ X := rfl
      _ = ρ.code [a] ++ ρ.code X := by rw [← haA, ← hXB]
      _ = l := h'

theorem Flat.codeGood {l : List Admin} (h : Flat l) (O : Own) : O.CodeGood l := by
  induction l with
  | nil => exact O.codeGood_nil
  | cons a l ih =>
    have hl : Flat l := fun b hb => h b (List.mem_cons_of_mem _ hb)
    refine O.codeGood_cons.mpr ⟨?_, ih hl⟩
    rcases h a List.mem_cons_self with ⟨i, rfl⟩ | rfl <;> simp

theorem num_toAdmin_plain (v : NumVal) : ∃ i, (Val.num v).toAdmin = .plain i := by
  rcases v with ⟨⟨_⟩ | ⟨_⟩, _⟩ <;> exact ⟨_, rfl⟩

theorem flat_of_list {l : List Admin} (h : ∀ a ∈ l, (∃ i, a = .plain i) ∨ a = .trap) : Flat l := h

theorem numericStep_flat {P : Profile} {l out : List Admin} (h : NumericStep P l out) :
    Flat l ∧ Flat out := by
  cases h <;> refine ⟨fun a ha => ?_, fun a ha => ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha <;>
    (repeat' rcases ha with rfl | ha) <;>
    first
    | exact .inr rfl
    | exact .inl ⟨_, rfl⟩
    | exact .inl (num_toAdmin_plain _)

theorem vectorStep_flat {P : Profile} {l out : List Admin} (h : VectorStep P l out) :
    Flat l ∧ Flat out := by
  cases h <;> refine ⟨fun a ha => ?_, fun a ha => ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha <;>
    (repeat' rcases ha with rfl | ha) <;>
    first
    | exact .inr rfl
    | exact .inl ⟨_, rfl⟩
    | exact .inl (num_toAdmin_plain _)

/-! ### `Soft` steps of a renamed part -/

theorem TableStep.not_mod {P : Profile} {O : Own} {c c' : Config H} (h : TableStep P c c')
    (hm : O.ModGood c.frame.module) : False := by
  have h1 := hm.tables
  have h2 := hm.elems
  cases h <;> simp_all [table?_none, elem?_none]

theorem MemoryStep.not_mod {P : Profile} {O : Own} {c c' : Config H} (h : MemoryStep P c c')
    (hm : O.ModGood c.frame.module) : False := by
  have h1 := hm.mems
  have h2 := hm.datas
  cases h <;> simp_all [mem?_none, data?_none]

/-- The conclusion of `ren_soft_back`. -/
def RenBack (P : Profile) (ρ : Ren) (O : Own) (p σ : Store H) (F : Frame) (X : List Admin)
    (d : Config H) : Prop :=
  ∃ X', Step P noHost ⟨p, F, X⟩ ⟨p, F, X'⟩ ∧ d = ⟨σ, ρ.frame F, ρ.code X'⟩ ∧ O.CodeGood X'

theorem ren_back_choice {P : Profile} {ρ : Ren} {O : Own} {p σ : Store H} {k : Fam}
    {F : Frame} {X : List Admin} {d : Config H} (hk : ChoiceFam k)
    (h : FamRel P k σ (ρ.frame F) (ρ.code X) d) (hf : O.FrameGood F) :
    RenBack P ρ O p σ F X d := by
  cases k with
  | numeric =>
    obtain ⟨out, hn, rfl⟩ := h
    obtain ⟨hl, ho⟩ := numericStep_flat hn
    have hX : ρ.code X = X := (Ren.code_flat_inv rfl hl).symm
    rw [hX] at hn
    exact ⟨out, .numeric hn, by rw [ho.ren ρ], ho.codeGood O⟩
  | vector =>
    obtain ⟨out, hn, rfl⟩ := h
    obtain ⟨hl, ho⟩ := vectorStep_flat hn
    have hX : ρ.code X = X := (Ren.code_flat_inv rfl hl).symm
    rw [hX] at hn
    exact ⟨out, .vector hn, by rw [ho.ren ρ], ho.codeGood O⟩
  | table => exact (TableStep.not_mod (O := O) h hf.1).elim
  | memory => exact (MemoryStep.not_mod (O := O) h hf.1).elim
  | _ => exact hk.elim

/-- The bubbling instruction of a renamed part is a `TRAP`: parts hold no exception
references. -/
theorem ren_bubble_trap {ρ : Ren} {O : Own} {A T : List Admin} (h : ρ.code A = T)
    (hT : IsBubble T) (hc : O.CodeGood A) : A = [.trap] ∧ T = [.trap] := by
  rcases hT with rfl | ⟨a, rfl⟩
  · obtain ⟨x, rfl, hx⟩ := Ren.code_single h
    exact ⟨by rw [Ren.single_trap hx], rfl⟩
  · exfalso
    obtain ⟨A₃, A₄, rfl, h3, -⟩ := Ren.code_eq_append (A := [.ref (.exn a)]) h
    obtain ⟨x, rfl, hx⟩ := Ren.code_single h3
    obtain ⟨r₀, rfl, hr₀⟩ := Ren.single_ref hx
    exact Own.not_codeGood_throwing (a := a) hc (by simp [Ren.ref_eq_exn hr₀])

/-- The renamed code of a bubble. -/
theorem ren_bubble_inv {ρ : Ren} {O : Own} {X : List Admin} {pp q : List Val}
    {T u r : List Admin} (hcode : ρ.code X = vals (pp ++ q) ++ T ++ (u ++ r)) (hT : IsBubble T)
    (hc : O.CodeGood X) :
    ∃ vp vq U R, X = vals (vp ++ vq) ++ [.trap] ++ (U ++ R) ∧ T = [.trap] ∧
      vp.map ρ.val = pp ∧ vq.map ρ.val = q ∧ ρ.code U = u ∧ ρ.code R = r := by
  obtain ⟨A, B, rfl, hA, hB⟩ := Ren.code_eq_append hcode
  obtain ⟨A₁, A₂, rfl, hA₁, hA₂⟩ := Ren.code_eq_append hA
  obtain ⟨U, R, rfl, hU, hR⟩ := Ren.code_eq_append hB
  obtain ⟨vs₀, rfl, hvs⟩ := Ren.code_eq_vals hA₁
  obtain ⟨vp, vq, rfl, hvp, hvq⟩ := List.map_eq_append_iff.mp hvs
  have hc₂ : O.CodeGood A₂ := (O.codeGood_append.mp (O.codeGood_append.mp hc).1).2
  obtain ⟨rfl, rfl⟩ := ren_bubble_trap hA₂ hT hc₂
  exact ⟨vp, vq, U, R, rfl, rfl, hvp, hvq, hU, hR⟩

theorem ren_back_bubble {P : Profile} {ρ : Ren} {O : Own} {p σ : Store H} {F : Frame}
    {X : List Admin} {d : Config H} (h : Bubble σ (ρ.frame F) (ρ.code X) d) (hc : O.CodeGood X) :
    RenBack P ρ O p σ F X d := by
  obtain ⟨pp, q, T, u, r, hcode, hT, hqu, hd⟩ := h
  obtain ⟨vp, vq, U, R, hX, hT', hvp, hvq, hU, hR⟩ := ren_bubble_inv hcode hT hc
  have hqU : vq ≠ [] ∨ U ≠ [] := by
    rcases hqu with hq | hu
    · exact .inl (fun h => hq (by rw [← hvq, h]; rfl))
    · exact .inr (fun h => hu (by rw [← hU, h, Ren.code_nil]))
  have hb : Bubble p F X ⟨p, F, vals vp ++ [.trap] ++ R⟩ := by
    rw [hX]
    exact ⟨vp, vq, [.trap], U, R, rfl, .inl rfl, hqU, rfl⟩
  have hc' : O.CodeGood (vals (vp ++ vq) ++ [.trap] ++ (U ++ R)) := hX ▸ hc
  have hgood : O.CodeGood (vals vp ++ [.trap] ++ R) := by
    have h1 := O.codeGood_append.mp hc'
    have h3 : O.CodeGood (vals vp) := by
      have h4 := (O.codeGood_append.mp h1.1).1
      rw [vals_append] at h4
      exact (O.codeGood_append.mp h4).1
    exact O.codeGood_append.mpr ⟨O.codeGood_append.mpr ⟨h3, by simp⟩,
      (O.codeGood_append.mp h1.2).2⟩
  refine ⟨_, bubble_step hb, ?_, hgood⟩
  rw [hd, hT', ← hvp, ← hR]
  simp

theorem ren_back_instrs {P : Profile} {ρ : Ren} {O : Own} {p σ s s' : Store H} {f f' : Frame}
    {vs : List Val} {is is' rest : List Admin}
    (ih : ∀ {F : Frame} {X : List Admin}, (⟨s, f, is⟩ : Config H) = ⟨σ, ρ.frame F, ρ.code X⟩ →
      O.FrameGood F → O.CodeGood X → RenBack P ρ O p σ F X ⟨s', f', is'⟩)
    {F : Frame} {X : List Admin}
    (hc : (⟨s, f, vals vs ++ is ++ rest⟩ : Config H) = ⟨σ, ρ.frame F, ρ.code X⟩)
    (hf : O.FrameGood F) (hX : O.CodeGood X) :
    RenBack P ρ O p σ F X ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  obtain ⟨rfl, rfl, hcode⟩ : s = σ ∧ f = ρ.frame F ∧ vals vs ++ is ++ rest = ρ.code X := by
    simpa only [Config.mk.injEq] using hc
  obtain ⟨A, R, rfl, hA, hR⟩ := Ren.code_eq_append hcode.symm
  obtain ⟨V, I, rfl, hV, hI⟩ := Ren.code_eq_append hA
  obtain ⟨vs₀, rfl, hvs⟩ := Ren.code_eq_vals hV
  have hgI : O.CodeGood I := (O.codeGood_append.mp (O.codeGood_append.mp hX).1).2
  obtain ⟨I', hstep, hd, hgI'⟩ := ih (by rw [hI]) hf hgI
  obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hd
  refine ⟨vals vs₀ ++ I' ++ R, lift_instrs vs₀ R ⟨p, F, I⟩ ⟨p, F, I'⟩ hstep, ?_, ?_⟩
  · simp [hvs, hR]
  · obtain ⟨h1, h2⟩ := O.codeGood_append.mp hX
    exact O.codeGood_append.mpr ⟨O.codeGood_append.mpr ⟨(O.codeGood_append.mp h1).1, hgI'⟩, h2⟩

theorem ren_back_label {P : Profile} {ρ : Ren} {O : Own} {p σ s s' : Store H} {f f' : Frame}
    {n : Nat} {cont : List Instr} {is is' : List Admin}
    (ih : ∀ {F : Frame} {X : List Admin}, (⟨s, f, is⟩ : Config H) = ⟨σ, ρ.frame F, ρ.code X⟩ →
      O.FrameGood F → O.CodeGood X → RenBack P ρ O p σ F X ⟨s', f', is'⟩)
    {F : Frame} {X : List Admin}
    (hc : (⟨s, f, [.label n cont is]⟩ : Config H) = ⟨σ, ρ.frame F, ρ.code X⟩)
    (hf : O.FrameGood F) (hX : O.CodeGood X) :
    RenBack P ρ O p σ F X ⟨s', f', [.label n cont is']⟩ := by
  obtain ⟨rfl, rfl, hcode⟩ : s = σ ∧ f = ρ.frame F ∧ [.label n cont is] = ρ.code X := by
    simpa only [Config.mk.injEq] using hc
  obtain ⟨x, rfl, hx⟩ := Ren.code_single hcode.symm
  obtain ⟨I, rfl, hI⟩ := Ren.single_label hx
  obtain ⟨I', hstep, hd, hgI'⟩ := ih (by rw [hI]) hf ((O.codeGood_single_label ..).mp hX)
  obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hd
  exact ⟨[.label n cont I'], lift_label n cont ⟨p, F, I⟩ ⟨p, F, I'⟩ hstep, by simp,
    (O.codeGood_single_label ..).mpr hgI'⟩

theorem ren_back_handler {P : Profile} {ρ : Ren} {O : Own} {p σ s s' : Store H} {f f' : Frame}
    {n : Nat} {cs : List Catch} {is is' : List Admin}
    (ih : ∀ {F : Frame} {X : List Admin}, (⟨s, f, is⟩ : Config H) = ⟨σ, ρ.frame F, ρ.code X⟩ →
      O.FrameGood F → O.CodeGood X → RenBack P ρ O p σ F X ⟨s', f', is'⟩)
    {F : Frame} {X : List Admin}
    (hc : (⟨s, f, [.handler n cs is]⟩ : Config H) = ⟨σ, ρ.frame F, ρ.code X⟩)
    (hf : O.FrameGood F) (hX : O.CodeGood X) :
    RenBack P ρ O p σ F X ⟨s', f', [.handler n cs is']⟩ := by
  obtain ⟨rfl, rfl, hcode⟩ : s = σ ∧ f = ρ.frame F ∧ [.handler n cs is] = ρ.code X := by
    simpa only [Config.mk.injEq] using hc
  obtain ⟨x, rfl, hx⟩ := Ren.code_single hcode.symm
  obtain ⟨I, rfl, hI⟩ := Ren.single_handler hx
  obtain ⟨I', hstep, hd, hgI'⟩ := ih (by rw [hI]) hf ((O.codeGood_single_handler ..).mp hX)
  obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hd
  exact ⟨[.handler n cs I'], lift_handler n cs ⟨p, F, I⟩ ⟨p, F, I'⟩ hstep, by simp,
    (O.codeGood_single_handler ..).mpr hgI'⟩

theorem ren_back_frame {P : Profile} {ρ : Ren} {O : Own} {p σ s s' : Store H} {f fi fi' : Frame}
    {n : Nat} {is is' : List Admin}
    (ih : ∀ {F : Frame} {X : List Admin}, (⟨s, fi, is⟩ : Config H) = ⟨σ, ρ.frame F, ρ.code X⟩ →
      O.FrameGood F → O.CodeGood X → RenBack P ρ O p σ F X ⟨s', fi', is'⟩)
    {F : Frame} {X : List Admin}
    (hc : (⟨s, f, [.frame n fi is]⟩ : Config H) = ⟨σ, ρ.frame F, ρ.code X⟩)
    (_hf : O.FrameGood F) (hX : O.CodeGood X) :
    RenBack P ρ O p σ F X ⟨s', f, [.frame n fi' is']⟩ := by
  obtain ⟨rfl, rfl, hcode⟩ : s = σ ∧ f = ρ.frame F ∧ [.frame n fi is] = ρ.code X := by
    simpa only [Config.mk.injEq] using hc
  obtain ⟨x, rfl, hx⟩ := Ren.code_single hcode.symm
  obtain ⟨fi₀, I, rfl, hfi, hI⟩ := Ren.single_frame hx
  have hgx := (O.codeGood_single_frame ..).mp hX
  obtain ⟨I', hstep, hd, hgI'⟩ := ih (F := fi₀) (by rw [hfi, hI]) hgx.1 hgx.2
  obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hd
  exact ⟨[.frame n fi₀ I'], lift_frame n F ⟨p, fi₀, I⟩ ⟨p, fi₀, I'⟩ hstep, by simp,
    (O.codeGood_single_frame ..).mpr ⟨hgx.1, hgI'⟩⟩

/-- **`Soft` steps of a renamed part go back** to steps of the part, in the same stores. -/
theorem ren_soft_back {P : Profile} {ρ : Ren} {O : Own} {p σ : Store H} :
    ∀ {c d : Config H}, Soft P c d → ∀ {F : Frame} {X : List Admin},
      c = ⟨σ, ρ.frame F, ρ.code X⟩ → O.FrameGood F → O.CodeGood X → RenBack P ρ O p σ F X d := by
  intro c d hs
  induction hs with
  | choice hk h =>
    intro F X hc hf _
    obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hc
    exact ren_back_choice hk h hf
  | bubble h =>
    intro F X hc _ hX
    obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hc
    exact ren_back_bubble h hX
  | instrs _ ih => intro F X hc hf hX; exact ren_back_instrs ih hc hf hX
  | label _ ih => intro F X hc hf hX; exact ren_back_label ih hc hf hX
  | handler _ ih => intro F X hc hf hX; exact ren_back_handler ih hc hf hX
  | frame _ ih => intro F X hc hf hX; exact ren_back_frame ih hc hf hX

/-! ### `Soft` steps of provider code under the callout context -/

theorem topAdmin_famOf {e : Admin} (h : TopAdmin e) (hv : e.val? = none) : famOf e = .control := by
  rcases e with i | r | _ | _ | _ | _ | _ | _
  · cases i <;> simp_all [TopAdmin, famOf, Admin.val?]
  all_goals simp_all [TopAdmin, famOf, Admin.val?]

theorem fnv_eq {l : List Admin} {W : List Val} {e : Admin} {R : List Admin}
    (h : fnv l = (W, e :: R)) : l = vals W ++ e :: R ∧ e.val? = none := by
  induction l generalizing W with
  | nil => simp at h
  | cons a l ih =>
    rcases ha : a.val? with _ | v
    · rw [fnv_cons_of_none ha] at h
      simp only [Prod.mk.injEq, List.nil_eq, List.cons.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨by simp, ha⟩
    · have hav : a = v.toAdmin := Admin.eq_of_val? ha
      subst hav
      rw [fnv_toAdmin_cons] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      obtain ⟨h3, h4⟩ := ih (W := (fnv l).1) (by rw [← h2])
      exact ⟨congrArg (v.toAdmin :: ·) h3, h4⟩

/-- The top-level code `Y` is running (its first non-value is not a trap). -/
def Live (Y : List Admin) : Prop := ∃ W e R, fnv Y = (W, e :: R) ∧ e ≠ .trap

/-- No `THROW_REF` bubbles out of code without exception references. -/
theorem soft_fill_exn {pre W : List Val} {Y rest R : List Admin} {e : Admin}
    (hexn : NoExnRef (vals pre ++ Y ++ rest)) (hY : Y = vals W ++ e :: R)
    (h : e = .plain .throwRef ∧ ∃ W' a, pre ++ W = W' ++ [.ref (.exn a)]) : False := by
  obtain ⟨-, W', a, hW⟩ := h
  have hmem : Ref.exn a ∈ codeRefs (vals (pre ++ W)) := by rw [hW]; simp
  have hcode : vals pre ++ Y ++ rest = vals (pre ++ W) ++ (e :: R ++ rest) := by
    rw [hY]; simp
  refine hexn a ?_
  rw [hcode, codeRefs_append]
  exact List.mem_append_left _ hmem

/-- A `Soft` step inside a frame of top-level code is a `Soft` step of that code. -/
theorem soft_fill_frame {P : Profile} {pre W : List Val} {rest R : List Admin} {s : Store H}
    {G : Frame} {Y : List Admin} {e : Admin} {d : Config H} (hY : Y = vals W ++ e :: R)
    (h : ∃ n fi is s' fi' is', e = .frame n fi is ∧ Soft P ⟨s, fi, is⟩ ⟨s', fi', is'⟩ ∧
      d = ⟨s', G, vals (pre ++ W) ++ [.frame n fi' is'] ++ (R ++ rest)⟩) :
    ∃ s' Y', d = ⟨s', G, vals pre ++ Y' ++ rest⟩ ∧ ∀ g, Soft P ⟨s, g, Y⟩ ⟨s', g, Y'⟩ := by
  obtain ⟨n, fi, is, s', fi', is', he, hin, hd⟩ := h
  refine ⟨s', vals W ++ [.frame n fi' is'] ++ R, by rw [hd]; simp, fun g => ?_⟩
  have hl := Soft.instrs (vs := W) (rest := R) (Soft.frame (f := g) (n := n) hin)
  rw [hY, he]
  simpa using hl

theorem soft_fill_top {P : Profile} {pre : List Val} {rest : List Admin} {s : Store H}
    {G : Frame} {Y : List Admin} {d : Config H} (htop : TopOK Y) (hlive : Live Y)
    (hexn : NoExnRef (vals pre ++ Y ++ rest)) (hs : Soft P ⟨s, G, vals pre ++ Y ++ rest⟩ d) :
    ∃ s' Y', d = ⟨s', G, vals pre ++ Y' ++ rest⟩ ∧ ∀ g, Soft P ⟨s, g, Y⟩ ⟨s', g, Y'⟩ := by
  obtain ⟨W, e, R, hfY, hne⟩ := hlive
  obtain ⟨hY, hv⟩ := fnv_eq hfY
  have he : TopAdmin e := htop e (by rw [hY]; simp)
  obtain ⟨W', e', R', hf, hat⟩ := Soft.at hs
  have hf' : fnv (vals pre ++ Y ++ rest) = (pre ++ W, e :: (R ++ rest)) := by
    rw [List.append_assoc, fnv_vals_append, fnv_append_of_cons hfY rest]
  have heq : pre ++ W = W' ∧ e = e' ∧ R ++ rest = R' := by simpa using hf'.symm.trans hf
  have hat' : SoftAt P s G (pre ++ W) e (R ++ rest) d := by
    rw [heq.1, heq.2.1, heq.2.2]
    exact hat
  rcases hat' with h | h | h | h | h | h
  · exact absurd h.1 hne
  · exact (soft_fill_exn hexn hY h).elim
  · exact absurd h (by rw [topAdmin_famOf he hv]; exact id)
  · obtain ⟨_, _, _, _, _, _, h, -⟩ := h; exact absurd (h ▸ he) (by simp [TopAdmin])
  · obtain ⟨_, _, _, _, _, _, h, -⟩ := h; exact absurd (h ▸ he) (by simp [TopAdmin])
  · exact soft_fill_frame hY h

theorem NoExnRef.inner {A B : List Admin} {x : Admin} {b : List Admin}
    (h : NoExnRef (A ++ [x] ++ B)) (hx : ∀ r ∈ codeRefs b, r ∈ codeRefs [x]) : NoExnRef b :=
  fun a ha => h a (by simp only [codeRefs_append, List.mem_append]; exact .inl (.inr (hx _ ha)))

/-- **`Soft` steps under the callout context.** A `Soft` step of running top-level code `Y`
under a callout context `E`, in code without exception references, is a `Soft` step of `Y`
(under any frame) in the hole of `E`. -/
theorem soft_fill {P : Profile} (E : Ctx) :
    ∀ {s : Store H} {G : Frame} {Y : List Admin} {d : Config H},
      TopOK Y → Live Y → NoExnRef (E.fill Y) → Soft P ⟨s, G, E.fill Y⟩ d →
      ∃ s' Y', d = ⟨s', G, E.fill Y'⟩ ∧ ∀ g, Soft P ⟨s, g, Y⟩ ⟨s', g, Y'⟩ := by
  induction E with
  | top pre rest => exact fun htop hlive hexn hs => soft_fill_top htop hlive hexn hs
  | label pre n cont E rest ih =>
    intro s G Y d htop hlive hexn hs
    obtain ⟨s', f', B', hin, hd⟩ := (Soft.at_of hs (fnv_vals_single pre _ rfl rest)).label_inv
    obtain ⟨s'', Y', hB, hY'⟩ := ih htop hlive (hexn.inner (by simp)) hin
    obtain ⟨hs'', hf'', hB'⟩ := Config.mk.inj hB
    exact ⟨s'', Y', by rw [hd, hs'', hf'', hB']; rfl, hY'⟩
  | handler pre n cs E rest ih =>
    intro s G Y d htop hlive hexn hs
    obtain ⟨s', f', B', hin, hd⟩ := (Soft.at_of hs (fnv_vals_single pre _ rfl rest)).handler_inv
    obtain ⟨s'', Y', hB, hY'⟩ := ih htop hlive (hexn.inner (by simp)) hin
    obtain ⟨hs'', hf'', hB'⟩ := Config.mk.inj hB
    exact ⟨s'', Y', by rw [hd, hs'', hf'', hB']; rfl, hY'⟩
  | frame pre n fi E rest ih =>
    intro s G Y d htop hlive hexn hs
    obtain ⟨s', fi', B', hin, hd⟩ := (Soft.at_of hs (fnv_vals_single pre _ rfl rest)).frame_inv
    obtain ⟨s'', Y', hB, hY'⟩ := ih htop hlive (hexn.inner (by simp)) hin
    obtain ⟨hs'', hf'', hB'⟩ := Config.mk.inj hB
    exact ⟨s'', Y', by rw [hd, hs'', hf'', hB']; rfl, hY'⟩

/-! ### Trapped shared configurations -/

/-- **Runs from a trapped configuration end in a trap**, in the same store, for every
profile. -/
theorem reach_doomed' {P : Profile} {x y : Store Nat × Thread} (run : Reach P x y) :
    ∀ {E : Ctx} {f : Frame}, x.2.config x.1 = ⟨x.1, f, E.fill [.trap]⟩ →
      ∀ {r : Result}, ResultAt y.1 y.2 r → r = .trap ∧ y.1 = x.1 := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro E f ht r hr
    have hc : E.fill [.trap] = r.toAdmin := by
      have h : (y.2.config y.1).code = r.toAdmin := hr
      rw [ht] at h
      exact h
    exact ⟨fill_trap_toAdmin hc, rfl⟩
  | @head a b hab _ ih =>
    show ∀ {E : Ctx} {f : Frame}, _ → ∀ {r : Result}, _ → r = .trap ∧ y.1 = a.1
    intro E f ht r hr
    obtain ⟨f', c', hb, hst⟩ := hab
    have hst' : Step P noHost ⟨a.1, f, E.fill [.trap]⟩ ⟨b.1, f', c'⟩ := ht ▸ hst
    obtain ⟨hs, hf, E', hE'⟩ := step_doomed hst'
    have hbc : b.2.config b.1 = ⟨b.1, f, E'.fill [.trap]⟩ := by
      rw [hb]
      simp only at hf hE'
      rw [hf, hE']
      rfl
    obtain ⟨h1, h2⟩ := ih hbc hr
    exact ⟨h1, h2.trans hs⟩

/-! ### Callout contexts -/

/-- Extend the innermost sequence of a callout context. -/
def Ctx.ext : Ctx → List Val → List Admin → Ctx
  | .top pre rest, A, B => .top (pre ++ A) (B ++ rest)
  | .label pre n cont E rest, A, B => .label pre n cont (Ctx.ext E A B) rest
  | .handler pre n cs E rest, A, B => .handler pre n cs (Ctx.ext E A B) rest
  | .frame pre n f E rest, A, B => .frame pre n f (Ctx.ext E A B) rest

theorem Ctx.fill_ext (E : Ctx) (A : List Val) (X B : List Admin) :
    E.fill (vals A ++ X ++ B) = (Ctx.ext E A B).fill X := by
  induction E with
  | top pre rest => simp [Ctx.fill, Ctx.ext, vals_append]
  | label pre n cont E rest ih => simp only [Ctx.fill, Ctx.ext, ih]
  | handler pre n cs E rest ih => simp only [Ctx.fill, Ctx.ext, ih]
  | frame pre n f E rest ih => simp only [Ctx.fill, Ctx.ext, ih]

/-- A non-value instruction keeps its kind under renaming. -/
theorem Ren.single_nonvalue (ρ : Ren) {e : Admin} (hv : e.val? = none) :
    ∃ e', ρ.code [e] = [e'] ∧ e'.val? = none ∧ (e' = .trap → e = .trap) := by
  rcases e with i | r | d | d | ⟨n, c, b⟩ | ⟨n, cs, b⟩ | ⟨n, f, b⟩ | _
  · exact ⟨.plain i, by simp, hv, by simp⟩
  · simp [Admin.val?] at hv
  · exact ⟨.callRefType d, by simp, rfl, by simp⟩
  · exact ⟨.returnCallRefType d, by simp, rfl, by simp⟩
  · exact ⟨.label n c (ρ.code b), by simp, rfl, by simp⟩
  · exact ⟨.handler n cs (ρ.code b), by simp, rfl, by simp⟩
  · exact ⟨.frame n (ρ.frame f) (ρ.code b), by simp, rfl, by simp⟩
  · exact ⟨.trap, by simp, rfl, fun _ => rfl⟩

theorem Live.ren {l : List Admin} (h : Live l) (ρ : Ren) : Live (ρ.code l) := by
  obtain ⟨W, e, R, hf, hne⟩ := h
  obtain ⟨hl, hv⟩ := fnv_eq hf
  obtain ⟨e', he', hv', ht⟩ := ρ.single_nonvalue hv
  refine ⟨W.map ρ.val, e', ρ.code R, ?_, fun h => hne (ht h)⟩
  have hcode : ρ.code l = vals (W.map ρ.val) ++ e' :: ρ.code R := by
    rw [hl, ρ.code_append, ρ.code_vals, ρ.code_cons, he']
    rfl
  rw [hcode, fnv_vals_append, fnv_cons_of_none hv']
  simp

/-! ### The backward steps of the joint machine -/

variable {S : Silmaril.Wasm.Game.Linking.Setup}

theorem active_config (s : Store Nat) (d : Config Nat) :
    (Thread.active d.frame d.code).config s = ⟨s, d.frame, d.code⟩ := rfl

/-- A `Soft` step of the shared world while the consumer runs is a consumer step. -/
theorem CRel.soft_back {St : Static S} {P : Profile} {σ π κ : Store Nat} {ts tc : Thread}
    (hR : CRel St σ ts π κ tc) {d : Config Nat} (hs : Soft P (ts.config σ) d) :
    ∃ X', InternalP P (κ, tc) (κ, .active (tc.config κ).frame X') ∧ d.store = σ ∧
      CRel St σ (.active d.frame d.code) π κ (.active (tc.config κ).frame X') := by
  obtain ⟨ρp, Op, ρc, Oc, hW, hf, hc, hts⟩ := hR
  obtain ⟨X', hstep, hd, hgood⟩ := ren_soft_back (p := κ) hs hts hf hc
  have hstep' : Step P noHost (tc.config κ) ⟨κ, (tc.config κ).frame, X'⟩ := by
    rw [Thread.config_eta κ tc]
    exact hstep
  refine ⟨X', ⟨_, _, rfl, hstep'⟩, by rw [hd], ρp, Op, ρc, Oc, hW, hf, hgood, ?_⟩
  rw [active_config, hd]
  rfl

/-- A `Soft` step of the shared world while a running provider is called is a provider step. -/
theorem PRel.soft_back {St : Static S} {P : Profile} {σ π κ : Store Nat} {ts tp tc : Thread}
    {h : Nat} {args : List Val} (hP : PRel St σ ts π tp κ tc h args)
    (hlive : Live (tp.config π).code) {d : Config Nat} (hs : Soft P (ts.config σ) d) :
    ∃ X', InternalP P (π, tp) (π, .active {} X') ∧ d.store = σ ∧
      PRel St σ (.active d.frame d.code) π (.active {} X') κ tc h args := by
  obtain ⟨ρp, Op, ρc, Oc, E, a, hW, hf, hc, hd, hF, htop, hcp, hts⟩ := hP
  obtain ⟨-, yy, -, -, -, -, -, -, -, hX⟩ := decompose?_sound hd
  have hexnc : NoExnRef ((ρc.ctx E).fill (ρc.code (vals args ++ [.ref (.func a), yy]))) := by
    rw [← Ren.code_fill, ← hX]
    exact (hc.noExnRef).ren ρc
  have hexn : NoExnRef ((ρc.ctx E).fill (ρp.code (tp.config π).code)) :=
    NoExnRef.fill hexnc ((hcp.noExnRef).ren ρp)
  rw [hts] at hs
  obtain ⟨s', Y', rfl, hY'⟩ := soft_fill (ρc.ctx E) (ρp.topOK_code htop) (hlive.ren ρp) hexn hs
  have hs' : Soft P ⟨σ, ρp.frame {}, ρp.code (tp.config π).code⟩ ⟨s', ρp.frame {}, Y'⟩ := hY' _
  obtain ⟨X', hstep, hd', hgood⟩ := ren_soft_back (p := π) hs' rfl (Op.frameGood_empty) hcp
  obtain ⟨rfl, -, rfl⟩ := Config.mk.inj hd'
  have hstep' : Step P noHost (tp.config π) ⟨π, {}, X'⟩ := by
    rw [Thread.config_eta π tp, hF]
    exact hstep
  have htop' : TopOK X' := (step_reframe hstep htop).2.1
  exact ⟨X', ⟨_, _, rfl, hstep'⟩, rfl, ρp, Op, ρc, Oc, E, a, hW, hf, hc, hd, rfl, htop', hgood,
    rfl⟩

end Silmaril.Proofs.Wasm.Game.Linking.Split
