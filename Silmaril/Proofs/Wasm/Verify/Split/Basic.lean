module

public import Silmaril.Wasm.Verify.Split.Defs
public import Silmaril.Proofs.Wasm.Verify.Reach.Plays

/-!
# Escaping references: basic lemmas

`LooseIn` over appended code (`looseIn_append`: the left part is followed by the head of the
right part), monotonicity in the flag (`LooseIn.mono`), values (`looseIn_vals_append`), code
whose references are all in `V` (`looseIn_of_codeIn`), and replacement of the redex of an
evaluation context (`LooseIn.fill`). The instruction predicate `PlVC V C fs` meets the
requirements of the reachability invariant at `C` (`plVC_plainOK`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Validation

variable {V C : Nat → Prop} {fs : List Nat}

/-! ## `nextCall` -/

@[simp] theorem nextCall_nil (b : Bool) : nextCall b [] = b := rfl
@[simp] theorem nextCall_cons (b : Bool) (x : Admin) (l : List Admin) :
    nextCall b (x :: l) = callAdm x := rfl

theorem nextCall_append (b : Bool) (l₁ l₂ : List Admin) :
    nextCall b (l₁ ++ l₂) = nextCall (nextCall b l₂) l₁ := by
  cases l₁ <;> rfl

@[simp] theorem callAdm_toAdmin (v : Val) : callAdm v.toAdmin = false := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

theorem nextCall_vals_append {b : Bool} {l : List Admin} (h : nextCall b l = false)
    (vs : List Val) : nextCall b (vals vs ++ l) = false := by
  cases vs with
  | nil => simpa [vals] using h
  | cons v vs => simp [vals]

/-! ## `LooseIn` -/

@[simp] theorem looseIn_nil (b : Bool) : LooseIn V b [] := by
  simp [LooseIn]

@[simp] theorem looseIn_ref (b : Bool) (r : Ref) (l : List Admin) :
    LooseIn V b (.ref r :: l) ↔ (RefIn V r ∨ nextCall b l = true) ∧ LooseIn V b l := by
  simp [LooseIn]

@[simp] theorem looseIn_plain (b : Bool) (i : Instr) (l : List Admin) :
    LooseIn V b (.plain i :: l) ↔ LooseIn V b l := by
  simp [LooseIn]

@[simp] theorem looseIn_callRefType (b : Bool) (d : DefType) (l : List Admin) :
    LooseIn V b (.callRefType d :: l) ↔ LooseIn V b l := by
  simp [LooseIn]

@[simp] theorem looseIn_returnCallRefType (b : Bool) (d : DefType) (l : List Admin) :
    LooseIn V b (.returnCallRefType d :: l) ↔ LooseIn V b l := by
  simp [LooseIn]

@[simp] theorem looseIn_trap (b : Bool) (l : List Admin) :
    LooseIn V b (.trap :: l) ↔ LooseIn V b l := by
  simp [LooseIn]

@[simp] theorem looseIn_label (b : Bool) (n : Nat) (cont : List Instr) (body l : List Admin) :
    LooseIn V b (.label n cont body :: l) ↔ LooseIn V false body ∧ LooseIn V b l := by
  simp [LooseIn]

@[simp] theorem looseIn_handler (b : Bool) (n : Nat) (cs : List Catch) (body l : List Admin) :
    LooseIn V b (.handler n cs body :: l) ↔ LooseIn V false body ∧ LooseIn V b l := by
  simp [LooseIn]

@[simp] theorem looseIn_frame (b : Bool) (n : Nat) (fr : Frame) (body l : List Admin) :
    LooseIn V b (.frame n fr body :: l) ↔ LocalsIn V fr ∧ LooseIn V false body ∧ LooseIn V b l := by
  simp [LooseIn]

/-- **`LooseIn` of appended code**: the left part is followed by the head of the right part. -/
theorem looseIn_append (b : Bool) (l₁ l₂ : List Admin) :
    LooseIn V b (l₁ ++ l₂) ↔ LooseIn V (nextCall b l₂) l₁ ∧ LooseIn V b l₂ := by
  induction l₁ with
  | nil => simp
  | cons x l₁ ih =>
    have hn : nextCall b (l₁ ++ l₂) = nextCall (nextCall b l₂) l₁ := nextCall_append b l₁ l₂
    cases x <;> simp only [List.cons_append, looseIn_ref, looseIn_plain, looseIn_callRefType,
      looseIn_returnCallRefType, looseIn_trap, looseIn_label, looseIn_handler, looseIn_frame,
      ih, hn, and_assoc]

/-- A stronger flag (followed by a call) asks less. -/
theorem LooseIn.mono {b : Bool} : ∀ {l : List Admin}, LooseIn V false l → LooseIn V b l
  | [], _ => looseIn_nil b
  | .ref r :: l, h => by
    rw [looseIn_ref] at h ⊢
    refine ⟨?_, LooseIn.mono h.2⟩
    cases l with
    | nil => exact .inl (h.1.resolve_right (by simp))
    | cons y l => exact h.1
  | .label _ _ _ :: _, h => by
    rw [looseIn_label] at h ⊢
    exact ⟨h.1, LooseIn.mono h.2⟩
  | .handler _ _ _ :: _, h => by
    rw [looseIn_handler] at h ⊢
    exact ⟨h.1, LooseIn.mono h.2⟩
  | .frame _ _ _ :: _, h => by
    rw [looseIn_frame] at h ⊢
    exact ⟨h.1, h.2.1, LooseIn.mono h.2.2⟩
  | .plain _ :: _, h => by
    rw [looseIn_plain] at h ⊢
    exact LooseIn.mono h
  | .callRefType _ :: _, h => by
    rw [looseIn_callRefType] at h ⊢
    exact LooseIn.mono h
  | .returnCallRefType _ :: _, h => by
    rw [looseIn_returnCallRefType] at h ⊢
    exact LooseIn.mono h
  | .trap :: _, h => by
    rw [looseIn_trap] at h ⊢
    exact LooseIn.mono h

theorem nextCall_vals_false (vs : List Val) : nextCall false (vals vs) = false := by
  cases vs <;> simp [vals]

theorem looseIn_vals_false (vs : List Val) :
    LooseIn V false (vals vs) ↔ ∀ r, Val.ref r ∈ vs → RefIn V r := by
  induction vs with
  | nil => simp [vals]
  | cons v vs ih =>
    have hn : nextCall false (vals vs) = false := nextCall_vals_false vs
    have hv : vals (v :: vs) = v.toAdmin :: vals vs := rfl
    rw [hv]
    rcases v with ⟨⟨_ | _⟩, _⟩ | _ | r <;>
      simp only [Val.toAdmin, looseIn_plain, looseIn_ref, ih, hn, Bool.false_eq_true, or_false,
        List.mem_cons, reduceCtorEq, false_or, forall_eq_or_imp, Val.ref.injEq]

/-- Values followed by code that does not start with a call. -/
theorem looseIn_vals_append {b : Bool} {l : List Admin} (h : nextCall b l = false)
    (vs : List Val) :
    LooseIn V b (vals vs ++ l) ↔ (∀ r, Val.ref r ∈ vs → RefIn V r) ∧ LooseIn V b l := by
  rw [looseIn_append, h, looseIn_vals_false]

/-- Values whose references are in `V`, followed by any code. -/
theorem LooseIn.vals_append {b : Bool} {vs : List Val} (hv : ∀ r, Val.ref r ∈ vs → RefIn V r)
    {l : List Admin} (hl : LooseIn V b l) : LooseIn V b (vals vs ++ l) :=
  (looseIn_append b _ l).2 ⟨LooseIn.mono ((looseIn_vals_false vs).2 hv), hl⟩

/-- Code made of values (followed by anything) has its references in `V`. -/
theorem LooseIn.vals_refs {b : Bool} {vs : List Val} {l : List Admin}
    (h : LooseIn V b (vals vs ++ l)) (hl : nextCall b l = false) :
    ∀ r, Val.ref r ∈ vs → RefIn V r :=
  ((looseIn_vals_append hl vs).1 h).1

/-- **Code whose references are all in `V`** and whose frames' locals are in `V`. -/
theorem looseIn_of_refs : ∀ (b : Bool) (l : List Admin), (∀ r ∈ codeRefs l, RefIn V r) →
    (∀ fr ∈ codeFrames l, LocalsIn V fr) → LooseIn V b l
  | b, [], _, _ => looseIn_nil b
  | b, .ref r :: l, hr, hf => (looseIn_ref b r l).2
    ⟨.inl (hr r (by simp)), looseIn_of_refs b l (fun r' h => hr r' (by simp [h]))
      (fun fr h => hf fr (by simpa using h))⟩
  | b, .label _ _ body :: l, hr, hf => (looseIn_label ..).2
    ⟨looseIn_of_refs false body (fun r' h => hr r' (by simp [h]))
        (fun fr h => hf fr (by simp [h])),
      looseIn_of_refs b l (fun r' h => hr r' (by simp [h])) (fun fr h => hf fr (by simp [h]))⟩
  | b, .handler _ _ body :: l, hr, hf => (looseIn_handler ..).2
    ⟨looseIn_of_refs false body (fun r' h => hr r' (by simp [h]))
        (fun fr h => hf fr (by simp [h])),
      looseIn_of_refs b l (fun r' h => hr r' (by simp [h])) (fun fr h => hf fr (by simp [h]))⟩
  | b, .frame _ f body :: l, hr, hf => (looseIn_frame ..).2
    ⟨hf f (by simp), looseIn_of_refs false body (fun r' h => hr r' (by simp [h]))
        (fun fr h => hf fr (by simp [h])),
      looseIn_of_refs b l (fun r' h => hr r' (by simp [h])) (fun fr h => hf fr (by simp [h]))⟩
  | b, .plain _ :: l, hr, hf => (looseIn_plain ..).2 <|
    looseIn_of_refs b l (fun r' h => hr r' (by simpa using h))
      (fun fr h => hf fr (by simpa using h))
  | b, .callRefType _ :: l, hr, hf => (looseIn_callRefType ..).2 <|
    looseIn_of_refs b l (fun r' h => hr r' (by simpa using h))
      (fun fr h => hf fr (by simpa using h))
  | b, .returnCallRefType _ :: l, hr, hf => (looseIn_returnCallRefType ..).2 <|
    looseIn_of_refs b l (fun r' h => hr r' (by simpa using h))
      (fun fr h => hf fr (by simpa using h))
  | b, .trap :: l, hr, hf => (looseIn_trap ..).2 <|
    looseIn_of_refs b l (fun r' h => hr r' (by simpa using h))
      (fun fr h => hf fr (by simpa using h))

/-- Code satisfying the reachability invariant at `V` satisfies `LooseIn V`. -/
theorem looseIn_of_codeIn {Pl : Instr → Prop} {l : List Admin} (h : CodeIn V fs Pl l) (b : Bool) :
    LooseIn V b l :=
  looseIn_of_refs b l h.1 fun fr hf => (h.2.1 fr hf).2

theorem LocalsIn.of_frameIn {fr : Frame} (h : FrameIn V fs fr) : LocalsIn V fr := h.2

/-- **The reachability invariant at `V`, from `LooseIn`** for code with no transient
reference: values followed by a source instruction. -/
theorem codeIn_of_looseIn {Pl : Instr → Prop} {b : Bool} {vs : List Val} {i : Instr}
    (h : LooseIn V b (vals vs ++ [.plain i])) (hi : PlOK Pl i) :
    CodeIn V fs Pl (vals vs ++ [.plain i]) :=
  CodeIn.vals_append (h.vals_refs rfl) ⟨by simp, by simp, by simpa using hi⟩

/-! ## Evaluation contexts -/

/-- **Replacing the redex of an evaluation context**: if the redex `X` does not start with a
call instruction, the code `E.fill Y` keeps `LooseIn` for any `Y` with `LooseIn V false Y`. -/
theorem LooseIn.fill {X Y : List Admin} (hX : ∀ b, nextCall b X = false)
    (hY : LooseIn V false Y) : ∀ (E : Ctx) {b : Bool}, LooseIn V b (E.fill X) →
      LooseIn V b (E.fill Y)
  | .top pre rest, b, h => by
    simp only [Ctx.fill, List.append_assoc] at h ⊢
    have h₁ := (looseIn_append b (vals pre) (X ++ rest)).1 h
    have h₂ := (looseIn_append b X rest).1 h₁.2
    rw [nextCall_append, hX] at h₁
    refine (looseIn_append b _ _).2 ⟨LooseIn.mono h₁.1, (looseIn_append b _ _).2
      ⟨LooseIn.mono hY, h₂.2⟩⟩
  | .label pre n cont E rest, b, h => by
    simp only [Ctx.fill] at h ⊢
    have h₁ := (looseIn_append b _ rest).1 h
    have h₂ := (looseIn_append _ (vals pre) _).1 h₁.1
    simp only [looseIn_label, looseIn_nil, and_true] at h₂
    refine (looseIn_append b _ rest).2 ⟨(looseIn_append _ _ _).2 ⟨h₂.1, ?_⟩, h₁.2⟩
    simp only [looseIn_label, looseIn_nil, and_true]
    exact LooseIn.fill hX hY E h₂.2
  | .handler pre n cs E rest, b, h => by
    simp only [Ctx.fill] at h ⊢
    have h₁ := (looseIn_append b _ rest).1 h
    have h₂ := (looseIn_append _ (vals pre) _).1 h₁.1
    simp only [looseIn_handler, looseIn_nil, and_true] at h₂
    refine (looseIn_append b _ rest).2 ⟨(looseIn_append _ _ _).2 ⟨h₂.1, ?_⟩, h₁.2⟩
    simp only [looseIn_handler, looseIn_nil, and_true]
    exact LooseIn.fill hX hY E h₂.2
  | .frame pre n f E rest, b, h => by
    simp only [Ctx.fill] at h ⊢
    have h₁ := (looseIn_append b _ rest).1 h
    have h₂ := (looseIn_append _ (vals pre) _).1 h₁.1
    simp only [looseIn_frame, looseIn_nil, and_true] at h₂
    refine (looseIn_append b _ rest).2 ⟨(looseIn_append _ _ _).2 ⟨h₂.1, ?_⟩, h₁.2⟩
    simp only [looseIn_frame, looseIn_nil, and_true]
    exact ⟨h₂.2.1, LooseIn.fill hX hY E h₂.2.2⟩

/-! ## The instruction predicate -/

theorem mem_exprRefFuncs {b : List Instr} {i : Instr} (hi : i ∈ b) {x : Nat}
    (hx : x ∈ instrRefFuncs i) : x ∈ exprRefFuncs b := by
  induction b with
  | nil => cases hi
  | cons j b ih =>
    rw [exprRefFuncs, List.mem_append]
    rcases List.mem_cons.1 hi with rfl | hi
    · exact .inl hx
    · exact .inr (ih hi)

theorem RefFuncIn.of_expr {b : List Instr}
    (h : ∀ x ∈ exprRefFuncs b, ∀ a, fs[x]? = some a → V a) : ∀ i ∈ b, RefFuncIn V fs i :=
  fun _ hi x hx => h x (mem_exprRefFuncs hi hx)

theorem PlVC.body {i₀ : Instr} {b : List Instr} (hrf : instrRefFuncs i₀ = exprRefFuncs b)
    (hin : InstrIn C fs i₀ → ∀ i ∈ b, InstrIn C fs i) (h : PlVC V C fs i₀) :
    ∀ i ∈ b, PlOK (PlVC V C fs) i :=
  fun i hi => .inr ⟨hin h.1 i hi, RefFuncIn.of_expr (by rw [← hrf]; exact h.2) i hi⟩

/-- `PlVC V C fs` meets the requirements of the reachability invariant at `C`. -/
theorem plVC_plainOK : PlainOK C (fun _ => False) fs (PlVC V C fs) where
  block _ _ h := PlVC.body (by simp [instrRefFuncs]) InstrIn.block h
  loop _ _ h := PlVC.body (by simp [instrRefFuncs]) InstrIn.loop h
  tryTable _ _ _ h := PlVC.body (by simp [instrRefFuncs]) InstrIn.tryTable h
  ifLeft _ _ _ h := .inr ⟨InstrIn.if_left h.1, fun x hx a ha =>
    h.2 x (by simp only [instrRefFuncs, List.mem_append] at hx ⊢; exact .inl hx) a ha⟩
  ifRight _ _ _ h := .inr ⟨InstrIn.if_right h.1, fun x hx a ha =>
    h.2 x (by simp only [instrRefFuncs, List.mem_append] at hx ⊢; exact .inr hx) a ha⟩
  call _ a h ha := .inl (h.1 _ (by simp [instrCallees]) a ha)
  returnCall _ a h ha := h.1 _ (by simp [instrCallees]) a ha
  refFunc _ a h ha := h.1 _ (by simp [instrCallees]) a ha

/-! ## Monotonicity in the sets -/

theorem RefIn.mono {G G' : Nat → Prop} (hG : ∀ a, G a → G' a) {r : Ref} (h : RefIn G r) :
    RefIn G' r :=
  fun a ha => hG a (h a ha)

theorem StoreIn.mono {H : Type} {G G' : Nat → Prop} (hG : ∀ a, G a → G' a) {s : Store H}
    (h : StoreIn G s) : StoreIn G' s where
  globals g hg r hr := (h.globals g hg r hr).mono hG
  tables t ht r hr := (h.tables t ht r hr).mono hG
  elems e he r hr := (h.elems e he r hr).mono hG
  structs si hsi r hr := (h.structs si hsi r hr).mono hG
  arrays ai hai r hr := (h.arrays ai hai r hr).mono hG
  exns e he r hr := (h.exns e he r hr).mono hG

theorem HostIn.mono {H : Type} {G G' : Nat → Prop} (hG : ∀ a, G a → G' a)
    {host : HostSemantics H} (h : HostIn G host) : HostIn G' host := by
  intro hh s vs s' r hr
  obtain ⟨h₁, h₂⟩ := h hh s vs s' r hr
  exact ⟨h₁, fun x hx => (h₂ x hx).mono hG⟩

end Silmaril.Wasm.Verify
