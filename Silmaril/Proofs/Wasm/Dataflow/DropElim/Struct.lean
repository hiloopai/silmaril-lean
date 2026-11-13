module

public import Silmaril.Proofs.Wasm.Dataflow.DropElim.Match

/-!
# an earlier step of the two-pass DCE: structured heads

`erase_struct_step`: a step of `vals us ++ [i]` with `i` a `block`, `loop` or `if` is that
rule; it keeps the store, and the erased instruction takes the same rule to erased code.
`erase_struct_match` lifts it to the one-step obligation.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head famOf noHost)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Structured heads -/

/-- `block`, `loop` and `if`. -/
def IsStruct : Instr → Prop
  | .block .. | .loop .. | .if_ .. => True
  | _ => False

theorem IsStruct.val_none {i : Instr} (hi : IsStruct i) : (Admin.plain i).val? = none := by
  cases i <;> first | rfl | exact (hi : False).elim

theorem IsStruct.not_callRef {i : Instr} (hi : IsStruct i) : ¬ (Admin.plain i).IsCallRef := by
  cases i <;> first | exact (hi : False).elim | exact id

theorem Erase.StructPair.isStruct {i i' : Instr} (h : Erase.StructPair i i') : IsStruct i := by
  cases h <;> trivial

/-- No family rule steps at a structured head. -/
theorem IsStruct.not_fam {i : Instr} (hi : IsStruct i) {k : SingleThreaded.Det.Fam}
    {us : List Val} (hk : k ≠ .control)
    (h : SingleThreaded.Det.FamShape k (vals us ++ [.plain i])) : False := by
  have hf := (SingleThreaded.Det.famOf_of_shape h).2
  cases i <;> first | exact (hi : False).elim | exact hk (by rw [← hf]; rfl)

theorem IsStruct.not_fam' {i : Instr} (hi : IsStruct i) {k : SingleThreaded.Det.Fam}
    {us : List Val} {l : List Admin} (hk : k ≠ .control) (hl : l = vals us ++ [.plain i])
    (h : SingleThreaded.Det.FamShape k l) : False :=
  hi.not_fam hk (hl ▸ h)

/-- The conclusion of `erase_struct_step` for a step `c ⟶ c'` at a structured head `i`
related to `i'`: the step keeps the store, and from any store `i'` takes the same rule to
erased code. -/
def StructStep (P : Profile) (host : HostSemantics H) (us : List Val) (i' : Instr)
    (c c' : Config H) : Prop :=
  c'.store = c.store ∧ ∃ r', Erase c'.code r' ∧
    ∀ t : Store H, Step P host ⟨t, c.frame, vals us ++ [.plain i']⟩ ⟨t, c'.frame, r'⟩

/-- The structured head `i` of `vals us ++ [i]`. -/
theorem struct_head_eq {vs us : List Val} {j i : Instr} (hi : IsStruct i)
    (hc : vals vs ++ [.plain j] = vals us ++ [.plain i]) : vs = us ∧ j = i := by
  obtain ⟨h1, h2, -⟩ := Sim.vals_append_cons_inj (IsStruct.val_none (by
    rcases SingleThreaded.Det.append_singleton_inj.mp hc with ⟨-, h⟩
    exact (Admin.plain.inj h) ▸ hi)) hi.val_none hc
  exact ⟨h1, Admin.plain.inj h2⟩

theorem struct_block {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr}
    {vs : List Val} {t₁ t₂ : List Validation.CValType}
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length)
    (us : List Val) (i i' : Instr)
    (hc : vals vs ++ [.plain (.block bt body)] = vals us ++ [.plain i])
    (hi : IsStruct i) (hii' : Erase.StructPair i i') :
    StructStep P host us i' ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩
      ⟨s, f, [.label t₂.length [] (vals vs ++ expression body)]⟩ := by
  obtain ⟨rfl, rfl⟩ := struct_head_eq hi hc
  cases hii' with
  | block _ hb =>
    exact ⟨rfl, _, .label _ (cont := []) (cont' := []) .nil ((Erase.refl _).append hb),
      fun _ => .block hbt hm⟩

theorem struct_loop {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr}
    {vs : List Val} {t₁ t₂ : List Validation.CValType}
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length)
    (us : List Val) (i i' : Instr)
    (hc : vals vs ++ [.plain (.loop bt body)] = vals us ++ [.plain i])
    (hi : IsStruct i) (hii' : Erase.StructPair i i') :
    StructStep P host us i' ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩
      ⟨s, f, [.label t₁.length [.loop bt body] (vals vs ++ expression body)]⟩ := by
  obtain ⟨rfl, rfl⟩ := struct_head_eq hi hc
  cases hii' with
  | loop _ hb =>
    exact ⟨rfl, _, .label _ (cont := [.loop bt body]) (cont' := [.loop bt _])
      (Erase.cons (.loop _ hb) .nil rfl) ((Erase.refl _).append hb), fun _ => .loop hbt hm⟩

theorem struct_ifTrue {s : Store H} {f : Frame} {c : BitVec 32} {bt : BlockType}
    {b₁ b₂ : List Instr} (hc0 : c ≠ 0) (us : List Val) (i i' : Instr)
    (hc : [constI32 c, .plain (.if_ bt b₁ b₂)] = vals us ++ [.plain i])
    (hi : IsStruct i) (hii' : Erase.StructPair i i') :
    StructStep P host us i' ⟨s, f, [constI32 c, .plain (.if_ bt b₁ b₂)]⟩
      ⟨s, f, [.plain (.block bt b₁)]⟩ := by
  obtain ⟨rfl, rfl⟩ := struct_head_eq (vs := [.i32 c]) hi hc
  cases hii' with
  | if_ _ h₁ _ => exact ⟨rfl, _, .block _ h₁, fun _ => .ifTrue hc0⟩

theorem struct_ifFalse {s : Store H} {f : Frame} {bt : BlockType} {b₁ b₂ : List Instr}
    (us : List Val) (i i' : Instr)
    (hc : [constI32 0, .plain (.if_ bt b₁ b₂)] = vals us ++ [.plain i])
    (hi : IsStruct i) (hii' : Erase.StructPair i i') :
    StructStep P host us i' ⟨s, f, [constI32 0, .plain (.if_ bt b₁ b₂)]⟩
      ⟨s, f, [.plain (.block bt b₂)]⟩ := by
  obtain ⟨rfl, rfl⟩ := struct_head_eq (vs := [.i32 0]) hi hc
  cases hii' with
  | if_ _ _ h₂ => exact ⟨rfl, _, .block _ h₂, fun _ => .ifFalse⟩

/-- `Step/ctxt-instrs` at a structured head: the inner step is again at that head. -/
theorem struct_ctxt {s s' : Store H} {f f' : Frame} {vs₀ : List Val} {is is' rest : List Admin}
    (hs : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) (hne : vs₀ ≠ [] ∨ rest ≠ [])
    (ih : ∀ us i i', is = vals us ++ [.plain i] → IsStruct i → Erase.StructPair i i' →
      StructStep P host us i' ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (us : List Val) (i i' : Instr) (hc : vals vs₀ ++ is ++ rest = vals us ++ [.plain i])
    (hi : IsStruct i) (hii' : Erase.StructPair i i') :
    StructStep P host us i' ⟨s, f, vals vs₀ ++ is ++ rest⟩ ⟨s', f', vals vs₀ ++ is' ++ rest⟩ := by
  obtain ⟨u₁, b, is₁, hb, rfl⟩ := Sim.exists_head_of_not_all hs.not_all_isVal
  have hc' : vals (vs₀ ++ u₁) ++ b :: (is₁ ++ rest) = vals us ++ Admin.plain i :: [] := by
    rw [← hc]; simp
  obtain ⟨rfl, rfl, h3⟩ := Sim.vals_append_cons_inj hb hi.val_none hc'
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h3
  obtain ⟨hs', r', hr, hstep⟩ := ih u₁ i i' rfl hi hii'
  refine ⟨hs', vals vs₀ ++ r' ++ [], ((Erase.refl _).append hr).append .nil, fun t => ?_⟩
  simpa using Step.ctxtInstrs (vs := vs₀) (rest := []) (hstep t) hne

/-- An administrative instruction that is not a structured instruction. -/
def NotStructAdmin (a : Admin) : Prop := ∀ i, a = .plain i → ¬ IsStruct i

theorem notStruct_of_callRef {c : Admin} (h : c.IsCallRef) : NotStructAdmin c := by
  rintro i rfl hi
  exact hi.not_callRef h

/-- A code whose last instruction is not structured does not end in `i`. -/
theorem IsStruct.last_absurd {i : Instr} (hi : IsStruct i) {l : List Admin} {us : List Val}
    (hc : l = vals us ++ [.plain i]) (hn : ∀ a ∈ l.getLast?, NotStructAdmin a) : False :=
  hn _ (by simp [hc]) i rfl hi

theorem struct_trap_absurd {s : Store H} {f : Frame} {vs : List Val} {rest : List Admin}
    {c' : Config H} (us : List Val) (i i' : Instr)
    (hc : vals vs ++ [.trap] ++ rest = vals us ++ [.plain i]) (hi : IsStruct i)
    (_ : Erase.StructPair i i') : StructStep P host us i' ⟨s, f, vals vs ++ [.trap] ++ rest⟩ c' :=
  absurd (Sim.vals_append_cons_inj rfl hi.val_none (by simpa using hc)).2.1 (by simp)

theorem struct_throw_absurd {s : Store H} {f : Frame} {vs : List Val} {a : Nat}
    {rest : List Admin} {c' : Config H} (us : List Val) (i i' : Instr)
    (hc : vals vs ++ throwing a ++ rest = vals us ++ [.plain i]) (hi : IsStruct i)
    (_ : Erase.StructPair i i') :
    StructStep P host us i' ⟨s, f, vals vs ++ throwing a ++ rest⟩ c' := by
  have hc' : vals (vs ++ [.ref (.exn a)]) ++ Admin.plain .throwRef :: rest =
      vals us ++ Admin.plain i :: [] := by
    rw [← hc]
    simp [vals, throwing, Val.toAdmin]
  have he : Admin.plain .throwRef = .plain i := (Sim.vals_append_cons_inj rfl hi.val_none hc').2.1
  cases he
  exact (hi : False).elim

/-- **Structured redexes.** A step of `vals us ++ [i]` with `i` structured is the
`block`/`loop`/`if` rule. It keeps the store, and the same rule applies to the erased `i'`
on any store, with erased results. -/
theorem erase_struct_step {c c' : Config H} (h : Step P host c c') :
    ∀ (us : List Val) (i i' : Instr), c.code = vals us ++ [.plain i] → IsStruct i →
      Erase.StructPair i i' → StructStep P host us i' c c' := by
  induction h with
  | ctxtInstrs hs hne ih => exact struct_ctxt hs hne ih
  | block hbt hm => exact struct_block hbt hm
  | loop hbt hm => exact struct_loop hbt hm
  | ifTrue hc0 => exact struct_ifTrue hc0
  | ifFalse => exact struct_ifFalse
  | parametric hp => exact fun _ _ _ hc hi _ =>
    (hi.not_fam' (by decide) hc (SingleThreaded.Det.ParametricStep.shape hp)).elim
  | numeric hp => exact fun _ _ _ hc hi _ =>
    (hi.not_fam' (by decide) hc (SingleThreaded.Det.NumericStep.shape hp)).elim
  | vector hp => exact fun _ _ _ hc hi _ =>
    (hi.not_fam' (by decide) hc (SingleThreaded.Det.VectorStep.shape hp)).elim
  | «variable» hp => exact fun _ _ _ hc hi _ =>
    (hi.not_fam' (by decide) hc (SingleThreaded.Det.VariableStep.shape hp)).elim
  | table hp => exact fun _ _ _ hc hi _ =>
    (hi.not_fam' (by decide) hc (SingleThreaded.Det.TableStep.shape hp)).elim
  | memory hp => exact fun _ _ _ hc hi _ =>
    (hi.not_fam' (by decide) hc (SingleThreaded.Det.MemoryStep.shape hp)).elim
  | reference hp => exact fun _ _ _ hc hi _ =>
    (hi.not_fam' (by decide) hc (SingleThreaded.Det.RefStep.shape hp)).elim
  | aggregate hp => exact fun _ _ _ hc hi _ =>
    (hi.not_fam' (by decide) hc (SingleThreaded.Det.AggregateStep.shape hp)).elim
  | trapInstrs _ => exact struct_trap_absurd
  | throwRefInstrs _ => exact struct_throw_absurd
  | callRefNull hcall => exact fun _ _ _ hc hi _ =>
    (hi.last_absurd hc (by simpa using notStruct_of_callRef hcall)).elim
  | callRefFunc hcall => exact fun _ _ _ hc hi _ =>
    (hi.last_absurd hc (by simpa using notStruct_of_callRef hcall)).elim
  | callRefHost hcall => exact fun _ _ _ hc hi _ =>
    (hi.last_absurd hc (by simpa using notStruct_of_callRef hcall)).elim
  | callRefHostDiv hcall => exact fun _ _ _ hc hi _ =>
    (hi.last_absurd hc (by simpa using notStruct_of_callRef hcall)).elim
  | _ => exact fun _ _ _ hc hi _ => (hi.last_absurd hc
    (by simp [NotStructAdmin, IsStruct, constI32, Val.i32, Val.toAdmin])).elim

/-- A structured erasure matches a head step in one target step. -/
theorem erase_struct_match {s s' : Store H} {f f' : Frame} {vs : List Val} {i i' : Instr}
    {rest rest' es' : List Admin} (hi : Erase.StructPair i i') (hr : Erase rest rest')
    (h : Step P host ⟨s, f, vals vs ++ [.plain i] ++ rest⟩ ⟨s', f', es'⟩) :
    EraseMatched P host ⟨s, f, vals vs ++ [.plain i] ++ rest⟩ ⟨s', f', es'⟩
      ⟨s, f, vals vs ++ [.plain i'] ++ rest'⟩ := by
  have his : IsStruct i := hi.isStruct
  have hs : Step P host ⟨s, f, vals vs ++ Admin.plain i :: rest⟩ ⟨s', f', es'⟩ := by simpa using h
  rcases Sim.Step.split_head his.val_none hs with ⟨ws, us, is', rfl, hh, rfl⟩ |
      ⟨he, _⟩ | ⟨he, _⟩
  · obtain ⟨hstore, code, hcode, hstep⟩ := erase_struct_step hh us i i' rfl his hi
    have hstore' : s' = s := hstore
    subst hstore'
    refine ⟨⟨_, f', vals ws ++ code ++ rest'⟩, ⟨rfl, rfl, ((Erase.refl _).append hcode).append hr⟩,
      .inl (.single ?_)⟩
    simpa using Sim.Step.append_right (Sim.Step.vals_left (hstep _) ws) rest'
  · cases he
  · cases he
    exact (his : False).elim

end Silmaril.Wasm.Dataflow
