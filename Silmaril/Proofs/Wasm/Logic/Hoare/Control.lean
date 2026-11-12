module

public import Silmaril.Proofs.Wasm.Logic.Hoare.Instr

/-!
# The every-run logic: structured control and exceptions

`block`, `loop` (partial correctness with an invariant, by induction on the step
index), `if`, `br_if`, `br_on_null`, `throw` and `try_table`, each as an instance
of `Safe.head`, entering `Safe.label`/`Safe.handler` and composed with what
follows by `Safe.seq`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det (Head famOf famOf_of_shape)
open Silmaril.Wasm.Logic.Core (Outcome Post handlerPost catchPost caughtPost)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Close a `Det.Head` case whose instruction is not the one at hand. -/
local macro "head_absurd" : tactic => `(tactic| (exfalso; first
  | exact absurd (famOf_of_shape (SingleThreaded.Det.ParametricStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.NumericStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.VectorStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.VariableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.TableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.MemoryStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.RefStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.AggregateStep.shape ‹_›)).2 (by simp [famOf])
  | (simp only [Admin.IsCallRef, Admin.IsReturnCallRef] at *; done)))

/-! ## Postconditions under monotone maps -/

theorem prePost_mono {us : List Val} {Q Q' : Post H} (hQ : ∀ s f o, Q s f o → Q' s f o)
    {s : Store H} {f : Frame} {o : Outcome} (h : prePost us Q s f o) : prePost us Q' s f o :=
  hQ _ _ _ h

theorem catchPost_mono {Q Q' : Post H} (hQ : ∀ s f o, Q s f o → Q' s f o) {s : Store H}
    {f : Frame} {a : Nat} : ∀ {cs : List Catch}, catchPost s f a Q cs → catchPost s f a Q' cs
  | [], h => hQ _ _ _ h
  | c :: _, .inl ⟨hm, hc⟩ => .inl ⟨hm, caught_mono c hc⟩
  | _ :: _, .inr ⟨hm, hcs⟩ => .inr ⟨hm, catchPost_mono hQ hcs⟩
where
  caught_mono (c : Catch) (h : caughtPost s f a Q c) : caughtPost s f a Q' c := by
    rcases c with ⟨x, l⟩ | ⟨x, l⟩ | l | l
    · obtain ⟨e, he, hq⟩ := h
      exact ⟨e, he, hQ _ _ _ hq⟩
    · obtain ⟨e, he, hq⟩ := h
      exact ⟨e, he, hQ _ _ _ hq⟩
    · exact hQ _ _ _ h
    · exact hQ _ _ _ h

theorem handlerPost_mono {cs : List Catch} {Q Q' : Post H} (hQ : ∀ s f o, Q s f o → Q' s f o)
    {s : Store H} {f : Frame} {o : Outcome} (h : handlerPost cs Q s f o) : handlerPost cs Q' s f o := by
  cases o with
  | throw a => exact catchPost_mono hQ h
  | _ => exact hQ _ _ _ h

/-- `labelPost` to `labelPostK`, through a monotone map of the postcondition. -/
theorem labelPost.toK' {m : Nat} {cont : List Instr} {us : List Val} {Q Q' : Post H} (k : Nat)
    (hQ : ∀ s f o, Q s f o → Q' s f o) {s : Store H} {f : Frame} {o : Outcome}
    (h : labelPost P host m cont us Q s f o) : labelPostK P host m cont us Q' k s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, c⟩
  · exact hQ _ _ _ h
  · obtain ⟨vs₁, vs₂, he, hn, hw⟩ := h
    exact ⟨vs₁, vs₂, he, hn, (hw k).post_mono hQ⟩
  all_goals exact hQ _ _ _ h

/-! ## Blocks -/

/-- **`block`.** -/
theorem Safe.block {n k : Nat} {s : Store H} {f : Frame} {us vs : List Val} {bt : BlockType}
    {body : List Instr} {rest : List Admin} {Q : Post H} {t₁ t₂ : List CValType} (hk : n ≤ k)
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hn : vs.length = t₁.length)
    (h : Safe P host (labelPostK P host t₂.length [] us (seqPostK P host rest Q k) k) n
      ⟨s, f, vals vs ++ expression body⟩) :
    Safe P host Q (n + 1) ⟨s, f, vals (us ++ vs) ++ .plain (.block bt body) :: rest⟩ := by
  refine Safe.head ⟨rfl, by simp, rfl⟩ ⟨us, vs, _, rfl, .block hbt hn⟩ ?_
  intro us' args c₀ hW hh
  obtain ⟨t₁', t₂', hbt', hn', rfl⟩ := SingleThreaded.head_block hh
  obtain ⟨rfl, rfl⟩ : t₁' = t₁ ∧ t₂' = t₂ := by simpa [hbt] using hbt'.symm
  obtain ⟨rfl, rfl⟩ := split_args hW (hn'.trans hn.symm)
  exact Safe.seq hk (Safe.label (by omega) h)

theorem HWP.block {s : Store H} {f : Frame} {us vs : List Val} {bt : BlockType}
    {body : List Instr} {rest : List Admin} {Q : Post H} {t₁ t₂ : List CValType}
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hn : vs.length = t₁.length)
    (h : HWP P host s f (vals vs ++ expression body) (labelPost P host t₂.length [] us (seqPost P host rest Q))) :
    HWP P host s f (vals (us ++ vs) ++ .plain (.block bt body) :: rest) Q
  | 0 => trivial
  | n + 1 => Safe.block le_rfl hbt hn
      ((h n).post_mono fun _ _ _ => labelPost.toK' n fun _ _ _ => seqPost.toK n)

/-! ## Loops -/

theorem head_loop {s : Store H} {f : Frame} {args : List Val} {bt : BlockType} {body : List Instr}
    {c₀ : Config H} (h : Head P s f args (.plain (.loop bt body)) c₀) :
    ∃ t₁ t₂, f.module.blockType? bt = some (t₁, t₂) ∧ args.length = t₁.length ∧
      c₀ = ⟨s, f, [.label t₁.length [.loop bt body] (vals args ++ expression body)]⟩ := by
  cases h with
  | loop hbt hm => exact ⟨_, _, hbt, hm, rfl⟩
  | _ => head_absurd

/-- What a loop body may end with: a branch to the loop's own label re-enters the
loop, so the top `n` values must satisfy the invariant; everything else leaves
the loop. -/
def loopPost (n : Nat) (us : List Val) (Inv : Store H → Frame → List Val → Prop) (Q : Post H) :
    Post H := fun s f o =>
  match o with
  | .normal vs => Q s f (.normal (us ++ vs))
  | .br 0 vs => ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧ vs₂.length = n ∧ Inv s f vs₂
  | .br (l + 1) vs => Q s f (.br l (us ++ vs))
  | .ret vs => Q s f (.ret (us ++ vs))
  | .trap => Q s f .trap
  | .throw a => Q s f (.throw a)
  | .tail vs a c => Q s f (.tail (us ++ vs) a c)

theorem loopPost.toK {m k : Nat} {us : List Val} {Inv : Store H → Frame → List Val → Prop}
    {Q : Post H} {bt : BlockType} {body : List Instr}
    (ih : ∀ s f vs, Inv s f vs → Safe P host Q k ⟨s, f, vals (us ++ vs) ++ [.plain (.loop bt body)]⟩)
    {s : Store H} {f : Frame} {o : Outcome} (h : loopPost m us Inv Q s f o) :
    labelPostK P host m [.loop bt body] us Q k s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, c⟩
  · exact h
  · obtain ⟨vs₁, vs₂, he, hn, hi⟩ := h
    exact ⟨vs₁, vs₂, he, hn, by simpa [expression] using ih s f vs₂ hi⟩
  all_goals exact h

/-- One unfolding of a loop, given the loop for fewer steps. -/
theorem Safe.loop_step {n : Nat} {us : List Val} {Inv : Store H → Frame → List Val → Prop}
    {Q : Post H} {bt : BlockType} {body : List Instr} {t₁ t₂ : List CValType}
    (hbt : ∀ s f vs, Inv s f vs → f.module.blockType? bt = some (t₁, t₂))
    (hn : ∀ s f vs, Inv s f vs → vs.length = t₁.length)
    (hbody : ∀ s f vs, Inv s f vs →
      HWP P host s f (vals vs ++ expression body) (loopPost t₁.length us Inv Q))
    (ih : ∀ s f vs, Inv s f vs → Safe P host Q n ⟨s, f, vals (us ++ vs) ++ [.plain (.loop bt body)]⟩)
    {s : Store H} {f : Frame} {vs : List Val} (hi : Inv s f vs) :
    Safe P host Q (n + 1) ⟨s, f, vals (us ++ vs) ++ [.plain (.loop bt body)]⟩ := by
  refine Safe.head ⟨rfl, by simp, rfl⟩ ⟨us, vs, _, rfl, .loop (hbt s f vs hi) (hn s f vs hi)⟩ ?_
  intro us' args c₀ hW hh
  obtain ⟨t₁', t₂', hbt', hn', rfl⟩ := head_loop hh
  obtain ⟨rfl, rfl⟩ : t₁' = t₁ ∧ t₂' = t₂ := by simpa [hbt s f vs hi] using hbt'.symm
  obtain ⟨rfl, rfl⟩ := split_args hW (hn'.trans (hn s f vs hi).symm)
  cases n with
  | zero => trivial
  | succ m =>
    have hb : Safe P host (labelPostK P host t₁'.length [.loop bt body] us' Q m) (m + 1)
        ⟨s, f, vals args ++ expression body⟩ :=
      (hbody s f args hi (m + 1)).post_mono fun _ _ _ =>
        loopPost.toK fun s f vs h => (ih s f vs h).mono (Nat.le_succ m)
    simpa using Safe.label (us := us') (k := m) le_rfl hb

/-- **`loop`** (partial correctness): an invariant on the loop's parameters that
the body re-establishes at every branch back to the loop. -/
theorem HWP.loop {us : List Val} {Inv : Store H → Frame → List Val → Prop} {Q : Post H}
    {bt : BlockType} {body : List Instr} {t₁ t₂ : List CValType}
    (hbt : ∀ s f vs, Inv s f vs → f.module.blockType? bt = some (t₁, t₂))
    (hn : ∀ s f vs, Inv s f vs → vs.length = t₁.length)
    (hbody : ∀ s f vs, Inv s f vs →
      HWP P host s f (vals vs ++ expression body) (loopPost t₁.length us Inv Q))
    {s : Store H} {f : Frame} {vs : List Val} (hi : Inv s f vs) :
    HWP P host s f (vals (us ++ vs) ++ [.plain (.loop bt body)]) Q := by
  intro n
  induction n generalizing s f vs with
  | zero => trivial
  | succ n ih => exact Safe.loop_step hbt hn hbody (fun s f vs h => ih h) hi

/-! ## Conditionals -/

theorem i32_inj {c c' : BitVec 32} (h : Val.i32 c = .num ⟨.int .i32, c'⟩) : c' = c :=
  (numVal_int_inj (Val.num.inj h)).symm

theorem head_if {s : Store H} {f : Frame} {args : List Val} {bt : BlockType} {b₁ b₂ : List Instr}
    {c₀ : Config H} (h : Head P s f args (.plain (.if_ bt b₁ b₂)) c₀) :
    ∃ c : BitVec 32, args = [.num ⟨.int .i32, c⟩] ∧
      ((c ≠ 0 ∧ c₀ = ⟨s, f, [.plain (.block bt b₁)]⟩) ∨ (c = 0 ∧ c₀ = ⟨s, f, [.plain (.block bt b₂)]⟩)) := by
  cases h with
  | ifTrue hc => exact ⟨_, rfl, .inl ⟨hc, rfl⟩⟩
  | ifFalse hc => exact ⟨_, rfl, .inr ⟨hc, rfl⟩⟩
  | _ => head_absurd

/-- **`if`.** -/
theorem HWP.if_ {s : Store H} {f : Frame} {us : List Val} {c : BitVec 32} {bt : BlockType}
    {b₁ b₂ : List Instr} {rest : List Admin} {Q : Post H}
    (h₁ : c ≠ 0 → HWP P host s f (vals us ++ .plain (.block bt b₁) :: rest) Q)
    (h₂ : c = 0 → HWP P host s f (vals us ++ .plain (.block bt b₂) :: rest) Q) :
    HWP P host s f (vals (us ++ [.i32 c]) ++ .plain (.if_ bt b₁ b₂) :: rest) Q := by
  have hp : ∃ vs args c₀, us ++ [Val.i32 c] = vs ++ args ∧
      Head P s f args (.plain (.if_ bt b₁ b₂)) c₀ := by
    by_cases hc : c = 0
    · exact ⟨us, _, _, rfl, .ifFalse hc⟩
    · exact ⟨us, _, _, rfl, .ifTrue hc⟩
  refine HWP.head ⟨rfl, by simp, rfl⟩ hp ?_
  intro us' args c₀ hW hh
  obtain ⟨c', rfl, ⟨hc, rfl⟩ | ⟨hc, rfl⟩⟩ := head_if hh <;>
    obtain ⟨rfl, hv⟩ := split_one hW <;> obtain rfl := i32_inj hv.symm
  · simpa using h₁ hc
  · simpa using h₂ hc

theorem head_brIf {s : Store H} {f : Frame} {args : List Val} {l : LabelIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.brIf l)) c₀) :
    ∃ c : BitVec 32, args = [.num ⟨.int .i32, c⟩] ∧
      ((c ≠ 0 ∧ c₀ = ⟨s, f, [.plain (.br l)]⟩) ∨ (c = 0 ∧ c₀ = ⟨s, f, []⟩)) := by
  cases h with
  | brIfTrue hc => exact ⟨_, rfl, .inl ⟨hc, rfl⟩⟩
  | brIfFalse hc => exact ⟨_, rfl, .inr ⟨hc, rfl⟩⟩
  | _ => head_absurd

/-- **`br_if`.** -/
theorem HWP.brIf {s : Store H} {f : Frame} {us : List Val} {c : BitVec 32} {l : LabelIdx}
    {rest : List Admin} {Q : Post H}
    (h₁ : c ≠ 0 → HWP P host s f (vals us ++ .plain (.br l) :: rest) Q)
    (h₂ : c = 0 → HWP P host s f (vals us ++ rest) Q) :
    HWP P host s f (vals (us ++ [.i32 c]) ++ .plain (.brIf l) :: rest) Q := by
  have hp : ∃ vs args c₀, us ++ [Val.i32 c] = vs ++ args ∧ Head P s f args (.plain (.brIf l)) c₀ := by
    by_cases hc : c = 0
    · exact ⟨us, _, _, rfl, .brIfFalse hc⟩
    · exact ⟨us, _, _, rfl, .brIfTrue hc⟩
  refine HWP.head ⟨rfl, by simp, rfl⟩ hp ?_
  intro us' args c₀ hW hh
  obtain ⟨c', rfl, ⟨hc, rfl⟩ | ⟨hc, rfl⟩⟩ := head_brIf hh <;>
    obtain ⟨rfl, hv⟩ := split_one hW <;> obtain rfl := i32_inj hv.symm
  · simpa using h₁ hc
  · simpa using h₂ hc

theorem head_brOnNull {s : Store H} {f : Frame} {args : List Val} {l : LabelIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.brOnNull l)) c₀) :
    (args = [.ref .null] ∧ c₀ = ⟨s, f, [.plain (.br l)]⟩) ∨
      ∃ v, args = [v] ∧ v ≠ .ref .null ∧ c₀ = ⟨s, f, [v.toAdmin]⟩ := by
  cases h with
  | brOnNullNull => exact .inl ⟨rfl, rfl⟩
  | brOnNullAddr hv => exact .inr ⟨_, rfl, hv, rfl⟩
  | _ => head_absurd

/-- **`br_on_null`.** -/
theorem HWP.brOnNull {s : Store H} {f : Frame} {us : List Val} {v : Val} {l : LabelIdx}
    {rest : List Admin} {Q : Post H}
    (h₁ : v = .ref .null → HWP P host s f (vals us ++ .plain (.br l) :: rest) Q)
    (h₂ : v ≠ .ref .null → HWP P host s f (vals (us ++ [v]) ++ rest) Q) :
    HWP P host s f (vals (us ++ [v]) ++ .plain (.brOnNull l) :: rest) Q := by
  have hp : ∃ vs args c₀, us ++ [v] = vs ++ args ∧ Head P s f args (.plain (.brOnNull l)) c₀ := by
    by_cases hv : v = .ref .null
    · exact ⟨us, _, _, by rw [hv], .brOnNullNull⟩
    · exact ⟨us, _, _, rfl, .brOnNullAddr hv⟩
  refine HWP.head ⟨rfl, by simp, rfl⟩ hp ?_
  intro us' args c₀ hW hh
  rcases head_brOnNull hh with ⟨rfl, rfl⟩ | ⟨v', rfl, hv, rfl⟩ <;>
    obtain ⟨rfl, rfl⟩ := split_one hW
  · simpa using h₁ rfl
  · simpa using h₂ hv

/-! ## Exceptions -/

theorem head_throw {s : Store H} {f : Frame} {args : List Val} {x : TagIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.throw x)) c₀) :
    ∃ ta ti ts, s.tag? f x = some (ta, ti) ∧ Expand ti.type (.func ts .nil) ∧
      args.length = ts.length ∧
      c₀ = ⟨s.addExn ⟨ta, args⟩, f, [.ref (.exn s.exns.length), .plain .throwRef]⟩ := by
  cases h with
  | throw ht he hn => exact ⟨_, _, _, ht, he, hn, rfl⟩
  | _ => head_absurd

/-- **`throw`.** The new exception is allocated at the end of the store's
exceptions. -/
theorem HWP.throw {s : Store H} {f : Frame} {us vs : List Val} {x : TagIdx} {ta : Nat}
    {ti : TagInst} {ts : Ty (.list .val)} {rest : List Admin} {Q : Post H}
    (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil))
    (hn : vs.length = ts.length) (hq : Q (s.addExn ⟨ta, vs⟩) f (.throw s.exns.length)) :
    HWP P host s f (vals (us ++ vs) ++ .plain (.throw x) :: rest) Q := by
  refine HWP.head ⟨rfl, by simp, rfl⟩ ⟨us, vs, _, rfl, .throw ht he hn⟩ ?_
  intro us' args c₀ hW hh
  obtain ⟨ta', ti', ts', ht', he', hn', rfl⟩ := head_throw hh
  obtain ⟨rfl, rfl⟩ : ta' = ta ∧ ti' = ti := by simpa [ht] using ht'.symm
  have hts : ts' = ts := by
    have h₂ := SingleThreaded.Det.Expand.det he' he
    injection h₂
  subst hts
  obtain ⟨rfl, rfl⟩ := split_args hW (hn'.trans hn.symm)
  exact HWP.of_exits (o := .throw _) ⟨us', rest, by simp⟩ hq

theorem head_tryTable {s : Store H} {f : Frame} {args : List Val} {bt : BlockType}
    {cs : List Catch} {body : List Instr} {c₀ : Config H}
    (h : Head P s f args (.plain (.tryTable bt cs body)) c₀) :
    ∃ t₁ t₂, f.module.blockType? bt = some (t₁, t₂) ∧ args.length = t₁.length ∧
      c₀ = ⟨s, f, [.handler t₂.length cs [.label t₂.length [] (vals args ++ expression body)]]⟩ := by
  cases h with
  | tryTable hbt hm => exact ⟨_, _, hbt, hm, rfl⟩
  | _ => head_absurd

/-- **`try_table`.** The body runs in a label (its own `br 0` target) inside an
exception handler with the catch clauses `cs`; a caught exception branches to its
clause's label with the exception's fields. -/
theorem HWP.tryTable {s : Store H} {f : Frame} {us vs : List Val} {bt : BlockType}
    {cs : List Catch} {body : List Instr} {rest : List Admin} {Q : Post H} {t₁ t₂ : List CValType}
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hn : vs.length = t₁.length)
    (h : HWP P host s f (vals vs ++ expression body)
      (labelPost P host t₂.length [] [] (handlerPost cs (prePost us (seqPost P host rest Q))))) :
    HWP P host s f (vals (us ++ vs) ++ .plain (.tryTable bt cs body) :: rest) Q := by
  refine HWP.head ⟨rfl, by simp, rfl⟩ ⟨us, vs, _, rfl, .tryTable hbt hn⟩ ?_
  intro us' args c₀ hW hh
  obtain ⟨t₁', t₂', hbt', hn', rfl⟩ := head_tryTable hh
  obtain ⟨rfl, rfl⟩ : t₁' = t₁ ∧ t₂' = t₂ := by simpa [hbt] using hbt'.symm
  obtain ⟨rfl, rfl⟩ := split_args hW (hn'.trans hn.symm)
  intro n
  have hb := (h n).post_mono fun _ _ _ =>
    labelPost.toK' n fun _ _ _ => handlerPost_mono fun _ _ _ => prePost_mono fun _ _ _ =>
      seqPost.toK (P := P) (host := host) (c₂ := rest) (Q := Q) n
  exact Safe.seq le_rfl (Safe.handler (Safe.label (us := []) (by omega) hb))

end Silmaril.Wasm.Logic.Hoare
