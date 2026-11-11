module

public import Silmaril.Wasm.SingleThreaded.Exec.InterpTyped

@[expose] public section

/-!
# The deterministic driver is reached at once or by a shrinking step (proofs)

silmaril-lean's executable driver `step?` (`Silmaril/Wasm/SingleThreaded/Exec`) is *maximal*:
every host-free successor `c₁` of `c` reaches the driver's successor `d` in at most one step
(`step?_maximal_at`). `step?_lag_at` refines this: either `c₁ = d`, or the step to `c₁` made the
code strictly smaller (`sizeOf`): it is a bubbling step (a trap or a thrown exception taking
part of the surrounding sequence with it), possibly inside labels, handlers and frames.
`stepI_lag_typed` is the instance for silmaril-lean's interpreter step `stepI` on Core-typed
configurations. The proof follows `step?_maximal_at` (same case split); new. Used by
`Silmaril.Proofs.Wasm.Interp.Termination`.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec

variable {H : Type}

/-! ## Sizes of codes -/

theorem sizeOf_append_admins (a b : List Admin) : sizeOf (a ++ b) + 1 = sizeOf a + sizeOf b := by
  induction a with
  | nil =>
    simp only [List.nil_append, List.nil.sizeOf_spec]
    omega
  | cons x a ih =>
    simp only [List.cons_append, List.cons.sizeOf_spec]
    omega

theorem sizeOf_admins_pos (a : List Admin) : 1 ≤ sizeOf a := by
  cases a <;> simp only [List.nil.sizeOf_spec, List.cons.sizeOf_spec] <;> omega

theorem sizeOf_admins_ne_nil {a : List Admin} (h : a ≠ []) : 2 ≤ sizeOf a := by
  cases a with
  | nil => exact absurd rfl h
  | cons x a =>
    have := sizeOf_admins_pos a
    simp only [List.cons.sizeOf_spec]
    omega

/-- Dropping a non-empty part of a sequence around a fixed piece shrinks it. -/
theorem sizeOf_drop_around (l m x n r : List Admin) (h : m ≠ [] ∨ n ≠ []) :
    sizeOf (l ++ x ++ r) < sizeOf (l ++ m ++ x ++ (n ++ r)) := by
  have e1 := sizeOf_append_admins (l ++ x) r
  have e2 := sizeOf_append_admins l x
  have e3 := sizeOf_append_admins (l ++ m ++ x) (n ++ r)
  have e4 := sizeOf_append_admins (l ++ m) x
  have e5 := sizeOf_append_admins l m
  have e6 := sizeOf_append_admins n r
  have p1 := sizeOf_admins_pos n
  have p2 := sizeOf_admins_pos m
  rcases h with h | h
  · have := sizeOf_admins_ne_nil h
    omega
  · have := sizeOf_admins_ne_nil h
    omega

/-- Replacing a piece by a smaller one in a sequence shrinks it. -/
theorem sizeOf_replace_lt (l r : List Admin) {x y : Admin} (h : sizeOf x < sizeOf y) :
    sizeOf (l ++ [x] ++ r) < sizeOf (l ++ [y] ++ r) := by
  have e1 := sizeOf_append_admins (l ++ [x]) r
  have e2 := sizeOf_append_admins l [x]
  have e3 := sizeOf_append_admins (l ++ [y]) r
  have e4 := sizeOf_append_admins l [y]
  simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec] at e2 e4
  omega

/-! ## The lag of a step behind the driver -/

section Lag

variable {o : GrowOracle} {head : HeadFn H} {Inv : Frame → Admin → Prop} {s : Store H}

/-- The two bubbling steps shrink the code. -/
theorem bubble_shrinks {f : Frame} {code : List Admin} {c₁ : Config H}
    (hb : Bubble s f code c₁) : sizeOf c₁.code < sizeOf code := by
  obtain ⟨p, q, X, u, r, rfl, -, hqu, rfl⟩ := hb
  have hq : vals q ≠ [] ∨ u ≠ [] := by
    rcases hqu with h | h
    · exact .inl (by simpa [vals] using h)
    · exact .inr h
  simpa [List.append_assoc] using sizeOf_drop_around (vals p) (vals q) X u r hq

/-- A successor `c₁` of `c` is the driver's successor `d`, or the step to it shrank the code
and kept the store and frame. -/
def Lag (c c₁ d : Config H) : Prop :=
  c₁ = d ∨ (sizeOf c₁.code < sizeOf c.code ∧ c₁.store = c.store ∧ c₁.frame = c.frame)

section Wrap

variable {s₀ s' : Store H} {f f' : Frame} {vs₀ : List Val} {rest is is' : List Admin} {n : Nat}
  {d' : Config H}

theorem lag_label {cont : List Instr} (hr : Lag ⟨s₀, f, is⟩ ⟨s', f', is'⟩ d') :
    Lag ⟨s₀, f, vals vs₀ ++ (vals [] ++ .label n cont is :: rest)⟩
      ⟨s', f', vals vs₀ ++ [.label n cont is'] ++ rest⟩
      ⟨d'.store, d'.frame, vals (vs₀ ++ []) ++ [.label n cont d'.code] ++ rest⟩ := by
  rcases hr with rfl | ⟨hlt, hs', hf'⟩
  · exact .inl (by simp)
  · have hsz : sizeOf (vals vs₀ ++ [.label n cont is'] ++ rest) <
        sizeOf (vals vs₀ ++ [.label n cont is] ++ rest) :=
      sizeOf_replace_lt (vals vs₀) rest (by simpa using hlt)
    exact .inr ⟨by simpa using hsz, hs', hf'⟩

theorem lag_handler {cs : List Catch} (hr : Lag ⟨s₀, f, is⟩ ⟨s', f', is'⟩ d') :
    Lag ⟨s₀, f, vals vs₀ ++ (vals [] ++ .handler n cs is :: rest)⟩
      ⟨s', f', vals vs₀ ++ [.handler n cs is'] ++ rest⟩
      ⟨d'.store, d'.frame, vals (vs₀ ++ []) ++ [.handler n cs d'.code] ++ rest⟩ := by
  rcases hr with rfl | ⟨hlt, hs', hf'⟩
  · exact .inl (by simp)
  · have hsz : sizeOf (vals vs₀ ++ [.handler n cs is'] ++ rest) <
        sizeOf (vals vs₀ ++ [.handler n cs is] ++ rest) :=
      sizeOf_replace_lt (vals vs₀) rest (by simpa using hlt)
    exact .inr ⟨by simpa using hsz, hs', hf'⟩

theorem lag_frame {fi fi' : Frame} (hr : Lag ⟨s₀, fi, is⟩ ⟨s', fi', is'⟩ d') :
    Lag ⟨s₀, f, vals vs₀ ++ (vals [] ++ .frame n fi is :: rest)⟩
      ⟨s', f, vals vs₀ ++ [.frame n fi' is'] ++ rest⟩
      ⟨d'.store, f, vals (vs₀ ++ []) ++ [.frame n d'.frame d'.code] ++ rest⟩ := by
  rcases hr with rfl | ⟨hlt, hs', hf'⟩
  · exact .inl (by simp)
  · have hfi : fi' = fi := hf'
    have hsz : sizeOf (vals vs₀ ++ [.frame n fi' is'] ++ rest) <
        sizeOf (vals vs₀ ++ [.frame n fi is] ++ rest) :=
      sizeOf_replace_lt (vals vs₀) rest (by simpa [hfi] using hlt)
    exact .inr ⟨by simpa using hsz, hs', rfl⟩

end Wrap

/-- The inner induction hypothesis of the lag lemma. -/
def LagIH (head : HeadFn H) (Inv : Frame → Admin → Prop) (s : Store H) (m : Nat) : Prop :=
  ∀ (fr : Frame) (is : List Admin) (c₁ d : Config H), sizeOf is < m → DeepAll Inv fr is →
    Step (profile o) noHost ⟨s, fr, is⟩ c₁ → step? head ⟨s, fr, is⟩ = some d →
    Lag ⟨s, fr, is⟩ c₁ d

section Ctx

variable {f : Frame} {vs₀ : List Val} {rest is : List Admin} {d : Config H} {n : Nat}
  {s' : Store H} {is' : List Admin}

theorem lag_ctx_label {cont : List Instr} {f' : Frame} (ih : LagIH (o := o) head Inv s (sizeOf is + 1))
    (hat : DeepAll Inv f is) (hin : Step (profile o) noHost ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (hd : (step? head ⟨s, f, is⟩).map (fun c' =>
      (⟨c'.store, c'.frame, vals (vs₀ ++ []) ++ [.label n cont c'.code] ++ rest⟩ : Config H)) =
        some d) :
    Lag ⟨s, f, vals vs₀ ++ (vals [] ++ .label n cont is :: rest)⟩
      ⟨s', f', vals vs₀ ++ [.label n cont is'] ++ rest⟩ d := by
  obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hd
  exact lag_label (ih f is _ d' (by omega) hat hin hd')

theorem lag_ctx_handler {cs : List Catch} {f' : Frame}
    (ih : LagIH (o := o) head Inv s (sizeOf is + 1))
    (hat : DeepAll Inv f is) (hin : Step (profile o) noHost ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (hd : (step? head ⟨s, f, is⟩).map (fun c' =>
      (⟨c'.store, c'.frame, vals (vs₀ ++ []) ++ [.handler n cs c'.code] ++ rest⟩ : Config H)) =
        some d) :
    Lag ⟨s, f, vals vs₀ ++ (vals [] ++ .handler n cs is :: rest)⟩
      ⟨s', f', vals vs₀ ++ [.handler n cs is'] ++ rest⟩ d := by
  obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hd
  exact lag_handler (ih f is _ d' (by omega) hat hin hd')

theorem lag_ctx_frame {fi fi' : Frame} (ih : LagIH (o := o) head Inv s (sizeOf is + 1))
    (hat : DeepAll Inv fi is) (hin : Step (profile o) noHost ⟨s, fi, is⟩ ⟨s', fi', is'⟩)
    (hd : (step? head ⟨s, fi, is⟩).map (fun c' =>
      (⟨c'.store, f, vals (vs₀ ++ []) ++ [.frame n c'.frame c'.code] ++ rest⟩ : Config H)) =
        some d) :
    Lag ⟨s, f, vals vs₀ ++ (vals [] ++ .frame n fi is :: rest)⟩
      ⟨s', f, vals vs₀ ++ [.frame n fi' is'] ++ rest⟩ d := by
  obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hd
  exact lag_frame (ih fi is _ d' (by omega) hat hin hd')

end Ctx

/-- A smaller induction hypothesis. -/
theorem LagIH.mono {m m' : Nat} (ih : LagIH (o := o) head Inv s m) (h : m' ≤ m) :
    LagIH (o := o) head Inv s m' :=
  fun fr is c₁ d hlt => ih fr is c₁ d (lt_of_lt_of_le hlt h)

/-- The head-decomposition case of the lag lemma. -/
theorem lag_headDec {f : Frame} {code : List Admin} {c₁ d : Config H}
    (hx : ∀ f vs args e c, Inv f e → Head (profile o) s f args e c → (∃ q, vs = q ++ args) →
      head s f vs e = some (args.length, c) ∨
        (head s f vs e = none ∧ IsCtxtHead (profile o) s f e c))
    (ih : LagIH (o := o) head Inv s (sizeOf code)) (hinv : DeepAll Inv f code)
    (hdec : HeadDec (profile o) s f code c₁) (hd : step? head ⟨s, f, code⟩ = some d) :
    Lag ⟨s, f, code⟩ c₁ d := by
  obtain ⟨vs₀, args, e, rest, c₀, rfl, hH, rfl⟩ := hdec
  have hg := hH.good
  have hs : splitVals (vals vs₀ ++ (vals args ++ e :: rest)) = (vs₀ ++ args, e :: rest) := by
    rw [← List.append_assoc, ← vals_append]; exact Det.splitVals_vals_cons hg.val_none rest
  have hat : Drv.DeepAt Inv f e := by
    rw [← List.append_assoc, ← vals_append] at hinv; exact Drv.deepAll_split hinv
  have htrap : Drv.isTrap e = false := by
    cases e <;> simp [Drv.isTrap]; exact hg.ne_trap rfl
  have hthrow : Drv.throwAddr? (vs₀ ++ args) e = none := by
    unfold Drv.throwAddr?
    split
    · rw [hg.throwRef rfl]; simp
    · rfl
  rw [step?_cons (c := ⟨s, f, _⟩) hs] at hd
  simp only [Drv.layer, htrap, hthrow] at hd
  rcases hx f (vs₀ ++ args) args e c₀ hat.inv hH ⟨vs₀, rfl⟩ with hsome | ⟨hnone, hctx⟩
  · rw [hsome] at hd
    simp only [Option.some.injEq] at hd
    subst hd
    left
    simp
  · rw [hnone] at hd
    have hlt : sizeOf e < sizeOf (vals vs₀ ++ (vals args ++ e :: rest)) := sizeOf_lt_code
    rcases hctx with ⟨n', cont, is, s', f', is', rfl, rfl, hin⟩ |
      ⟨n', cs, is, s', f', is', rfl, rfl, hin⟩ | ⟨n', fi, is, s', fi', is', rfl, rfl, hin⟩
    · obtain rfl := Head.args_nil_label hH
      have h1 : sizeOf is < sizeOf (Admin.label n' cont is) := Drv.sizeOf_label_body
      exact lag_ctx_label (ih.mono (m' := sizeOf is + 1) (by omega)) hat.2 hin hd
    · obtain rfl := Head.args_nil_handler hH
      have h1 : sizeOf is < sizeOf (Admin.handler n' cs is) := Drv.sizeOf_handler_body
      exact lag_ctx_handler (ih.mono (m' := sizeOf is + 1) (by omega)) hat.2 hin hd
    · obtain rfl := Head.args_nil_frame hH
      have h1 : sizeOf is < sizeOf (Admin.frame n' fi is) := Drv.sizeOf_frame_body
      exact lag_ctx_frame (ih.mono (m' := sizeOf is + 1) (by omega)) hat.2 hin hd

/-- **The lag lemma.** A host-free successor `c₁` of `c` is the driver's successor `d`, or
the step to it shrank the code and kept the store and frame. -/
theorem step?_lag_at
    (hx : ∀ f vs args e c, Inv f e → Head (profile o) s f args e c → (∃ q, vs = q ++ args) →
      head s f vs e = some (args.length, c) ∨
        (head s f vs e = none ∧ IsCtxtHead (profile o) s f e c)) :
    ∀ (n : Nat) (c c₁ d : Config H), sizeOf c.code = n → c.store = s →
      DeepAll Inv c.frame c.code →
      Step (profile o) noHost c c₁ → step? head c = some d → Lag c c₁ d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rintro ⟨s₀, f, code⟩ c₁ d hn hst hinv hstep hd
  have hs₀ : s₀ = s := hst
  subst hs₀
  have ih' : LagIH (o := o) head Inv s₀ (sizeOf code) := fun fr is c₁ d hlt =>
    ih (sizeOf is) (hn ▸ hlt) ⟨s₀, fr, is⟩ c₁ d rfl rfl
  rcases Step.decomp hstep with hdec | hb
  · exact lag_headDec hx ih' hinv hdec hd
  · have hsz := bubble_shrinks hb
    obtain ⟨p, q, X, u, r, -, -, -, rfl⟩ := hb
    exact .inr ⟨hsz, rfl, rfl⟩

end Lag

/-- **The lag lemma for silmaril-lean's interpreter step** on Core-typed configurations. -/
theorem stepI_lag_typed {o : GrowOracle} {ts : List Validation.CValType} {c c₁ d : Config H}
    (hc : ConfigOk c ts) (h : Step (profile o) noHost c c₁) (hd : stepI o c = some d) :
    Lag c c₁ d :=
  step?_lag_at (interpHead_exact (ConfigOk.storeOk hc)) _ c c₁ d rfl rfl
    (ConfigOk.deepAll_iHeadInv hc) h hd

end Silmaril.Wasm.Interp
