module

public import Silmaril.Proofs.Wasm.Logic.Core.Rules

/-!
# Straight-line code by evaluation: soundness

`exec s f rs is` (`Silmaril.Wasm.Logic.Core.Defs`) is a small interpreter for
straight-line Core 3.0 code with a top-first operand stack. `exec1_spec` shows
that one successful instruction pops some values `pop` and pushes `push` by a run
of the small-step semantics, in any profile and for any host; `exec_sound` lifts
this to whole sequences, and `wp_exec` (with its variants) to a `WP` step, which
is what the `wasm_step` tactic applies before evaluating `exec` with `simp`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Core

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Unfolding `exec` -/

@[simp] theorem exec_nil (s : Store H) (f : Frame) (rs : List Val) :
    exec s f rs [] = some (s, f, rs) := rfl

theorem exec_cons (s : Store H) (f : Frame) (rs : List Val) (i : Instr) (is : List Instr) :
    exec s f rs (i :: is) =
      (match exec1 s f rs i with
        | some (s₁, f₁, rs₁) => exec s₁ f₁ rs₁ is
        | none => none) := rfl

theorem exec_cons_of_some {s s₁ : Store H} {f f₁ : Frame} {rs rs₁ : List Val} {i : Instr}
    {is : List Instr} (h : exec1 s f rs i = some (s₁, f₁, rs₁)) :
    exec s f rs (i :: is) = exec s₁ f₁ rs₁ is := by
  rw [exec_cons, h]

theorem exec_append (s : Store H) (f : Frame) (rs : List Val) (is js : List Instr) :
    exec s f rs (is ++ js) =
      (match exec s f rs is with
        | some (s₁, f₁, rs₁) => exec s₁ f₁ rs₁ js
        | none => none) := by
  induction is generalizing s f rs with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, exec_cons]
    split
    · exact ih ..
    · rfl

@[simp] theorem popInt_i32 (a : BitVec 32) (rs : List Val) :
    popInt .i32 (Val.i32 a :: rs) = some (a, rs) := rfl

@[simp] theorem popInt_i64 (a : BitVec 64) (rs : List Val) :
    popInt .i64 (Val.i64 a :: rs) = some (a, rs) := rfl

@[simp] theorem popV_cons (v : Val) (rs : List Val) : popV (v :: rs) = some (v, rs) := rfl

/-! ## Inverting the stack accessors -/

theorem popInt_eq {t : IntType} {rs rs' : List Val} {a : BitVec t.width}
    (h : popInt t rs = some (a, rs')) : rs = .num ⟨.int t, a⟩ :: rs' := by
  cases t
  all_goals
    rcases rs with _ | ⟨v, rs⟩
    · cases h
    · rcases v with ⟨ty, b⟩ | v | v
      · rcases ty with t' | t'
        · cases t' <;> first | (cases h; rfl) | cases h
        · cases h
      · cases h
      · cases h

theorem popV_eq {rs rs' : List Val} {v : Val} (h : popV rs = some (v, rs')) : rs = v :: rs' := by
  cases rs with
  | nil => cases h
  | cons w rs => cases h; rfl

theorem localVal?_eq {f : Frame} {x : LocalIdx} {v : Val} (h : localVal? f x = some v) :
    f.local? x = some (some v) := by
  unfold localVal? at h
  split at h
  · cases h; assumption
  · cases h

/-- Inverting `Option.bind` on a popped value. -/
theorem bind_eq_some {α β : Type} {o : Option α} {g : α → Option β} {b : β}
    (h : o.bind g = some b) : ∃ a, o = some a ∧ g a = some b := Option.bind_eq_some_iff.mp h

/-- Inverting `Option.map` on a popped value. -/
theorem map_eq_some {α β : Type} {o : Option α} {g : α → β} {b : β}
    (h : o.map g = some b) : ∃ a, o = some a ∧ g a = b := Option.map_eq_some_iff.mp h

/-! ## One instruction: pop, run, push -/

/-- The common shape of one straight-line instruction: it pops `pop` (top-first) from
`rs`, runs, and pushes `push`. -/
def ExecSpec (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (rs : List Val)
    (i : Instr) (s' : Store H) (f' : Frame) (rs' : List Val) : Prop :=
  ∃ pop push rs₀ : List Val, rs = pop ++ rs₀ ∧ rs' = push ++ rs₀ ∧
    Steps P host ⟨s, f, vals pop.reverse ++ [.plain i]⟩ ⟨s', f', vals push.reverse⟩

/-- A run on the popped values, in the context of the rest of the stack and code. -/
theorem steps_top {s s' : Store H} {f f' : Frame} {pop push rs₀ : List Val} {i : Instr}
    (rest : List Admin)
    (h : Steps P host ⟨s, f, vals pop.reverse ++ [.plain i]⟩ ⟨s', f', vals push.reverse⟩) :
    Steps P host ⟨s, f, vals (pop ++ rs₀).reverse ++ .plain i :: rest⟩
      ⟨s', f', vals (push ++ rs₀).reverse ++ rest⟩ := by
  have hc := Steps.ctx rs₀.reverse rest h
  simpa only [List.reverse_append, vals_append, List.append_assoc, List.singleton_append]
    using hc

section Inversion

variable {s s' : Store H} {f f' : Frame} {rs rs' : List Val}

/-- The result of a successful instruction, as three equations. -/
theorem result_eq {a b : Store H × Frame × List Val} (h : some a = some b) :
    a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2 = b.2.2 := by
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem exec1_nop (h : exec1 s f rs .nop = some (s', f', rs')) :
    ExecSpec P host s f rs .nop s' f' rs' := by
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ rs = rs' := result_eq h
  exact ⟨[], [], rs, rfl, rfl, .single (.parametric .nop)⟩

theorem exec1_drop (h : exec1 s f rs .drop = some (s', f', rs')) :
    ExecSpec P host s f rs .drop s' f' rs' := by
  obtain ⟨⟨v, rs₀⟩, hp, he⟩ := map_eq_some h
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ rs₀ = rs' := result_eq (congrArg some he)
  exact ⟨[v], [], rs₀, popV_eq hp, rfl, .single (.parametric (.drop v))⟩

theorem exec1_intConst {t : IntType} {c : BitVec t.width}
    (h : exec1 s f rs (.intConst t c) = some (s', f', rs')) :
    ExecSpec P host s f rs (.intConst t c) s' f' rs' := by
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ .num ⟨.int t, c⟩ :: rs = rs' := result_eq h
  exact ⟨[], [.num ⟨.int t, c⟩], rs, rfl, rfl, .refl⟩

theorem exec1_localGet {x : LocalIdx} (h : exec1 s f rs (.localGet x) = some (s', f', rs')) :
    ExecSpec P host s f rs (.localGet x) s' f' rs' := by
  obtain ⟨v, hv, he⟩ := map_eq_some h
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ v :: rs = rs' := result_eq (congrArg some he)
  exact ⟨[], [v], rs, rfl, rfl, .single (.variable (.localGet (localVal?_eq hv)))⟩

theorem exec1_localSet {x : LocalIdx} (h : exec1 s f rs (.localSet x) = some (s', f', rs')) :
    ExecSpec P host s f rs (.localSet x) s' f' rs' := by
  obtain ⟨⟨v, rs₀⟩, hp, he⟩ := bind_eq_some h
  by_cases hx : x.toNat < f.locals.length
  · have he' : some (s, f.setLocal x v, rs₀) = some (s', f', rs') := by
      simpa only [hx, ↓reduceIte] using he
    obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f.setLocal x v = f' ∧ rs₀ = rs' := result_eq he'
    exact ⟨[v], [], rs₀, popV_eq hp, rfl, .single (.variable (.localSet hx))⟩
  · have he' : (none : Option (Store H × Frame × List Val)) = some (s', f', rs') := by
      simpa only [hx, ↓reduceIte] using he
    cases he'

theorem exec1_localTee {x : LocalIdx} (h : exec1 s f rs (.localTee x) = some (s', f', rs')) :
    ExecSpec P host s f rs (.localTee x) s' f' rs' := by
  obtain ⟨⟨v, rs₀⟩, hp, he⟩ := bind_eq_some h
  by_cases hx : x.toNat < f.locals.length
  · have he' : some (s, f.setLocal x v, v :: rs₀) = some (s', f', rs') := by
      simpa only [hx, ↓reduceIte] using he
    obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f.setLocal x v = f' ∧ v :: rs₀ = rs' := result_eq he'
    have h₁ : Step P host ⟨s, f, [v.toAdmin, .plain (.localTee x)]⟩
        ⟨s, f, [v.toAdmin] ++ [v.toAdmin, .plain (.localSet x)]⟩ := .variable .localTee
    have h₂ := Step.ctx (P := P) (host := host) [v] [] (VariableStep.localSet (s := s)
      (f := f) (x := x) (v := v) hx |> Step.variable)
    exact ⟨[v], [v], rs₀, popV_eq hp, rfl, .head h₁ (.single h₂)⟩
  · have he' : (none : Option (Store H × Frame × List Val)) = some (s', f', rs') := by
      simpa only [hx, ↓reduceIte] using he
    cases he'

theorem exec1_globalGet {x : GlobalIdx} (h : exec1 s f rs (.globalGet x) = some (s', f', rs')) :
    ExecSpec P host s f rs (.globalGet x) s' f' rs' := by
  obtain ⟨⟨a, g⟩, hg, he⟩ := map_eq_some h
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ g.value :: rs = rs' := result_eq (congrArg some he)
  exact ⟨[], [g.value], rs, rfl, rfl, .single (.variable (.globalGet hg))⟩

theorem exec1_globalSet {x : GlobalIdx} (h : exec1 s f rs (.globalSet x) = some (s', f', rs')) :
    ExecSpec P host s f rs (.globalSet x) s' f' rs' := by
  obtain ⟨⟨v, rs₀⟩, hp, he⟩ := bind_eq_some h
  obtain ⟨⟨a, g⟩, hg, he'⟩ := map_eq_some he
  obtain ⟨rfl, rfl, rfl⟩ : s.setGlobal a v = s' ∧ f = f' ∧ rs₀ = rs' :=
    result_eq (congrArg some he')
  exact ⟨[v], [], rs₀, popV_eq hp, rfl, .single (.variable (.globalSet hg))⟩

theorem exec1_intUnOp {t : IntType} {op : IntUnOp}
    (h : exec1 s f rs (.intUnOp t op) = some (s', f', rs')) :
    ExecSpec P host s f rs (.intUnOp t op) s' f' rs' := by
  obtain ⟨⟨x, rs₁⟩, hp, he⟩ := map_eq_some h
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ .num ⟨.int t, intUnOp t op x⟩ :: rs₁ = rs' :=
    result_eq (congrArg some he)
  exact ⟨[.num ⟨.int t, x⟩], [.num ⟨.int t, intUnOp t op x⟩], rs₁, popInt_eq hp, rfl,
    .single (.numeric .intUnOp)⟩

theorem exec1_intBinOp {t : IntType} {op : IntBinOp}
    (h : exec1 s f rs (.intBinOp t op) = some (s', f', rs')) :
    ExecSpec P host s f rs (.intBinOp t op) s' f' rs' := by
  obtain ⟨⟨y, rs₁⟩, hp₁, he₁⟩ := bind_eq_some h
  obtain ⟨⟨x, rs₂⟩, hp₂, he₂⟩ := bind_eq_some he₁
  have hrs : rs = [.num ⟨.int t, y⟩, .num ⟨.int t, x⟩] ++ rs₂ := by
    rw [popInt_eq hp₁, popInt_eq hp₂]; rfl
  cases hz : intBinOp t op x y with
  | error e =>
    have hn : (none : Option (Store H × Frame × List Val)) = some (s', f', rs') := by
      simpa only [hz] using he₂
    cases hn
  | ok z =>
    have hs : some (s, f, .num ⟨.int t, z⟩ :: rs₂) = some (s', f', rs') := by
      simpa only [hz] using he₂
    obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ .num ⟨.int t, z⟩ :: rs₂ = rs' := result_eq hs
    exact ⟨_, [.num ⟨.int t, z⟩], rs₂, hrs, rfl, .single (.numeric (.intBinOp hz))⟩

theorem exec1_intTestOp {t : IntType} {op : IntTestOp}
    (h : exec1 s f rs (.intTestOp t op) = some (s', f', rs')) :
    ExecSpec P host s f rs (.intTestOp t op) s' f' rs' := by
  obtain ⟨⟨x, rs₁⟩, hp, he⟩ := map_eq_some h
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ Val.i32 (intTestOp t op x) :: rs₁ = rs' :=
    result_eq (congrArg some he)
  exact ⟨[.num ⟨.int t, x⟩], [Val.i32 (intTestOp t op x)], rs₁, popInt_eq hp, rfl,
    .single (.numeric .intTestOp)⟩

theorem exec1_intRelOp {t : IntType} {op : IntRelOp}
    (h : exec1 s f rs (.intRelOp t op) = some (s', f', rs')) :
    ExecSpec P host s f rs (.intRelOp t op) s' f' rs' := by
  obtain ⟨⟨y, rs₁⟩, hp₁, he₁⟩ := bind_eq_some h
  obtain ⟨⟨x, rs₂⟩, hp₂, he₂⟩ := map_eq_some he₁
  have hrs : rs = [.num ⟨.int t, y⟩, .num ⟨.int t, x⟩] ++ rs₂ := by
    rw [popInt_eq hp₁, popInt_eq hp₂]; rfl
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ Val.i32 (intRelOp t op x y) :: rs₂ = rs' :=
    result_eq (congrArg some he₂)
  exact ⟨_, [Val.i32 (intRelOp t op x y)], rs₂, hrs, rfl, .single (.numeric .intRelOp)⟩

theorem exec1_intLoadFull {t : IntType} {x : MemIdx} {arg : MemArg}
    (h : exec1 s f rs (.intLoad t none x arg) = some (s', f', rs')) :
    ExecSpec P host s f rs (.intLoad t none x arg) s' f' rs' := by
  obtain ⟨⟨a, rs₁⟩, hp, he₁⟩ := bind_eq_some h
  obtain ⟨⟨ma, mi⟩, hm, he₂⟩ := bind_eq_some he₁
  obtain ⟨c, hl, he₃⟩ := map_eq_some he₂
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ .num ⟨.int t, c.setWidth t.width⟩ :: rs₁ = rs' :=
    result_eq (congrArg some he₃)
  exact ⟨[Val.i32 a], [.num ⟨.int t, c.setWidth t.width⟩], rs₁, popInt_eq hp, rfl,
    .single (.memory (.loadIntVal (a := .i32) hm hl))⟩

theorem exec1_intLoadPack {t : IntType} {sz : PackSize} {sx : Signedness} {x : MemIdx}
    {arg : MemArg} (h : exec1 s f rs (.intLoad t (some (sz, sx)) x arg) = some (s', f', rs')) :
    ExecSpec P host s f rs (.intLoad t (some (sz, sx)) x arg) s' f' rs' := by
  obtain ⟨⟨a, rs₁⟩, hp, he₁⟩ := bind_eq_some h
  obtain ⟨⟨ma, mi⟩, hm, he₂⟩ := bind_eq_some he₁
  obtain ⟨c, hl, he₃⟩ := map_eq_some he₂
  have hstep := MemoryStep.loadPackVal (P := P) (t := t) (sx := sx) (a := .i32) (i := a) hm hl
  rcases sx with _ | _
  · obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ .num ⟨.int t, c.signExtend t.width⟩ :: rs₁ = rs' :=
      result_eq (congrArg some he₃)
    exact ⟨[Val.i32 a], [.num ⟨.int t, c.signExtend t.width⟩], rs₁, popInt_eq hp, rfl,
      .single (.memory hstep)⟩
  · obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ .num ⟨.int t, c.setWidth t.width⟩ :: rs₁ = rs' :=
      result_eq (congrArg some he₃)
    exact ⟨[Val.i32 a], [.num ⟨.int t, c.setWidth t.width⟩], rs₁, popInt_eq hp, rfl,
      .single (.memory hstep)⟩

theorem exec1_intStoreFull {t : IntType} {x : MemIdx} {arg : MemArg}
    (h : exec1 s f rs (.intStore t none x arg) = some (s', f', rs')) :
    ExecSpec P host s f rs (.intStore t none x arg) s' f' rs' := by
  obtain ⟨⟨c, rs₁⟩, hp₁, he₁⟩ := bind_eq_some h
  obtain ⟨⟨a, rs₂⟩, hp₂, he₂⟩ := bind_eq_some he₁
  obtain ⟨⟨ma, mi⟩, hm, he₃⟩ := bind_eq_some he₂
  obtain ⟨b, hb, he₄⟩ := map_eq_some he₃
  obtain ⟨rfl, rfl, rfl⟩ : s.setMem ma { mi with bytes := b } = s' ∧ f = f' ∧ rs₂ = rs' :=
    result_eq (congrArg some he₄)
  have hrs : rs = [.num ⟨.int t, c⟩, Val.i32 a] ++ rs₂ := by
    rw [popInt_eq hp₁, popInt_eq hp₂]; rfl
  exact ⟨_, [], rs₂, hrs, rfl, .single (.memory (.storeIntVal (a := .i32) hm hb))⟩

theorem exec1_intStorePack {t : IntType} {sz : PackSize} {x : MemIdx} {arg : MemArg}
    (h : exec1 s f rs (.intStore t (some sz) x arg) = some (s', f', rs')) :
    ExecSpec P host s f rs (.intStore t (some sz) x arg) s' f' rs' := by
  obtain ⟨⟨c, rs₁⟩, hp₁, he₁⟩ := bind_eq_some h
  obtain ⟨⟨a, rs₂⟩, hp₂, he₂⟩ := bind_eq_some he₁
  obtain ⟨⟨ma, mi⟩, hm, he₃⟩ := bind_eq_some he₂
  obtain ⟨b, hb, he₄⟩ := map_eq_some he₃
  obtain ⟨rfl, rfl, rfl⟩ : s.setMem ma { mi with bytes := b } = s' ∧ f = f' ∧ rs₂ = rs' :=
    result_eq (congrArg some he₄)
  have hrs : rs = [.num ⟨.int t, c⟩, Val.i32 a] ++ rs₂ := by
    rw [popInt_eq hp₁, popInt_eq hp₂]; rfl
  exact ⟨_, [], rs₂, hrs, rfl, .single (.memory (.storePackVal (a := .i32) hm hb))⟩

theorem exec1_intLoad {t : IntType} {p : Option (PackSize × Signedness)} {x : MemIdx}
    {arg : MemArg} (h : exec1 s f rs (.intLoad t p x arg) = some (s', f', rs')) :
    ExecSpec P host s f rs (.intLoad t p x arg) s' f' rs' := by
  rcases p with _ | ⟨sz, sx⟩
  · exact exec1_intLoadFull h
  · exact exec1_intLoadPack h

theorem exec1_intStore {t : IntType} {p : Option PackSize} {x : MemIdx} {arg : MemArg}
    (h : exec1 s f rs (.intStore t p x arg) = some (s', f', rs')) :
    ExecSpec P host s f rs (.intStore t p x arg) s' f' rs' := by
  rcases p with _ | sz
  · exact exec1_intStoreFull h
  · exact exec1_intStorePack h

end Inversion

/-- **One instruction of straight-line code pops, runs and pushes**, in any profile. -/
theorem exec1_spec {s s' : Store H} {f f' : Frame} {rs rs' : List Val} {i : Instr}
    (h : exec1 s f rs i = some (s', f', rs')) : ExecSpec P host s f rs i s' f' rs' := by
  cases i <;>
    first
    | exact exec1_nop h | exact exec1_drop h | exact exec1_intConst h
    | exact exec1_localGet h | exact exec1_localSet h | exact exec1_localTee h
    | exact exec1_globalGet h | exact exec1_globalSet h | exact exec1_intUnOp h
    | exact exec1_intBinOp h | exact exec1_intTestOp h | exact exec1_intRelOp h
    | exact exec1_intLoad h | exact exec1_intStore h
    | exact absurd h (by simp only [exec1, reduceCtorEq, not_false_eq_true])

/-- **One instruction of straight-line code is a run**, in any profile. -/
theorem exec1_sound {s s' : Store H} {f f' : Frame} {rs rs' : List Val} {i : Instr}
    (rest : List Admin) (h : exec1 s f rs i = some (s', f', rs')) :
    Steps P host ⟨s, f, vals rs.reverse ++ .plain i :: rest⟩
      ⟨s', f', vals rs'.reverse ++ rest⟩ := by
  obtain ⟨pop, push, rs₀, rfl, rfl, hs⟩ := exec1_spec (P := P) (host := host) h
  exact steps_top rest hs

/-- **Soundness of `exec`.** -/
theorem exec_sound {s s' : Store H} {f f' : Frame} {rs rs' : List Val} {is : List Instr}
    (rest : List Admin) (h : exec s f rs is = some (s', f', rs')) :
    Steps P host ⟨s, f, vals rs.reverse ++ expression is ++ rest⟩
      ⟨s', f', vals rs'.reverse ++ rest⟩ := by
  induction is generalizing s f rs with
  | nil => cases h; exact Steps.of_eq (by simp)
  | cons i is ih =>
    rw [exec_cons] at h
    split at h
    · rename_i s₁ f₁ rs₁ h₁
      have h₁' := exec1_sound (P := P) (host := host) (expression is ++ rest) h₁
      rw [expression_cons, List.append_assoc, List.cons_append]
      refine h₁'.trans ?_
      rw [← List.append_assoc]
      exact ih h
    · cases h

/-- The `WP` form of `exec_sound`: evaluate straight-line code, then continue. The
premise is a `match` on `exec`, so that `simp` can compute it in place. -/
theorem wp_exec {s : Store H} {f : Frame} {vs : List Val} {is : List Instr}
    {rest : List Admin} {Q : Post H}
    (h : match exec s f vs.reverse is with
      | some (s', f', rs') => WP P host s' f' (vals rs'.reverse ++ rest) Q
      | none => False) :
    WP P host s f (vals vs ++ expression is ++ rest) Q := by
  split at h
  · rename_i s' f' rs' he
    have hs := exec_sound (P := P) (host := host) rest he
    rw [List.reverse_reverse] at hs
    exact WP.steps hs h
  · exact h.elim

/-- `wp_exec` from an empty stack. -/
theorem wp_exec₀ {s : Store H} {f : Frame} {is : List Instr} {rest : List Admin} {Q : Post H}
    (h : match exec s f [] is with
      | some (s', f', rs') => WP P host s' f' (vals rs'.reverse ++ rest) Q
      | none => False) :
    WP P host s f (expression is ++ rest) Q := by
  simpa [vals] using wp_exec (P := P) (host := host) (vs := []) (rest := rest) h

/-- `wp_exec` for a whole body of straight-line code. -/
theorem wp_exec_all {s : Store H} {f : Frame} {is : List Instr} {Q : Post H}
    (h : match exec s f [] is with
      | some (s', f', rs') => Q s' f' (.normal rs'.reverse)
      | none => False) :
    WP P host s f (expression is) Q := by
  split at h
  · rename_i s' f' rs' he
    have hs := exec_sound (P := P) (host := host) [] he
    simp only [List.reverse_nil, List.append_nil] at hs
    rw [show vals ([] : List Val) = [] from rfl, List.nil_append] at hs
    exact WP.steps hs (wp_vals h)
  · exact h.elim

/-- `wp_exec` for straight-line code that ends the block, on a non-empty stack. -/
theorem wp_exec_vals {s : Store H} {f : Frame} {vs : List Val} {is : List Instr} {Q : Post H}
    (h : match exec s f vs.reverse is with
      | some (s', f', rs') => Q s' f' (.normal rs'.reverse)
      | none => False) :
    WP P host s f (vals vs ++ expression is) Q := by
  split at h
  · rename_i s' f' rs' he
    have hs := exec_sound (P := P) (host := host) [] he
    simp only [List.reverse_reverse, List.append_nil] at hs
    exact WP.steps hs (wp_vals h)
  · exact h.elim

end Silmaril.Wasm.Logic.Core
