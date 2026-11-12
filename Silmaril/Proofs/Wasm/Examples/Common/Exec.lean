module

public import Silmaril.Wasm.Logic.Instr.Thms
public import Silmaril.Wasm.Logic.Core.Thms

@[expose] public section

/-!
# Symbolic execution for the every-run logic

`Silmaril.Wasm.Logic.Core.exec` evaluates straight-line integer code (locals, globals, integer
arithmetic, integer loads and stores at `i32` addresses). Its soundness in the source
(`exec_sound`) is a run, which suffices for the existential calculus `WP`. Here every
instruction it evaluates is shown to be a profile-free family head step (except constants,
which are values, and `local.tee`, which is two such steps), so by `Wp.det` its result is the
**only** continuation in every profile and for every host:

* `Wp.exec1`: one evaluated instruction, in either reading (`HWP`/`TWP`);
* `Wp.exec_eq`: the same with the evaluation given as an equation;
* **`Wp.exec`**: a whole evaluated sequence: if `exec s f vs.reverse is = some (s', f', rs')`,
  then `Wp m P host s f (vals vs ++ expression is ++ rest) Q` follows from
  `Wp m P host s' f' (vals rs'.reverse ++ rest) Q`.

This is the verification-condition generator for straight-line export bodies: `simp` evaluates
`exec` and leaves the continuation. A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.Common

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head famOf)
open Silmaril.Wasm.Logic.Core (Post exec exec1 popInt popV localVal? exec_cons popInt_eq popV_eq
  localVal?_eq bind_eq_some map_eq_some result_eq)
open Silmaril.Wasm.Logic.Hoare (Wp Corr ProfileFree)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- One evaluated instruction is a profile-free family head step popping `pop` and pushing
`push` (both top-first). -/
def HeadSpec (P : Profile) (s : Store H) (f : Frame) (rs : List Val) (i : Instr) (s' : Store H)
    (f' : Frame) (rs' : List Val) : Prop :=
  ∃ pop push rs₀ : List Val, rs = pop ++ rs₀ ∧ rs' = push ++ rs₀ ∧
    Head P s f pop.reverse (.plain i) ⟨s', f', vals push.reverse⟩ ∧
    famOf (.plain i) ≠ .control ∧ ProfileFree i

/-- A head-step instruction in context. -/
theorem HeadSpec.wp {m : Corr} {s s' : Store H} {f f' : Frame} {rs rs' : List Val} {i : Instr}
    {rest : List Admin} {Q : Post H} (h : HeadSpec P s f rs i s' f' rs')
    (hk : Wp m P host s' f' (vals rs'.reverse ++ rest) Q) :
    Wp m P host s f (vals rs.reverse ++ .plain i :: rest) Q := by
  obtain ⟨pop, push, rs₀, rfl, rfl, hh, hfam, hpf⟩ := h
  have hk' : Wp m P host s' f' (vals (rs₀.reverse ++ push.reverse) ++ rest) Q := by
    simpa only [List.reverse_append] using hk
  simpa only [List.reverse_append] using Wp.detVals hfam hpf hh hk'

section Inversion

variable {s s' : Store H} {f f' : Frame} {rs rs' : List Val}

theorem head_nop (h : exec1 s f rs .nop = some (s', f', rs')) : HeadSpec P s f rs .nop s' f' rs' := by
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ rs = rs' := result_eq h
  exact ⟨[], [], rs, rfl, rfl, .parametric .nop, by simp [famOf], trivial⟩

theorem head_drop (h : exec1 s f rs .drop = some (s', f', rs')) :
    HeadSpec P s f rs .drop s' f' rs' := by
  obtain ⟨⟨v, rs₀⟩, hp, he⟩ := map_eq_some h
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ rs₀ = rs' := result_eq (congrArg some he)
  exact ⟨[v], [], rs₀, popV_eq hp, rfl, .parametric (.drop v), by simp [famOf], trivial⟩

theorem head_localGet {x : LocalIdx} (h : exec1 s f rs (.localGet x) = some (s', f', rs')) :
    HeadSpec P s f rs (.localGet x) s' f' rs' := by
  obtain ⟨v, hv, he⟩ := map_eq_some h
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ v :: rs = rs' := result_eq (congrArg some he)
  exact ⟨[], [v], rs, rfl, rfl, .variable (.localGet (localVal?_eq hv)), by simp [famOf], trivial⟩

theorem head_localSet {x : LocalIdx} (h : exec1 s f rs (.localSet x) = some (s', f', rs')) :
    HeadSpec P s f rs (.localSet x) s' f' rs' := by
  obtain ⟨⟨v, rs₀⟩, hp, he⟩ := bind_eq_some h
  by_cases hx : x.toNat < f.locals.length
  · have he' : some (s, f.setLocal x v, rs₀) = some (s', f', rs') := by
      simpa only [hx, ↓reduceIte] using he
    obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f.setLocal x v = f' ∧ rs₀ = rs' := result_eq he'
    exact ⟨[v], [], rs₀, popV_eq hp, rfl, .variable (.localSet hx), by simp [famOf], trivial⟩
  · have he' : (none : Option (Store H × Frame × List Val)) = some (s', f', rs') := by
      simpa only [hx, ↓reduceIte] using he
    cases he'

theorem head_globalGet {x : GlobalIdx} (h : exec1 s f rs (.globalGet x) = some (s', f', rs')) :
    HeadSpec P s f rs (.globalGet x) s' f' rs' := by
  obtain ⟨⟨a, g⟩, hg, he⟩ := map_eq_some h
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ g.value :: rs = rs' := result_eq (congrArg some he)
  exact ⟨[], [g.value], rs, rfl, rfl, .variable (.globalGet hg), by simp [famOf], trivial⟩

theorem head_globalSet {x : GlobalIdx} (h : exec1 s f rs (.globalSet x) = some (s', f', rs')) :
    HeadSpec P s f rs (.globalSet x) s' f' rs' := by
  obtain ⟨⟨v, rs₀⟩, hp, he⟩ := bind_eq_some h
  obtain ⟨⟨a, g⟩, hg, he'⟩ := map_eq_some he
  obtain ⟨rfl, rfl, rfl⟩ : s.setGlobal a v = s' ∧ f = f' ∧ rs₀ = rs' :=
    result_eq (congrArg some he')
  exact ⟨[v], [], rs₀, popV_eq hp, rfl, .variable (.globalSet hg), by simp [famOf], trivial⟩

theorem head_intUnOp {t : IntType} {op : IntUnOp}
    (h : exec1 s f rs (.intUnOp t op) = some (s', f', rs')) :
    HeadSpec P s f rs (.intUnOp t op) s' f' rs' := by
  obtain ⟨⟨x, rs₁⟩, hp, he⟩ := map_eq_some h
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ .num ⟨.int t, intUnOp t op x⟩ :: rs₁ = rs' :=
    result_eq (congrArg some he)
  exact ⟨[.num ⟨.int t, x⟩], [.num ⟨.int t, intUnOp t op x⟩], rs₁, popInt_eq hp, rfl,
    .numeric .intUnOp, by simp [famOf], trivial⟩

theorem head_intBinOp {t : IntType} {op : IntBinOp}
    (h : exec1 s f rs (.intBinOp t op) = some (s', f', rs')) :
    HeadSpec P s f rs (.intBinOp t op) s' f' rs' := by
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
    exact ⟨_, [.num ⟨.int t, z⟩], rs₂, hrs, rfl, .numeric (.intBinOp hz), by simp [famOf], trivial⟩

theorem head_intTestOp {t : IntType} {op : IntTestOp}
    (h : exec1 s f rs (.intTestOp t op) = some (s', f', rs')) :
    HeadSpec P s f rs (.intTestOp t op) s' f' rs' := by
  obtain ⟨⟨x, rs₁⟩, hp, he⟩ := map_eq_some h
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ Val.i32 (intTestOp t op x) :: rs₁ = rs' :=
    result_eq (congrArg some he)
  exact ⟨[.num ⟨.int t, x⟩], [Val.i32 (intTestOp t op x)], rs₁, popInt_eq hp, rfl,
    .numeric .intTestOp, by simp [famOf], trivial⟩

theorem head_intRelOp {t : IntType} {op : IntRelOp}
    (h : exec1 s f rs (.intRelOp t op) = some (s', f', rs')) :
    HeadSpec P s f rs (.intRelOp t op) s' f' rs' := by
  obtain ⟨⟨y, rs₁⟩, hp₁, he₁⟩ := bind_eq_some h
  obtain ⟨⟨x, rs₂⟩, hp₂, he₂⟩ := map_eq_some he₁
  have hrs : rs = [.num ⟨.int t, y⟩, .num ⟨.int t, x⟩] ++ rs₂ := by
    rw [popInt_eq hp₁, popInt_eq hp₂]; rfl
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ Val.i32 (intRelOp t op x y) :: rs₂ = rs' :=
    result_eq (congrArg some he₂)
  exact ⟨_, [Val.i32 (intRelOp t op x y)], rs₂, hrs, rfl, .numeric .intRelOp, by simp [famOf],
    trivial⟩

theorem head_intLoadFull {t : IntType} {x : MemIdx} {arg : MemArg}
    (h : exec1 s f rs (.intLoad t none x arg) = some (s', f', rs')) :
    HeadSpec P s f rs (.intLoad t none x arg) s' f' rs' := by
  obtain ⟨⟨a, rs₁⟩, hp, he₁⟩ := bind_eq_some h
  obtain ⟨⟨ma, mi⟩, hm, he₂⟩ := bind_eq_some he₁
  obtain ⟨c, hl, he₃⟩ := map_eq_some he₂
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ .num ⟨.int t, c.setWidth t.width⟩ :: rs₁ = rs' :=
    result_eq (congrArg some he₃)
  exact ⟨[Val.i32 a], [.num ⟨.int t, c.setWidth t.width⟩], rs₁, popInt_eq hp, rfl,
    .memory (.loadIntVal (a := .i32) hm hl), by simp [famOf], trivial⟩

theorem head_intLoadPack {t : IntType} {sz : PackSize} {sx : Signedness} {x : MemIdx}
    {arg : MemArg} (h : exec1 s f rs (.intLoad t (some (sz, sx)) x arg) = some (s', f', rs')) :
    HeadSpec P s f rs (.intLoad t (some (sz, sx)) x arg) s' f' rs' := by
  obtain ⟨⟨a, rs₁⟩, hp, he₁⟩ := bind_eq_some h
  obtain ⟨⟨ma, mi⟩, hm, he₂⟩ := bind_eq_some he₁
  obtain ⟨c, hl, he₃⟩ := map_eq_some he₂
  have hstep := MemoryStep.loadPackVal (P := P) (t := t) (sx := sx) (a := .i32) (i := a) hm hl
  rcases sx with _ | _
  · obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ .num ⟨.int t, c.signExtend t.width⟩ :: rs₁ = rs' :=
      result_eq (congrArg some he₃)
    exact ⟨[Val.i32 a], [.num ⟨.int t, c.signExtend t.width⟩], rs₁, popInt_eq hp, rfl,
      .memory hstep, by simp [famOf], trivial⟩
  · obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ .num ⟨.int t, c.setWidth t.width⟩ :: rs₁ = rs' :=
      result_eq (congrArg some he₃)
    exact ⟨[Val.i32 a], [.num ⟨.int t, c.setWidth t.width⟩], rs₁, popInt_eq hp, rfl,
      .memory hstep, by simp [famOf], trivial⟩

theorem head_intStoreFull {t : IntType} {x : MemIdx} {arg : MemArg}
    (h : exec1 s f rs (.intStore t none x arg) = some (s', f', rs')) :
    HeadSpec P s f rs (.intStore t none x arg) s' f' rs' := by
  obtain ⟨⟨c, rs₁⟩, hp₁, he₁⟩ := bind_eq_some h
  obtain ⟨⟨a, rs₂⟩, hp₂, he₂⟩ := bind_eq_some he₁
  obtain ⟨⟨ma, mi⟩, hm, he₃⟩ := bind_eq_some he₂
  obtain ⟨b, hb, he₄⟩ := map_eq_some he₃
  obtain ⟨rfl, rfl, rfl⟩ : s.setMem ma { mi with bytes := b } = s' ∧ f = f' ∧ rs₂ = rs' :=
    result_eq (congrArg some he₄)
  have hrs : rs = [.num ⟨.int t, c⟩, Val.i32 a] ++ rs₂ := by
    rw [popInt_eq hp₁, popInt_eq hp₂]; rfl
  exact ⟨_, [], rs₂, hrs, rfl, .memory (.storeIntVal (a := .i32) hm hb), by simp [famOf], trivial⟩

theorem head_intStorePack {t : IntType} {sz : PackSize} {x : MemIdx} {arg : MemArg}
    (h : exec1 s f rs (.intStore t (some sz) x arg) = some (s', f', rs')) :
    HeadSpec P s f rs (.intStore t (some sz) x arg) s' f' rs' := by
  obtain ⟨⟨c, rs₁⟩, hp₁, he₁⟩ := bind_eq_some h
  obtain ⟨⟨a, rs₂⟩, hp₂, he₂⟩ := bind_eq_some he₁
  obtain ⟨⟨ma, mi⟩, hm, he₃⟩ := bind_eq_some he₂
  obtain ⟨b, hb, he₄⟩ := map_eq_some he₃
  obtain ⟨rfl, rfl, rfl⟩ : s.setMem ma { mi with bytes := b } = s' ∧ f = f' ∧ rs₂ = rs' :=
    result_eq (congrArg some he₄)
  have hrs : rs = [.num ⟨.int t, c⟩, Val.i32 a] ++ rs₂ := by
    rw [popInt_eq hp₁, popInt_eq hp₂]; rfl
  exact ⟨_, [], rs₂, hrs, rfl, .memory (.storePackVal (a := .i32) hm hb), by simp [famOf], trivial⟩

end Inversion

section Wp

variable {m : Corr} {s s' : Store H} {f f' : Frame} {rs rs' : List Val} {rest : List Admin}
  {Q : Post H}

theorem Wp.exec1_intConst {t : IntType} {c : BitVec t.width}
    (h : exec1 s f rs (.intConst t c) = some (s', f', rs'))
    (hk : Wp m P host s' f' (vals rs'.reverse ++ rest) Q) :
    Wp m P host s f (vals rs.reverse ++ .plain (.intConst t c) :: rest) Q := by
  obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f = f' ∧ .num ⟨.int t, c⟩ :: rs = rs' := result_eq h
  simpa only [List.reverse_cons, vals, List.map_append, List.map_cons, List.map_nil,
    Val.toAdmin, List.append_assoc, List.singleton_append] using hk

theorem Wp.exec1_localTee {x : LocalIdx} (h : exec1 s f rs (.localTee x) = some (s', f', rs'))
    (hk : Wp m P host s' f' (vals rs'.reverse ++ rest) Q) :
    Wp m P host s f (vals rs.reverse ++ .plain (.localTee x) :: rest) Q := by
  obtain ⟨⟨v, rs₀⟩, hp, he⟩ := bind_eq_some h
  obtain rfl := popV_eq hp
  by_cases hx : x.toNat < f.locals.length
  · have he' : some (s, f.setLocal x v, v :: rs₀) = some (s', f', rs') := by
      simpa only [hx, ↓reduceIte] using he
    obtain ⟨rfl, rfl, rfl⟩ : s = s' ∧ f.setLocal x v = f' ∧ v :: rs₀ = rs' := result_eq he'
    have hset : Wp m P host s f (vals (rs₀.reverse ++ [v, v]) ++ .plain (.localSet x) :: rest) Q := by
      have h₁ := Silmaril.Wasm.Logic.Hoare.Wp.localSet (m := m) (P := P) (host := host) (s := s)
        (us := rs₀.reverse ++ [v]) (rest := rest) (Q := Q) (v := v) hx
        (by simpa only [List.reverse_cons] using hk)
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using h₁
    simpa only [List.reverse_cons] using Silmaril.Wasm.Logic.Hoare.Wp.localTee hset
  · have he' : (none : Option (Store H × Frame × List Val)) = some (s', f', rs') := by
      simpa only [hx, ↓reduceIte] using he
    cases he'

/-- **One evaluated instruction** in the every-run logic: its result is the only continuation. -/
theorem Wp.exec1 {i : Instr} (h : exec1 s f rs i = some (s', f', rs'))
    (hk : Wp m P host s' f' (vals rs'.reverse ++ rest) Q) :
    Wp m P host s f (vals rs.reverse ++ .plain i :: rest) Q := by
  cases i
  case intConst => exact Wp.exec1_intConst h hk
  case localTee => exact Wp.exec1_localTee h hk
  case intLoad t p x arg =>
    rcases p with _ | ⟨sz, sx⟩
    · exact (head_intLoadFull h).wp hk
    · exact (head_intLoadPack h).wp hk
  case intStore t p x arg =>
    rcases p with _ | sz
    · exact (head_intStoreFull h).wp hk
    · exact (head_intStorePack h).wp hk
  all_goals
    first
    | exact (head_nop h).wp hk | exact (head_drop h).wp hk | exact (head_localGet h).wp hk
    | exact (head_localSet h).wp hk | exact (head_globalGet h).wp hk
    | exact (head_globalSet h).wp hk | exact (head_intUnOp h).wp hk
    | exact (head_intBinOp h).wp hk | exact (head_intTestOp h).wp hk
    | exact (head_intRelOp h).wp hk
    | exact absurd h (by simp only [Silmaril.Wasm.Logic.Core.exec1, reduceCtorEq, not_false_eq_true])

/-- **Symbolic execution of straight-line code** in the every-run logic, either reading, every
profile and host: the evaluated result is the only continuation. -/
theorem Wp.exec {vs : List Val} {is : List Instr}
    (h : match exec s f vs.reverse is with
      | some (s', f', rs') => Wp m P host s' f' (vals rs'.reverse ++ rest) Q
      | none => False) :
    Wp m P host s f (vals vs ++ expression is ++ rest) Q := by
  induction is generalizing s f vs with
  | nil => simpa only [Silmaril.Wasm.Logic.Core.exec_nil, List.reverse_reverse, expression,
      List.map_nil, List.append_nil] using h
  | cons i is ih =>
    cases he : Silmaril.Wasm.Logic.Core.exec1 s f vs.reverse i with
    | none =>
      have hn : exec s f vs.reverse (i :: is) = none := by rw [exec_cons, he]
      rw [hn] at h
      exact h.elim
    | some r =>
      obtain ⟨s₁, f₁, rs₁⟩ := r
      have hs : exec s f vs.reverse (i :: is) = exec s₁ f₁ rs₁ is :=
        Silmaril.Wasm.Logic.Core.exec_cons_of_some he
      have hk : Wp m P host s₁ f₁ (vals rs₁.reverse ++ expression is ++ rest) Q :=
        ih (vs := rs₁.reverse) (by simpa only [List.reverse_reverse, ← hs] using h)
      have h₁ := Wp.exec1 (rs := vs.reverse) (rest := expression is ++ rest) he
        (by simpa only [List.append_assoc] using hk)
      simpa only [List.reverse_reverse, expression, List.map_cons, List.append_assoc,
        List.cons_append] using h₁

/-- `Wp.exec` with the evaluation given as an equation (e.g. proved by `rfl`). -/
theorem Wp.exec_eq {vs : List Val} {is : List Instr}
    (he : Silmaril.Wasm.Logic.Core.exec s f vs.reverse is = some (s', f', rs'))
    (hk : Wp m P host s' f' (vals rs'.reverse ++ rest) Q) :
    Wp m P host s f (vals vs ++ expression is ++ rest) Q :=
  Wp.exec (by rw [he]; exact hk)

end Wp

end Silmaril.Wasm.Examples.Common
