module

public import Silmaril.Compiler.Core.Verified.ArrDesig.Defs
public import Silmaril.Compiler.Core.Verified.IntWrap.Defs
/-! # Structs of `int` members as cells

`struct T { int m₀; …; int m_{N-1}; }` (at least one member, no alignment specifier, no flexible
member) has Cerberus's LP64 layout of `int[N]`: size `4 * N`, alignment `4`, member `k` at offset
`4 * k` (`layout`, `offsets_ok`). So a local of such a type is an `ArrDesig.Arr` object of `N`
`int` cells, and the member designator `let strong p = pure(s) in pure(member_shift(p, T, m_k))`
(`memberOf`) runs to the pointer to cell `k` (`member_runs`), reading nothing.

`cellOf` recognises an array element designator (`ArrDesig.elemOf`) or a member designator;
`cell_runs_arr` is `ArrDesig.elem_runs_arr` for both.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.StructCell

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave (LocalReaches)
open ReturnLit (Eff)
open LoadTask (Touched plain_value plain_pureExpr plain_effectExpr)
open PtrDeref (Runs)
open Mem.Concrete (Tags typeLayout TypeLayout memberOffsets roundUp identifierEq)

/-! ## Layout -/

abbrev Member := Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)

/-- A member of type `int` without an alignment specifier. -/
def intMember : Member → Bool
  | (_, (_, none, _, .mk _ (.basic (.integer (.signed .int))))) => true
  | _ => false

theorem intMember_inv {mem : Member} (h : intMember mem = true) :
    ∃ name attrs q c, mem = (name, (attrs, none, q, .mk c (.basic (.integer (.signed .int))))) := by
  unfold intMember at h
  split at h
  · exact ⟨_, _, _, _, rfl⟩
  · cases h

/-- The members of `struct T` when there is at least one, all `int`, and no flexible member. -/
def members (defs : Map Sym (Loc × TagDefinition)) (T : Sym) : Option (List Member) :=
  match defs.lookup T with
  | some (_, .struct ms none) => if ms.isEmpty = false ∧ ms.all intMember = true then some ms else none
  | _ => none

theorem members_inv {defs : Map Sym (Loc × TagDefinition)} {T : Sym} {ms : List Member}
    (h : members defs T = some ms) :
    ∃ loc, defs.lookup T = some (loc, .struct ms none) ∧ ms.isEmpty = false ∧
      ms.all intMember = true := by
  unfold members at h
  split at h
  · rename_i loc ms' hl
    split at h
    · rename_i hc
      cases h
      exact ⟨loc, hl, hc.1, hc.2⟩
    · cases h
  · cases h

/-- The member list of the layout, from member index `j`. -/
def offsets : List Member → Nat → List (Identifier × Ctype × Int)
  | [], _ => []
  | (f, (_, _, _, t)) :: ms, j => (f, t, 4 * (j : Int)) :: offsets ms (j + 1)

/-- The struct layout fold over `int` members, for any step that places one `int`. -/
theorem fold_ints {ε : Type} (f : List (Identifier × Ctype × Int) × Int × Int → Member →
      Except ε (List (Identifier × Ctype × Int) × Int × Int))
    (step : ∀ acc (j : Nat) (a : Int) (mem : Member), intMember mem = true → 0 ≤ a → a ≤ 4 →
      f (acc, 4 * (j : Int), a) mem =
        .ok (acc ++ [(mem.1, mem.2.2.2.2, 4 * (j : Int))], 4 * ((j + 1 : Nat) : Int), 4)) :
    ∀ (ms : List Member) (acc : List (Identifier × Ctype × Int)) (j : Nat) (off a : Int),
      off = 4 * (j : Int) → ms.all intMember = true → 0 ≤ a → a ≤ 4 →
      ms.foldlM f (acc, off, a) =
        .ok (acc ++ offsets ms j, 4 * ((j + ms.length : Nat) : Int), if ms.isEmpty then a else 4)
  | [], acc, j, off, a, hoff, _, _, _ => by
    subst hoff
    simp [offsets, pure, Except.pure]
  | mem :: ms, acc, j, off, a, hoff, hall, h0, h4 => by
    subst hoff
    simp only [List.all_cons, Bool.and_eq_true] at hall
    rw [List.foldlM_cons, step acc j a mem hall.1 h0 h4]
    simp only [bind, Except.bind]
    rw [fold_ints f step ms _ (j + 1) _ 4 rfl hall.2 (by omega) (by omega)]
    obtain ⟨name, attrs, al, q, t⟩ := mem
    simp only [offsets, List.append_assoc, List.singleton_append, List.length_cons,
      List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, ite_self,
      show j + 1 + ms.length = j + (ms.length + 1) by omega]

/-- **The layout of an all-`int` struct**: that of `int[N]`. -/
theorem layout {tags : Tags} {T : Sym} {ms : List Member} (h : members tags.definitions T = some ms)
    (fuel : Nat) (ann : List Annot) :
    typeLayout (fuel + 2) tags (.mk ann (.struct T)) = .ok ⟨4 * ms.length, 4, offsets ms 0⟩ := by
  obtain ⟨loc, hl, ne, all⟩ := members_inv h
  have hl' : tags.lookup T = some (loc, .struct ms none) := hl
  simp only [typeLayout, hl', bind, Except.bind, pure, Except.pure]
  rw [fold_ints _ ?step ms [] 0 0 0 (by simp) all le_rfl (by omega)]
  · simp only [ne, Bool.false_eq_true, ↓reduceIte, List.nil_append, Nat.zero_add,
      show ¬ ((4 : Int) ≤ 0) by omega, roundUp, Int.mul_emod_right, eq_self]
  case step =>
    intro acc j a mem hm h0 h4
    obtain ⟨name, attrs, q, c, rfl⟩ := intMember_inv hm
    simp only [IntWrap.int_layout, roundUp, Int.mul_emod_right, eq_self, ↓reduceIte, show ¬ ((4 : Int) ≤ 0) by omega]
    refine congrArg Except.ok (Prod.ext rfl (Prod.ext ?_ ?_))
    · simp only; omega
    · simp only; omega

theorem offsets_ok {tags : Tags} {T : Sym} {ms : List Member} (h : members tags.definitions T = some ms) :
    memberOffsets 64 tags T = .ok (offsets ms 0) := by
  obtain ⟨loc, hl, -, -⟩ := members_inv h
  have hl' : tags.lookup T = some (loc, .struct ms none) := hl
  simp [memberOffsets, layout h 62 [], hl', bind, Except.bind, pure, Except.pure]

/-- The index of the first member named `name`. -/
def index (name : Identifier) : List Member → Option Nat
  | [] => none
  | (f, _) :: ms => if identifierEq f name then some 0 else (index name ms).map (· + 1)

theorem find_offsets (name : Identifier) :
    ∀ (ms : List Member) (j k : Nat), index name ms = some k →
      k < ms.length ∧ ∃ f t, (offsets ms j).find? (fun x => identifierEq x.1 name) =
        some (f, t, 4 * ((j + k : Nat) : Int))
  | [], _, _, h => by cases h
  | (f, (attrs, al, q, t)) :: ms, j, k, h => by
    unfold index at h
    by_cases hf : identifierEq f name = true
    · simp only [hf, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨by simp, f, t, by simp [offsets, hf]⟩
    · have hf' : identifierEq f name = false := by simpa using hf
      simp only [hf', Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨k', hk', rfl⟩ := h
      obtain ⟨lt, f', t', found⟩ := find_offsets name ms (j + 1) k' hk'
      refine ⟨by simp only [List.length_cons]; omega, f', t', ?_⟩
      simp only [offsets, List.find?_cons, hf']
      rw [found]
      simp only [Option.some.injEq, Prod.mk.injEq, true_and]
      omega

/-- **A member shift of an all-`int` struct** moves the pointer to the member's cell. -/
theorem shift {tags : Tags} {T : Sym} {ms : List Member} (h : members tags.definitions T = some ms)
    {name : Identifier} {k : Nat} (hk : index name ms = some k) (id addr : Int) :
    primitive (.memberShift T name) [.object (.pointer (.allocated id addr))] tags =
      .ok (.object (.pointer (.allocated id (addr + 4 * (k : Int))))) := by
  obtain ⟨loc, hl, -, -⟩ := members_inv h
  have hl' : tags.lookup T = some (loc, .struct ms none) := hl
  obtain ⟨-, f, t, found⟩ := find_offsets name ms 0 k hk
  refine SubobjectPointer.member tags T name _ f t _ id addr (by simp [hl']) (offsets_ok h) ?_
  simpa using found

/-! ## Designators -/

/-- `let strong p = pure(x) in pure(member_shift(p, T, name))` for an all-`int` struct `T`: the
local `x` and the member's index. -/
def memberOf (file : Program) : Eff → Option (Sym × Int)
  | .mk _ (.sseq (.mk _ (.base (some p, _))) (.mk _ (.pure (.mk _ () (.sym x))))
      (.mk _ (.pure (.mk _ () (.memberShift (.mk _ () (.sym p')) T name))))) =>
      if p'.key = p.key then
        match members file.tagDefs T with
        | some ms => (index name ms).map fun k => (x, (k : Int))
        | none => none
      else none
  | _ => none

theorem memberOf_inv {file : Program} {d : Eff} {x : Sym} {n : Int} (h : memberOf file d = some (x, n)) :
    ∃ (an pn : List Annot) (p : Sym) (pt : BaseType) (xa xp ea pa sa : List Annot) (p' T : Sym)
      (name : Identifier) (ms : List Member) (k : Nat),
      d = .mk an (.sseq (.mk pn (.base (some p, pt))) (.mk xa (.pure (.mk xp () (.sym x))))
        (.mk ea (.pure (.mk pa () (.memberShift (.mk sa () (.sym p')) T name))))) ∧
      p'.key = p.key ∧ members file.tagDefs T = some ms ∧ index name ms = some k ∧ n = k := by
  unfold memberOf at h
  split at h
  · rename_i an pn p pt xa xp x' ea pa sa p' T name
    split at h
    · rename_i hp
      split at h
      · rename_i ms hms
        cases hk : index name ms with
        | none => simp [hk] at h
        | some k =>
          simp [hk] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hp, hms, hk, rfl⟩
      · cases h
    · cases h
  · cases h

theorem memberOf_noCall {file : Program} {d : Eff} {x : Sym} {n : Int}
    (h : memberOf file d = some (x, n)) : hasCCall d = false := by
  obtain ⟨an, pn, p, pt, xa, xp, ea, pa, sa, p', T, name, ms, k, rfl, -⟩ := memberOf_inv h
  simp [hasCCall]

variable {file : Program} {labels : Labels}

/-- **A member designator runs** to the pointer to the member's cell, reading nothing. -/
theorem member_runs {e : Eff} {r : Sym} {n : Int} (h : memberOf file e = some (r, n))
    (I : Mem.Concrete.State → Prop) {env : Env} {id addr : Int}
    (hr : env.lookup r = some (.object (.pointer (.allocated id addr)))) :
    Runs (file := file) (labels := labels) I env e (.object (.pointer (.allocated id (addr + 4 * n)))) := by
  obtain ⟨an, pn, p, pt, xa, xp, ea, pa, sa, p', T, name, ms, k, rfl, hp', hms, hk, rfl⟩ := memberOf_inv h
  refine ⟨by simp [hasCCall], fun k' m _ => ?_⟩
  let ptr : Val := .object (.pointer (.allocated id addr))
  let E : EE := .mk ea (.pure (.mk pa () (.memberShift (.mk sa () (.sym p')) T name)))
  let K := Frame.strongBind (.mk pn (.base (some p, pt))) E env :: k'
  have s₁ : LocalReaches file labels false
      ⟨.effectExpr (.mk an (.sseq (.mk pn (.base (some p, pt))) (.mk xa (.pure (.mk xp () (.sym r)))) E)) env, k', m⟩
      ⟨.effectExpr (.mk xa (.pure (.mk xp () (.sym r)))) env, K, m⟩ :=
    .single (.next (IntWrap.requestAux_sseq m an _ _ E env k' false) (plain_effectExpr _ _))
  obtain ⟨l₁, s₂⟩ := LoadTask.pure_sym_local (file := file) (labels := labels) (wc := false)
    xa xp r env hr K m
  let m₁ : Mem.Concrete.State := {m with currentLocation := l₁}
  let env₁ := extendEnv [(p, ptr)] env
  have s₃ : LocalReaches file labels false ⟨.value ptr, K, m₁⟩ ⟨.effectExpr E env₁, k', m₁⟩ :=
    .single (.next (IntWrap.requestAux_strongBind m₁ pn p pt ptr E env k' false) (plain_effectExpr _ _))
  obtain ⟨l, hreq⟩ := LoadTask.requestAux_pure (file := file) (labels := labels) m₁ ea
    (.mk pa () (.memberShift (.mk sa () (.sym p')) T name)) env₁ k' false
  obtain ⟨l', s₄⟩ := LoadTask.focus_local (plain_pureExpr _ env₁) (by simpa using hreq)
  let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l'}
  have s₅ := SubobjectPointer.member_local (file := file) (labels := labels) pa
    (.mk sa () (.sym p')) T name env₁ (.diagnosticLocation m₁.currentLocation :: k') m₂ false
    id addr (4 * (k : Int)) (.cons (.sym (ConvInt.lookup_one hp')) .nil)
    (shift (tags := PureEval.tagsOf file m₂) hms hk id addr)
  refine ⟨[], m₂, [], .inl ⟨rfl, rfl⟩, by simp, ⟨l', m.lastUsed, rfl⟩,
    s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.tail ?_))))⟩
  exact .next (Interleave.requestAux_value_diagnostic file labels _ _ _ k' false) (plain_value _)

/-- An array element designator or a member designator of an all-`int` struct. -/
def cellOf (file : Program) (e : Eff) : Option (Sym × Int) :=
  match ArrDesig.elemOf e with
  | some c => some c
  | none => memberOf file e

theorem cellOf_noCall {file : Program} {e : Eff} {r : Sym} {n : Int} (h : cellOf file e = some (r, n)) :
    hasCCall e = false := by
  unfold cellOf at h
  split at h
  · rename_i c hc
    cases h
    exact ArrDesig.elemOf_noCall hc
  · exact memberOf_noCall h

/-- **The cell `n`** of an array or all-`int` struct object `r`, for `0 ≤ n < N`. -/
theorem cell_runs_arr {e : Eff} {r : Sym} {n : Int} (h : cellOf file e = some (r, n))
    (I : Mem.Concrete.State → Prop) (hI : ∀ m m', I m → Touched m m' → I m') {env : Env}
    {id addr : Int} {N : Nat} (hr : env.lookup r = some (.object (.pointer (.allocated id addr))))
    (arr : ∀ m, I m → ArrDesig.Arr m id addr N) (h0 : 0 ≤ n) (hn : n < N) (aligned : addr % 4 = 0) :
    Runs (file := file) (labels := labels) I env e (.object (.pointer (.allocated id (addr + 4 * n)))) := by
  unfold cellOf at h
  split at h
  · rename_i c hc
    cases h
    exact ArrDesig.elem_runs_arr hc I hI hr arr h0 hn aligned
  · exact member_runs h I hr

end Silmaril.Compile.Core.Verified.StructCell
