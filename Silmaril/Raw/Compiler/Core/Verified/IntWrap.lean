module

public import Silmaril.Compiler.Core.Verified.SubobjectTask.Defs
public import Silmaril.Compiler.Core.Verified.SubobjectPointer.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-! # Structs wrapping one `int`

`struct T { int x; }`, and structs whose only member is such a struct (`struct S2 { struct S1 s1; }`),
have Cerberus's LP64 layout of an `int`: size `4`, alignment `4`, the member at offset `0`
(`wraps_layout`). A local of such a type is one `int` slot, and a member designator of it
(`s.x`, `s2.s1.x`) is its own address: `member_shift(p, T, x)` at offset `0` (`wraps_shift`).

`desig file d = some x`: `d` is `pure(x)` or `let strong p = d' in pure(member_shift(p, T, f))`
with `d'` a designator of `x` and `f` the member of a wrapper `T`. `desig_runs`: from any memory,
local steps take `d` to the pointer `x` holds, reading nothing. `load_desig`: the read
`let weak p = d in load(int, p)` of an `int` slot through such a designator.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.IntWrap

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf argState)
open Silmaril.Cerberus.Core.Interleave (LocalReaches)
open ReturnLit (Eff)
open LoadTask (Touched plain_value plain_pureExpr plain_effectExpr)

/-! ## Layout -/

/-- The struct `T` has exactly one member, of type `int` or of a struct type wrapping an `int` (at
most `d` levels), with no alignment specifier and no flexible member: that member and its type. -/
def wraps (defs : Map Sym (Loc × TagDefinition)) : Nat → Sym → Option (Identifier × Ctype)
  | 0, _ => none
  | d + 1, T => match defs.lookup T with
    | some (_, .struct [(f, (_, none, _, .mk c (.basic (.integer (.signed .int)))))] none) =>
        some (f, .mk c (.basic (.integer (.signed .int))))
    | some (_, .struct [(f, (_, none, _, .mk c (.struct T')))] none) =>
        (wraps defs d T').map fun _ => (f, .mk c (.struct T'))
    | _ => none

open Mem.Concrete (Tags typeLayout TypeLayout memberOffsets roundUp)

theorem int_layout (fuel : Nat) (tags : Tags) (c : List Annot) :
    typeLayout (fuel + 1) tags (.mk c (.basic (.integer (.signed .int)))) = .ok ⟨4, 4, []⟩ := by
  simp [typeLayout, Mem.Concrete.registeredIntegerLayout, Mem.Concrete.registeredInteger,
    Mem.Concrete.integerLayout, Mem.Concrete.baseWidth, bind, pure, Except.pure]

/-- A struct whose only member has the layout of an `int` has the layout of an `int`. -/
theorem struct_one (fuel : Nat) (tags : Tags) {T : Sym} {loc : Loc} {f : Identifier}
    {attrs : Attributes} {q : Qualifiers} {ty : Ctype}
    (hl : tags.lookup T = some (loc, .struct [(f, (attrs, none, q, ty))] none)) {ms : List _}
    (hty : typeLayout fuel tags ty = .ok ⟨4, 4, ms⟩) (ann : List Annot) :
    typeLayout (fuel + 1) tags (.mk ann (.struct T)) = .ok ⟨4, 4, [(f, ty, 0)]⟩ := by
  simp [typeLayout, hl, hty, roundUp, bind, Except.bind, pure, Except.pure, List.foldlM]

theorem wraps_lookup {defs : Map Sym (Loc × TagDefinition)} :
    {d : Nat} → {T : Sym} → {f : Identifier} → {ty : Ctype} → wraps defs d T = some (f, ty) →
      ∃ loc attrs q, defs.lookup T = some (loc, .struct [(f, (attrs, none, q, ty))] none)
  | 0, _, _, _, h => by cases h
  | d + 1, T, f, ty, h => by
    unfold wraps at h
    split at h
    · rename_i loc f' attrs q c hl
      cases h
      exact ⟨_, _, _, hl⟩
    · rename_i loc f' attrs q c T' hl
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨_, -, rfl, rfl⟩ := h
      exact ⟨_, _, _, hl⟩
    · cases h

/-- **The layout of a wrapper**: that of an `int`, its member at offset `0`. -/
theorem wraps_layout {defs : Map Sym (Loc × TagDefinition)} {tags : Tags}
    (hdefs : tags.definitions = defs) :
    (d : Nat) → {T : Sym} → {f : Identifier} → {ty : Ctype} → wraps defs d T = some (f, ty) →
      (fuel : Nat) → d < fuel → (ann : List Annot) →
      typeLayout fuel tags (.mk ann (.struct T)) = .ok ⟨4, 4, [(f, ty, 0)]⟩
  | 0, _, _, _, h, _, _, _ => by cases h
  | d + 1, T, f, ty, h, fuel + 1, hf, ann => by
    obtain ⟨loc, attrs, q, hl⟩ := wraps_lookup h
    have hl' : tags.lookup T = some (loc, .struct [(f, (attrs, none, q, ty))] none) := by
      rw [Mem.Concrete.Tags.lookup, hdefs]; exact hl
    unfold wraps at h
    split at h
    · cases h
      obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
      exact struct_one _ tags hl' (int_layout fuel' tags _) ann
    · rename_i c T' _
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨f', ty'⟩, h', rfl, rfl⟩ := h
      exact struct_one _ tags hl' (wraps_layout hdefs d h' fuel (by omega) c) ann
    · cases h

theorem wraps_offsets {defs : Map Sym (Loc × TagDefinition)} {tags : Tags}
    (hdefs : tags.definitions = defs) {d : Nat} {T : Sym} {f : Identifier} {ty : Ctype}
    (h : wraps defs d T = some (f, ty)) (hd : d < 64) :
    memberOffsets 64 tags T = .ok [(f, ty, 0)] := by
  obtain ⟨loc, attrs, q, hl⟩ := wraps_lookup h
  have hl' : tags.lookup T = some (loc, .struct [(f, (attrs, none, q, ty))] none) := by
    rw [Mem.Concrete.Tags.lookup, hdefs]; exact hl
  simp [memberOffsets, wraps_layout hdefs d h 64 hd [], hl', bind, Except.bind, pure, Except.pure]

/-- **A member shift of a wrapper** keeps the pointer. -/
theorem wraps_shift {defs : Map Sym (Loc × TagDefinition)} {tags : Tags}
    (hdefs : tags.definitions = defs) {d : Nat} {T : Sym} {f name : Identifier} {ty : Ctype}
    (h : wraps defs d T = some (f, ty)) (hd : d < 64) (hname : f.key = name.key) (id addr : Int) :
    primitive (.memberShift T name) [.object (.pointer (.allocated id addr))] tags =
      .ok (.object (.pointer (.allocated id (addr + 0)))) := by
  obtain ⟨loc, attrs, q, hl⟩ := wraps_lookup h
  have hl' : tags.lookup T = some (loc, .struct [(f, (attrs, none, q, ty))] none) := by
    rw [Mem.Concrete.Tags.lookup, hdefs]; exact hl
  refine SubobjectPointer.member tags T name _ f ty 0 id addr (by simp [hl'])
    (wraps_offsets hdefs h hd) ?_
  simp [Mem.Concrete.identifierEq, hname]

/-! ## Designators -/

/-- The depth bound of the wrappers the recognisers accept. -/
abbrev depth : Nat := 8

/-- `d` designates the `int` slot of the local `x`: `pure(x)`, or a member shift (offset `0`) of a
wrapper over a designator of `x`. -/
def desig (file : Program) : Eff → Option Sym
  | .mk _ (.pure (.mk _ () (.sym x))) => some x
  | .mk _ (.sseq (.mk _ (.base (some p, _))) d
      (.mk _ (.pure (.mk _ () (.memberShift (.mk _ () (.sym p')) T name))))) =>
      match wraps file.tagDefs depth T with
      | some (f, _) => if p'.key = p.key ∧ f.key = name.key then desig file d else none
      | none => none
  | _ => none
termination_by e => sizeOf e
decreasing_by all_goals (simp_all; omega)

theorem desig_inv {file : Program} {d : Eff} {x : Sym} (h : desig file d = some x) :
    (∃ an pa, d = .mk an (.pure (.mk pa () (.sym x)))) ∨
    ∃ (an pn : List Annot) (p : Sym) (pt : BaseType) (d' : Eff) (ea pa sa : List Annot) (p' T : Sym)
      (name : Identifier) (f : Identifier) (ty : Ctype),
      d = .mk an (.sseq (.mk pn (.base (some p, pt))) d'
        (.mk ea (.pure (.mk pa () (.memberShift (.mk sa () (.sym p')) T name))))) ∧
      wraps file.tagDefs depth T = some (f, ty) ∧ p'.key = p.key ∧ f.key = name.key ∧
      desig file d' = some x ∧ sizeOf d' < sizeOf d := by
  unfold desig at h
  split at h
  · cases h; exact .inl ⟨_, _, rfl⟩
  · rename_i an pn p pt d' ea pa sa p' T name
    split at h
    · rename_i f ty hw
      split at h
      · rename_i hc
        exact .inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hw, hc.1, hc.2, h, by simp; omega⟩
      · cases h
    · cases h
  · cases h

theorem desig_noCall {file : Program} : {d : Eff} → {x : Sym} → desig file d = some x →
    hasCCall d = false
  | d, x, h => by
    rcases desig_inv h with ⟨an, pa, rfl⟩ | ⟨an, pn, p, pt, d', ea, pa, sa, p', T, name, f, ty, rfl,
      -, -, -, h', hs⟩
    · rw [hasCCall.eq_def]
    · have := desig_noCall h'
      rw [hasCCall.eq_def]
      simp only [this, Bool.false_or]
      rw [hasCCall.eq_def]
termination_by d => sizeOf d
decreasing_by all_goals omega

variable {file : Program} {labels : Labels}

theorem requestAux_sseq (m : Mem.Concrete.State) (ann : List Annot) (pat : Pattern Sym) (a b : EE)
    (env : Env) (k : List Frame) (wc : Bool) :
    requestAux file labels m (.effectExpr (.mk ann (.sseq pat a b)) env) k wc =
      .next (.effectExpr a env) (.strongBind pat b env :: k) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem requestAux_strongBind (m : Mem.Concrete.State) (ann : List Annot) (p : Sym) (ty : BaseType)
    (v : Val) (b : EE) (env : Env) (k : List Frame) (wc : Bool) :
    requestAux file labels m (.value v) (.strongBind (.mk ann (.base (some p, ty))) b env :: k) wc =
      .next (.effectExpr b (extendEnv [(p, v)] env)) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, matchPattern]

/-- **A designator runs** to the pointer its local holds, reading nothing. -/
theorem desig_runs : {d : Eff} → {x : Sym} → desig file d = some x → {env : Env} → {id addr : Int} →
    env.lookup x = some (.object (.pointer (.allocated id addr))) →
    ∀ (k : List Frame) (m : Mem.Concrete.State), ∃ m', Touched m m' ∧
      LocalReaches file labels false ⟨.effectExpr d env, k, m⟩
        ⟨.value (.object (.pointer (.allocated id addr))), k, m'⟩
  | d, x, h, env, id, addr, hx, k, m => by
    rcases desig_inv h with ⟨an, pa, rfl⟩ | ⟨an, pn, p, pt, d', ea, pa, sa, p', T, name, f, ty, rfl,
      hw, hp', hname, h', hs⟩
    · obtain ⟨l', run⟩ := LoadTask.pure_sym_local (file := file) (labels := labels) (wc := false)
        an pa x env hx k m
      exact ⟨_, ⟨l', m.lastUsed, rfl⟩, run⟩
    · let ptr : Val := .object (.pointer (.allocated id addr))
      let E : EE := .mk ea (.pure (.mk pa () (.memberShift (.mk sa () (.sym p')) T name)))
      let K := Frame.strongBind (.mk pn (.base (some p, pt))) E env :: k
      have s₁ : LocalReaches file labels false
          ⟨.effectExpr (.mk an (.sseq (.mk pn (.base (some p, pt))) d' E)) env, k, m⟩
          ⟨.effectExpr d' env, K, m⟩ :=
        .single (.next (requestAux_sseq m an _ d' E env k false) (plain_effectExpr _ _))
      obtain ⟨m₁, t₁, s₂⟩ := desig_runs h' hx K m
      let env₁ := extendEnv [(p, ptr)] env
      have s₃ : LocalReaches file labels false ⟨.value ptr, K, m₁⟩ ⟨.effectExpr E env₁, k, m₁⟩ :=
        .single (.next (requestAux_strongBind m₁ pn p pt ptr E env k false) (plain_effectExpr _ _))
      obtain ⟨l, hr⟩ := LoadTask.requestAux_pure (file := file) (labels := labels) m₁ ea
        (.mk pa () (.memberShift (.mk sa () (.sym p')) T name)) env₁ k false
      obtain ⟨l', s₄⟩ := LoadTask.focus_local (plain_pureExpr _ env₁) (by simpa using hr)
      let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l'}
      have s₅ := SubobjectPointer.member_local (file := file) (labels := labels) pa
        (.mk sa () (.sym p')) T name env₁ (.diagnosticLocation m₁.currentLocation :: k) m₂ false
        id addr 0 (.cons (.sym (ConvInt.lookup_one hp')) .nil)
        (wraps_shift rfl hw (by decide) hname id addr)
      rw [Int.add_zero] at s₅
      refine ⟨m₂, t₁.trans ⟨l', m₁.lastUsed, rfl⟩, s₁.trans (s₂.trans (s₃.trans (s₄.trans
        (s₅.tail ?_))))⟩
      exact .next (Interleave.requestAux_value_diagnostic file labels _ _ _ k false) (plain_value _)
termination_by d => sizeOf d
decreasing_by all_goals omega

/-- A designator is a read-only task with the pointer as its value. -/
theorem desig_readTask (I : Mem.Concrete.State → Prop) {d : Eff} {x : Sym}
    (h : desig file d = some x) {env : Env} {id addr : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr)))) :
    LoadTask.ReadTask (file := file) (labels := labels) I env d
      (.object (.pointer (.allocated id addr))) := by
  refine ⟨desig_noCall h, fun m _ => ?_⟩
  obtain ⟨m', t, run⟩ := desig_runs (file := file) (labels := labels) h hx [] m
  exact ⟨[], m', by simp, t, [], run, rfl⟩

/-- **The read of an `int` slot through a designator**: `let weak p = d in load(int, p')`. -/
theorem load_desig (a0 pa la a3 c1 a4 : List Annot) (pt : BaseType) (p p' : Sym) (d : Eff)
    (l : Loc) (u : Unit) (hp' : p'.key = p.key) {x : Sym} (hd : desig file d = some x)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hn : Mem.Concrete.IntRange n) (slot : Locals.Slot m id addr n) :
    ∃ a m', a.write = false ∧ Touched m m' ∧
      LocalReaches file labels false
        ⟨.effectExpr (.mk a0 (.wseq (.mk pa (.base (some p, pt))) d
          (.mk la (.action (.mk .pos (.mk l u (.load (Locals.intVal a3 c1) (.mk a4 () (.sym p'))
            .na))))))) env, k, m⟩
        ⟨.value (.loaded (.specified (.integer n))), .annotations [a] :: k, m'⟩ := by
  let ptr : Val := .object (.pointer (.allocated id addr))
  let LOAD : EE := .mk la (.action (.mk .pos (.mk l u
    (.load (Locals.intVal a3 c1) (.mk a4 () (.sym p')) .na))))
  let env₁ := extendEnv [(p, ptr)] env
  have s₁ : LocalReaches file labels false
      ⟨.effectExpr (.mk a0 (.wseq (.mk pa (.base (some p, pt))) d LOAD)) env, k, m⟩
      ⟨.effectExpr d env, .effectBind (.mk pa (.base (some p, pt))) LOAD env :: k, m⟩ :=
    .single (.next (LoadTask.requestAux_wseq _ _ _ _ _ _ _ _) (plain_effectExpr _ _))
  obtain ⟨m₁, t₁, s₂⟩ := desig_runs (file := file) (labels := labels) hd hx
    (.effectBind (.mk pa (.base (some p, pt))) LOAD env :: k) m
  have s₃ : LocalReaches file labels false
      ⟨.value ptr, .effectBind (.mk pa (.base (some p, pt))) LOAD env :: k, m₁⟩
      ⟨.effectExpr LOAD env₁, k, m₁⟩ :=
    .single (.next (LoadTask.requestAux_bind _ _ _ _ _ _ _ _ _) (plain_effectExpr _ _))
  have slot₁ : IntSubobject.Slot m₁ id addr n := (IntSubobject.Slot.ofSlot slot).touched t₁
  obtain ⟨a, ha, s₄⟩ := SubobjectTask.load_local (file := file) (labels := labels) la l u
    (Locals.intVal a3 c1) (.mk a4 () (.sym p')) env₁ k m₁ c1 slot₁ hn
    (.cons (Locals.eval_intVal _ env₁ a3 c1) (.cons (.sym (ConvInt.lookup_one hp')) .nil))
  refine ⟨a, _, ha, t₁.trans ?_, s₁.trans (s₂.trans (s₃.trans s₄))⟩
  exact (LoadTask.focusMemory_touched la m₁).trans
    ⟨(ReturnConst.focusMemory la m₁).currentLocation, some id, rfl⟩

end Silmaril.Compile.Core.Verified.IntWrap
