module

public import Silmaril.Wasm.V2.Validation.Modules

/-!
# WebAssembly 2.0 validation: inversion

The inversion lemmas the 2.0 soundness proof needs, stated against
`specification/wasm-2.0/6-typing.spectec` at WebAssembly/spec revision
`608711107b7f1edb13efd57b7d79b49477462d36`. Line references of the form
`6-typing:NN` point into that file.

## Why naive `cases` is not enough

`InstrsOk` (`6-typing:156-177`) has two *non-syntax-directed* rules:
`Instrs_ok/sub` (`6-typing:168`) weakens the assigned type along
`InstrType.Sub`, and `Instrs_ok/frame` (`6-typing:175`) prefixes both sides with
an untouched stack `t*`. Either may be applied at any point and any number of
times, so a derivation of `InstrsOk C [i] it` need not end in `Instrs_ok/instr`,
and a derivation of `InstrsOk C (is₁ ++ is₂) it` need not end in
`Instrs_ok/seq`. Every inversion lemma below is therefore stated *modulo* the
closure of its conclusion under those two rules.

That closure has a normal form. Framing a subsumption is a subsumption of a
framing — `CResultType.sub_append` with a reflexive left operand turns
`sub` after `frame` into `frame` after `sub` — and two framings compose into
one, so every chain of `sub`s and `frame`s collapses to a single `frame`
followed by a single `sub`. `InstrType.Weaken` is exactly that normal form:

```
InstrType.Weaken it it'  ↔  ∃ ts, InstrType.Sub ⟨ts ++ it.params, ts ++ it.results⟩ it'
```

`InstrsOk.weaken` says `InstrsOk` is closed under it, and
`InstrType.weaken_refl`/`weaken_trans` say it is a preorder.

## `InstrOk` needs no such care

`InstrOk` (`6-typing:142`) *is* syntax directed: it has one rule per instruction
form and no subsumption rule of its own — in 2.0 subsumption lives entirely in
`Instrs_ok/sub`. So `cases` works on `InstrOk`, and the per-instruction lemmas
of the `InstrOk` namespace below are one-liners. The `InstrsOk` corollaries that
follow them compose those with `InstrsOk.singleton_inv`, which is where the
weakening is absorbed.

## `InstrOk.immediatesValid`

The lemma that a well-typed instruction satisfies
`Silmaril.Wasm.V2.Instr.immediatesValid` — the one that makes the `VCVTOP`
side-condition deviation pay off — is already stated *and proved* at the end of
`Silmaril/Wasm/V2/Validation/Instructions.lean`, together with its `InstrsOk`
form, because the induction needs both motives of the mutual block. This file
only adds the `ExprOk` corollary, `ExprOk.immediatesValid`.

## Contents

* `InstrType.Weaken` and `InstrsOk.weaken` — the closure described above;
* `InstrsOk.{nil_inv, singleton_inv, append_inv, cons_inv, singleton_elim}` —
  the structural inversions;
* `Instr.valueType?`, `InstrsOk.values_inv` and `InstrsOk.values_iff` — canonical
  forms for a sequence of self-describing constant instructions;
* the `InstrOk.*_inv` family — one per instruction form, recovering exactly the
  premises `8-reduction` needs: the mutability of `global.set`, the `FUNCREF`
  element type of `call_indirect`, the matching element types of `table.copy`
  and `table.init`, `C.MEMS[0]` for every memory instruction, `x \in C.REFS`
  for `ref.func`, and the alignment bounds of every load and store;
* `InstrsOk.*` corollaries of those, for the one-instruction sequences the
  soundness proof actually meets.

Nothing in this file is `sorry`ed.

No deviation from the pinned SpecTec source is taken in this file.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Validation

/-! ## Framing and subsumption, packaged -/

namespace InstrType

/-- Subtyping of instruction types is compatible with framing: `Instrs_ok/frame`
(`6-typing:175`) applied to both sides of an `Instrs_ok/sub` (`6-typing:168`)
premise. This is what lets a `sub`-then-`frame` chain be reordered. -/
theorem Sub.frame {a b : InstrType} (h : InstrType.Sub a b) (ts : CResultType) :
    InstrType.Sub ⟨ts ++ a.params, ts ++ a.results⟩ ⟨ts ++ b.params, ts ++ b.results⟩ :=
  ⟨CResultType.sub_append (CResultType.sub_refl ts) h.1,
    CResultType.sub_append (CResultType.sub_refl ts) h.2⟩

/-- The normal form of a chain of `Instrs_ok/frame` and `Instrs_ok/sub` steps:
one framing by `ts`, then one subsumption. `Weaken it it'` holds when `it'` is
reachable from `it` by such a chain. -/
def Weaken (it it' : InstrType) : Prop :=
  ∃ ts : CResultType, InstrType.Sub ⟨ts ++ it.params, ts ++ it.results⟩ it'

theorem weaken_refl (it : InstrType) : InstrType.Weaken it it :=
  ⟨[], InstrType.sub_refl it⟩

/-- A subsumption is a weakening with an empty frame. -/
theorem Sub.weaken {it it' : InstrType} (h : InstrType.Sub it it') :
    InstrType.Weaken it it' := ⟨[], h⟩

/-- A framing is a weakening with a reflexive subsumption. -/
theorem weaken_frame (ts t₁ t₂ : CResultType) :
    InstrType.Weaken ⟨t₁, t₂⟩ ⟨ts ++ t₁, ts ++ t₂⟩ :=
  ⟨ts, InstrType.sub_refl _⟩

/-- Shrinking the parameters is a weakening: `Instrs_ok/sub` (`6-typing:168`) is
contravariant in `t_1*`. -/
theorem weaken_of_sub_params {a b c : CResultType} (h : CResultType.Sub a b) :
    InstrType.Weaken ⟨b, c⟩ ⟨a, c⟩ := ⟨[], h, CResultType.sub_refl c⟩

/-- Growing the results is a weakening: `Instrs_ok/sub` (`6-typing:168`) is
covariant in `t_2*`. -/
theorem weaken_of_sub_results {a b c : CResultType} (h : CResultType.Sub b c) :
    InstrType.Weaken ⟨a, b⟩ ⟨a, c⟩ := ⟨[], CResultType.sub_refl a, h⟩

theorem weaken_trans {a b c : InstrType} (h₁ : InstrType.Weaken a b)
    (h₂ : InstrType.Weaken b c) : InstrType.Weaken a c := by
  obtain ⟨ts, hts⟩ := h₁
  obtain ⟨us, hus⟩ := h₂
  refine ⟨us ++ ts, ?_⟩
  have := InstrType.sub_trans (hts.frame us) hus
  simpa [List.append_assoc] using this

end InstrType

namespace InstrsOk

/-- `Instrs_ok` is closed under `InstrType.Weaken`: this is `Instrs_ok/frame`
(`6-typing:175`) followed by `Instrs_ok/sub` (`6-typing:168`). -/
theorem weaken {C : Context} {is : List Instr} {it it' : InstrType}
    (h : InstrsOk C is it) (hw : InstrType.Weaken it it') : InstrsOk C is it' := by
  obtain ⟨ts, hts⟩ := hw
  obtain ⟨t₁, t₂⟩ := it
  exact (InstrsOk.frame (ts := ts) h).sub hts

/-! ## Structural inversion -/

/-- Inversion for the empty sequence: the only types it has are the coercions.
This is the forward direction of `InstrsOk.nil_iff`. -/
theorem nil_inv {C : Context} {it : InstrType} (h : InstrsOk C [] it) :
    CResultType.Sub it.params it.results := by
  obtain ⟨t₁, t₂⟩ := it
  exact InstrsOk.nil_iff.mp h

/-- Inversion for a one-instruction sequence: some `Instr_ok` type for the
instruction weakens to the given one. The `Instrs_ok/instr` rule
(`6-typing:159`) need not be the last rule applied, so the conclusion is stated
modulo `InstrType.Weaken`. -/
theorem singleton_inv {C : Context} {i : Instr} {it : InstrType}
    (h : InstrsOk C [i] it) : ∃ it', InstrOk C i it' ∧ InstrType.Weaken it' it := by
  have aux : ∀ {C' : Context} {is : List Instr} {u : InstrType}, InstrsOk C' is u →
      ∀ j : Instr, is = [j] → ∃ u', InstrOk C' j u' ∧ InstrType.Weaken u' u := by
    intro C' is u h'
    induction h' using InstrsOk.rec (motive_1 := fun _ _ _ _ => True) with
    | empty => intro j hj; exact absurd hj (by simp)
    | instr hi =>
        intro j hj
        simp only [List.cons.injEq, and_true] at hj
        subst hj
        exact ⟨_, hi, InstrType.weaken_refl _⟩
    | seq h₁ h₂ ih₁ ih₂ =>
        intro j hj
        rcases List.append_eq_singleton_iff.mp hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · obtain ⟨u', hu, hw⟩ := ih₂ j rfl
          exact ⟨u', hu, InstrType.weaken_trans hw
            (InstrType.weaken_of_sub_params (InstrsOk.nil_iff.mp h₁))⟩
        · obtain ⟨u', hu, hw⟩ := ih₁ j rfl
          exact ⟨u', hu, InstrType.weaken_trans hw
            (InstrType.weaken_of_sub_results (InstrsOk.nil_iff.mp h₂))⟩
    | sub _ hs ih =>
        intro j hj
        obtain ⟨u', hu, hw⟩ := ih j hj
        exact ⟨u', hu, InstrType.weaken_trans hw hs.weaken⟩
    | frame _ ih =>
        intro j hj
        obtain ⟨u', hu, hw⟩ := ih j hj
        exact ⟨u', hu, InstrType.weaken_trans hw (InstrType.weaken_frame _ _ _)⟩
    | _ => trivial
  exact aux h i rfl

/-- Inversion for a concatenation: the sequence splits at some intermediate
stack type. `Instrs_ok/seq` (`6-typing:163`) need not be the last rule applied,
and need not split at this particular point, so this is a genuine theorem rather
than a repackaging of the constructor. -/
theorem append_inv {C : Context} {is₁ is₂ : List Instr} {t₁ t₃ : CResultType}
    (h : InstrsOk C (is₁ ++ is₂) ⟨t₁, t₃⟩) :
    ∃ t₂, InstrsOk C is₁ ⟨t₁, t₂⟩ ∧ InstrsOk C is₂ ⟨t₂, t₃⟩ := by
  have aux : ∀ {C' : Context} {is : List Instr} {u : InstrType}, InstrsOk C' is u →
      ∀ as bs : List Instr, is = as ++ bs →
        ∃ m, InstrsOk C' as ⟨u.params, m⟩ ∧ InstrsOk C' bs ⟨m, u.results⟩ := by
    intro C' is u h'
    induction h' using InstrsOk.rec (motive_1 := fun _ _ _ _ => True) with
    | empty =>
        intro as bs hb
        obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hb.symm
        exact ⟨[], InstrsOk.empty, InstrsOk.empty⟩
    | instr hi =>
        intro as bs hb
        rcases List.append_eq_singleton_iff.mp hb.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨_, InstrsOk.nil_iff.mpr (CResultType.sub_refl _), InstrsOk.instr hi⟩
        · exact ⟨_, InstrsOk.instr hi, InstrsOk.nil_iff.mpr (CResultType.sub_refl _)⟩
    | seq h₁ h₂ ih₁ ih₂ =>
        intro as bs hb
        rcases List.append_eq_append_iff.mp hb with ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
        · obtain ⟨m, hk, hbs⟩ := ih₂ k bs rfl
          exact ⟨m, InstrsOk.seq h₁ hk, hbs⟩
        · obtain ⟨m, has, hk⟩ := ih₁ as k rfl
          exact ⟨m, has, InstrsOk.seq hk h₂⟩
    | sub _ hs ih =>
        intro as bs hb
        obtain ⟨m, ha, hb'⟩ := ih as bs hb
        exact ⟨m, ha.sub ⟨hs.1, CResultType.sub_refl m⟩,
          hb'.sub ⟨CResultType.sub_refl m, hs.2⟩⟩
    | frame _ ih =>
        intro as bs hb
        obtain ⟨m, ha, hb'⟩ := ih as bs hb
        exact ⟨_, InstrsOk.frame ha, InstrsOk.frame hb'⟩
    | _ => trivial
  exact aux h is₁ is₂ rfl

/-- Inversion for a non-empty sequence: the head has an `Instr_ok` type that
weakens to a prefix of the whole type, and the tail continues from there. -/
theorem cons_inv {C : Context} {i : Instr} {is : List Instr} {t₁ t₃ : CResultType}
    (h : InstrsOk C (i :: is) ⟨t₁, t₃⟩) :
    ∃ t₂ it, InstrOk C i it ∧ InstrType.Weaken it ⟨t₁, t₂⟩ ∧ InstrsOk C is ⟨t₂, t₃⟩ := by
  obtain ⟨t₂, h₁, h₂⟩ := InstrsOk.append_inv (is₁ := [i]) (is₂ := is) h
  obtain ⟨it, hit, hw⟩ := h₁.singleton_inv
  exact ⟨t₂, it, hit, hw, h₂⟩

/-- Eliminate a one-instruction sequence down to its `Instr_ok` premise. Every
per-instruction corollary below is an instance of this: the premises of
`Instr_ok` are properties of the context and of the immediates alone, so they
survive the weakening that `singleton_inv` exposes. -/
theorem singleton_elim {C : Context} {i : Instr} {it : InstrType} {P : Prop}
    (h : InstrsOk C [i] it) (hP : ∀ it', InstrOk C i it' → P) : P := by
  obtain ⟨it', h', -⟩ := h.singleton_inv
  exact hP it' h'

end InstrsOk

/-! ## Canonical forms for constant instructions

The value-producing instructions whose type is determined by their immediates:
`CONST`, `VCONST` and `REF.NULL` (`Instr_ok/const`, `/vconst`, `/ref.null` at
`6-typing:264`, `304`, `291`). `REF.FUNC` is deliberately excluded — it is an
`Instr_const` (`6-typing:552`) and produces a value, but its `Instr_ok` rule
(`6-typing:294`) has context premises, so it is not self-describing. -/

/-- The value type a self-describing constant instruction produces, if it is
one. -/
def Instr.valueType? : Instr → Option ValType
  | .intConst t _ => some (.num (.int t))
  | .floatConst t _ => some (.num (.float t))
  | .vecConst _ => some (.vec .v128)
  | .refNull rt => some (.ref rt)
  | _ => none

/-- A self-describing constant instruction has exactly the type its immediates
name. -/
theorem InstrOk.of_valueType? {C : Context} {i : Instr} {t : ValType}
    (h : Instr.valueType? i = some t) : InstrOk C i ⟨[], [.val t]⟩ := by
  cases i <;> simp only [Instr.valueType?, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> constructor

/-- A well-typed self-describing constant instruction has *exactly* the type its
immediates name: `Instr_ok` assigns it no other. -/
theorem InstrOk.valueType?_eq {C : Context} {i : Instr} {t : ValType} {it : InstrType}
    (hv : Instr.valueType? i = some t) (h : InstrOk C i it) : it = ⟨[], [.val t]⟩ := by
  cases i <;> simp only [Instr.valueType?, Option.some.injEq, reduceCtorEq] at hv <;>
    subst hv <;> cases h <;> rfl

/-- Splitting a `Resulttype_sub` (`6-typing:80`) along a concatenation on the
left: pointwise relations split where the sequence does. -/
theorem CResultType.sub_append_left_inv : ∀ {a b c : CResultType},
    CResultType.Sub (a ++ b) c →
      ∃ c₁ c₂, c = c₁ ++ c₂ ∧ CResultType.Sub a c₁ ∧ CResultType.Sub b c₂
  | [], b, c, h => ⟨[], c, rfl, List.Forall₂.nil, h⟩
  | x :: a, b, c, h => by
      rw [List.cons_append] at h
      obtain ⟨y, c', hxy, hrest, rfl⟩ := List.forall₂_cons_left_iff.mp h
      obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := CResultType.sub_append_left_inv hrest
      exact ⟨y :: c₁, c₂, rfl, List.Forall₂.cons hxy h₁, h₂⟩

/-- The general canonical-forms statement for a sequence of self-describing
constant instructions. Framing may have replaced the incoming stack `t_1*` by
any supertype `t_1'*` — `Instrs_ok/sub` (`6-typing:168`) can raise a `BOT` in
the frame to anything — but the *suffix* the sequence contributes is exactly the
lift of the types its immediates name: a value instruction has no subsumption
freedom, because `CResultType.sub_liftResult_iff` says a lifted result type is a
subtype only of itself. -/
theorem InstrsOk.values_inv {C : Context} {is : List Instr} {vts : List ValType}
    {t₁ t₂ : CResultType}
    (hv : List.Forall₂ (fun i t => Instr.valueType? i = some t) is vts)
    (h : InstrsOk C is ⟨t₁, t₂⟩) :
    ∃ t₁', CResultType.Sub t₁ t₁' ∧ t₂ = t₁' ++ liftResult vts := by
  induction hv generalizing t₁ t₂ with
  | nil => exact ⟨t₂, InstrsOk.nil_inv h, by simp⟩
  | @cons i t is' vts' hi _ ih =>
      obtain ⟨m, u, hu, hw, hrest⟩ := InstrsOk.cons_inv h
      obtain rfl := InstrOk.valueType?_eq hi hu
      obtain ⟨ws, hp, hr⟩ := hw
      obtain ⟨m', hm, rfl⟩ := ih hrest
      obtain ⟨c₁, c₂, rfl, hc₁, hc₂⟩ :=
        CResultType.sub_append_left_inv (CResultType.sub_trans hr hm)
      obtain rfl : c₂ = liftResult [t] := CResultType.sub_liftResult_iff.mp hc₂
      refine ⟨c₁, CResultType.sub_trans (by simpa using hp) hc₁, ?_⟩
      simp

/-- Canonical forms for a sequence of self-describing constant instructions: its
type from the empty stack is exactly the lift of the types its immediates name,
with no room for subsumption or framing. This is the shape the soundness proof
uses to read a result stack off a sequence of values. -/
theorem InstrsOk.values_iff {C : Context} {is : List Instr} {vts : List ValType}
    {ts : CResultType} (hv : List.Forall₂ (fun i t => Instr.valueType? i = some t) is vts) :
    InstrsOk C is ⟨[], ts⟩ ↔ ts = liftResult vts := by
  constructor
  · intro h
    obtain ⟨t₁', hsub, rfl⟩ := InstrsOk.values_inv hv h
    cases hsub
    simp
  · rintro rfl
    induction hv with
    | nil => exact InstrsOk.empty
    | cons hi _ ih =>
      refine InstrsOk.cons (InstrOk.of_valueType? hi) ?_
      simpa using InstrsOk.frame (ts := [CValType.val _]) ih

/-! ## Memory-access widths

The alignment premises of `6-typing:468-532` are `$(2^(memarg.ALIGN) <= N/8)`
for the *accessed* width `N`: the packed width `M` of `Instr_ok/load-pack`
(`6-typing:473`) when the access packs, the full width `$size(nt)` of
`Instr_ok/load-val` (`6-typing:468`) when it does not. `intLoadWidth` and
`intStoreWidth` are that `N`, and `IntLoadNarrows`/`IntStoreNarrows` are the
syntactic side conditions `sz < $sizenn(Inn)` of `1-syntax:388` and
`1-syntax:509`. They are named rather than written inline so that the
statements of the `InstrOk` and `InstrsOk` forms are literally the same
proposition. -/

/-- The width an integer load accesses: `M` when packed, `$size(nt)` when
not. -/
def intLoadWidth (t : IntType) : Option (PackSize × Signedness) → Nat
  | none => t.width
  | some (sz, _) => sz.width

/-- The width an integer store accesses. -/
def intStoreWidth (t : IntType) : Option PackSize → Nat
  | none => t.width
  | some sz => sz.width

/-- `sz < $sizenn(Inn)` (`1-syntax:388`): a packed load must really narrow. -/
def IntLoadNarrows (t : IntType) : Option (PackSize × Signedness) → Prop
  | none => True
  | some (sz, _) => sz.width < t.width

/-- `sz < $sizenn(Inn)` (`1-syntax:509`): a packed store must really narrow. -/
def IntStoreNarrows (t : IntType) : Option PackSize → Prop
  | none => True
  | some sz => sz.width < t.width

/-! ## Per-instruction inversion

`InstrOk` is syntax directed, so each of these is a `cases` on the single rule
that can conclude with the given instruction form. The premises recovered are
exactly the ones the reduction rules of `8-reduction` need in order to step. -/

namespace InstrOk

variable {C : Context} {it : InstrType}

/-- `Instr_ok/local.get` (`6-typing:371`). -/
theorem localGet_inv {x : LocalIdx} (h : InstrOk C (.localGet x) it) :
    ∃ t, C.locals[x.toNat]? = some t ∧ it = ⟨[], [.val t]⟩ := by
  cases h; exact ⟨_, by assumption, rfl⟩

/-- `Instr_ok/local.set` (`6-typing:375`). -/
theorem localSet_inv {x : LocalIdx} (h : InstrOk C (.localSet x) it) :
    ∃ t, C.locals[x.toNat]? = some t ∧ it = ⟨[.val t], []⟩ := by
  cases h; exact ⟨_, by assumption, rfl⟩

/-- `Instr_ok/local.tee` (`6-typing:379`). -/
theorem localTee_inv {x : LocalIdx} (h : InstrOk C (.localTee x) it) :
    ∃ t, C.locals[x.toNat]? = some t ∧ it = ⟨[.val t], [.val t]⟩ := by
  cases h; exact ⟨_, by assumption, rfl⟩

/-- `Instr_ok/global.get` (`6-typing:386`): either mutability is accepted. -/
theorem globalGet_inv {x : GlobalIdx} (h : InstrOk C (.globalGet x) it) :
    ∃ gt, C.globals[x.toNat]? = some gt ∧ it = ⟨[], [.val gt.value]⟩ := by
  cases h; exact ⟨_, by assumption, rfl⟩

/-- `Instr_ok/global.set` (`6-typing:390`): the global must exist **and be
mutable**. This is the premise `Step/global.set` needs in order to write. -/
theorem globalSet_inv {x : GlobalIdx} (h : InstrOk C (.globalSet x) it) :
    ∃ gt, C.globals[x.toNat]? = some gt ∧ gt.mutability = .var ∧
      it = ⟨[.val gt.value], []⟩ := by
  cases h with
  | globalSet hx hmut => exact ⟨_, hx, hmut, rfl⟩

/-- `Instr_ok/call` (`6-typing:248`). -/
theorem call_inv {x : FuncIdx} (h : InstrOk C (.call x) it) :
    ∃ ft, C.funcs[x.toNat]? = some ft ∧ it = InstrType.lift ft.params ft.results := by
  cases h; exact ⟨_, by assumption, rfl⟩

/-- `Instr_ok/call_indirect` (`6-typing:252`): the table exists, its element
type is **exactly** `FUNCREF` (2.0 has no reference subtyping), and the type
index resolves. -/
theorem callIndirect_inv {x : TableIdx} {y : TypeIdx} (h : InstrOk C (.callIndirect x y) it) :
    ∃ tt ft, C.tables[x.toNat]? = some tt ∧ tt.element = .funcref ∧
      C.types[y.toNat]? = some ft ∧
      it = ⟨liftResult ft.params ++ [.val .i32], liftResult ft.results⟩ := by
  cases h with
  | callIndirect hx hrt hy => exact ⟨_, _, hx, hrt, hy, rfl⟩

/-- `Instr_ok/ref.func` (`6-typing:294`) together with the `C.REFS` premise of
decided deviation 6. -/
theorem refFunc_inv {x : FuncIdx} (h : InstrOk C (.refFunc x) it) :
    (∃ ft, C.funcs[x.toNat]? = some ft) ∧ x ∈ C.refs ∧ it = ⟨[], [.val .funcref]⟩ := by
  cases h with
  | refFunc hx hrefs => exact ⟨⟨_, hx⟩, hrefs, rfl⟩

/-- `Instr_ok/br` (`6-typing:232`). -/
theorem br_inv {l : LabelIdx} (h : InstrOk C (.br l) it) :
    ∃ ts, C.labels[l.toNat]? = some ts ∧ ∃ t₁ t₂, it = ⟨t₁ ++ ts, t₂⟩ := by
  cases h with
  | br hl => exact ⟨_, hl, _, _, rfl⟩

/-- `Instr_ok/br_if` (`6-typing:236`). -/
theorem brIf_inv {l : LabelIdx} (h : InstrOk C (.brIf l) it) :
    ∃ ts, C.labels[l.toNat]? = some ts ∧ it = ⟨ts ++ [.val .i32], ts⟩ := by
  cases h with
  | brIf hl => exact ⟨_, hl, rfl⟩

/-- `Instr_ok/br_table` (`6-typing:240`): every label of the table, and the
default, has a result type above the common `t*`. -/
theorem brTable_inv {ls : List LabelIdx} {l' : LabelIdx} (h : InstrOk C (.brTable ls l') it) :
    ∃ ts, (∀ l ∈ ls, ∃ lt, C.labels[l.toNat]? = some lt ∧ CResultType.Sub ts lt) ∧
      (∃ lt, C.labels[l'.toNat]? = some lt ∧ CResultType.Sub ts lt) ∧
      ∃ t₁ t₂, it = ⟨t₁ ++ ts ++ [.val .i32], t₂⟩ := by
  cases h with
  | brTable hls hl' => exact ⟨_, hls, hl', _, _, rfl⟩

/-- `Instr_ok/return` (`6-typing:257`). -/
theorem return_inv (h : InstrOk C .return_ it) :
    ∃ ts, C.return_ = some ts ∧ ∃ t₁ t₂, it = ⟨t₁ ++ ts, t₂⟩ := by
  cases h with
  | return_ hr => exact ⟨_, hr, _, _, rfl⟩

/-! ### Table instructions -/

/-- `Instr_ok/table.get` (`6-typing:397`). -/
theorem tableGet_inv {x : TableIdx} (h : InstrOk C (.tableGet x) it) :
    ∃ tt, C.tables[x.toNat]? = some tt ∧ it = ⟨[.val .i32], [.val (.ref tt.element)]⟩ := by
  cases h; exact ⟨_, by assumption, rfl⟩

/-- `Instr_ok/table.set` (`6-typing:401`). -/
theorem tableSet_inv {x : TableIdx} (h : InstrOk C (.tableSet x) it) :
    ∃ tt, C.tables[x.toNat]? = some tt ∧
      it = ⟨[.val .i32, .val (.ref tt.element)], []⟩ := by
  cases h; exact ⟨_, by assumption, rfl⟩

/-- `Instr_ok/table.size` (`6-typing:405`). -/
theorem tableSize_inv {x : TableIdx} (h : InstrOk C (.tableSize x) it) :
    (∃ tt, C.tables[x.toNat]? = some tt) ∧ it = ⟨[], [.val .i32]⟩ := by
  cases h; exact ⟨⟨_, by assumption⟩, rfl⟩

/-- `Instr_ok/table.grow` (`6-typing:409`). -/
theorem tableGrow_inv {x : TableIdx} (h : InstrOk C (.tableGrow x) it) :
    ∃ tt, C.tables[x.toNat]? = some tt ∧
      it = ⟨[.val (.ref tt.element), .val .i32], [.val .i32]⟩ := by
  cases h; exact ⟨_, by assumption, rfl⟩

/-- `Instr_ok/table.fill` (`6-typing:413`). -/
theorem tableFill_inv {x : TableIdx} (h : InstrOk C (.tableFill x) it) :
    ∃ tt, C.tables[x.toNat]? = some tt ∧
      it = ⟨[.val .i32, .val (.ref tt.element), .val .i32], []⟩ := by
  cases h; exact ⟨_, by assumption, rfl⟩

/-- `Instr_ok/table.copy` (`6-typing:417`): both tables exist and their element
types **agree**, which is what makes the element written into the destination
well typed. -/
theorem tableCopy_inv {x₁ x₂ : TableIdx} (h : InstrOk C (.tableCopy x₁ x₂) it) :
    ∃ tt₁ tt₂, C.tables[x₁.toNat]? = some tt₁ ∧ C.tables[x₂.toNat]? = some tt₂ ∧
      tt₁.element = tt₂.element ∧ it = ⟨[.val .i32, .val .i32, .val .i32], []⟩ := by
  cases h with
  | tableCopy hx₁ hx₂ hrt => exact ⟨_, _, hx₁, hx₂, hrt, rfl⟩

/-- `Instr_ok/table.init` (`6-typing:422`): the table's element type is the
segment's. -/
theorem tableInit_inv {x₁ : TableIdx} {x₂ : ElemIdx} (h : InstrOk C (.tableInit x₁ x₂) it) :
    ∃ tt rt, C.tables[x₁.toNat]? = some tt ∧ C.elems[x₂.toNat]? = some rt ∧
      tt.element = rt ∧ it = ⟨[.val .i32, .val .i32, .val .i32], []⟩ := by
  cases h with
  | tableInit hx₁ hx₂ hrt => exact ⟨_, _, hx₁, hx₂, hrt, rfl⟩

/-- `Instr_ok/elem.drop` (`6-typing:427`). -/
theorem elemDrop_inv {x : ElemIdx} (h : InstrOk C (.elemDrop x) it) :
    (∃ rt, C.elems[x.toNat]? = some rt) ∧ it = ⟨[], []⟩ := by
  cases h; exact ⟨⟨_, by assumption⟩, rfl⟩

/-! ### Memory instructions

Every rule of `6-typing:434-532` has the premise `C.MEMS[0] = mt`: 2.0 has no
memory index immediate, so a well-typed memory instruction always witnesses that
the module has a memory. -/

/-- `Instr_ok/memory.size` (`6-typing:434`). -/
theorem memorySize_inv (h : InstrOk C .memorySize it) :
    (∃ mt, C.mems[0]? = some mt) ∧ it = ⟨[], [.val .i32]⟩ := by
  cases h; exact ⟨⟨_, by assumption⟩, rfl⟩

/-- `Instr_ok/memory.grow` (`6-typing:438`). -/
theorem memoryGrow_inv (h : InstrOk C .memoryGrow it) :
    (∃ mt, C.mems[0]? = some mt) ∧ it = ⟨[.val .i32], [.val .i32]⟩ := by
  cases h; exact ⟨⟨_, by assumption⟩, rfl⟩

/-- `Instr_ok/memory.fill` (`6-typing:442`). -/
theorem memoryFill_inv (h : InstrOk C .memoryFill it) :
    (∃ mt, C.mems[0]? = some mt) ∧ it = ⟨[.val .i32, .val .i32, .val .i32], []⟩ := by
  cases h; exact ⟨⟨_, by assumption⟩, rfl⟩

/-- `Instr_ok/memory.copy` (`6-typing:446`). -/
theorem memoryCopy_inv (h : InstrOk C .memoryCopy it) :
    (∃ mt, C.mems[0]? = some mt) ∧ it = ⟨[.val .i32, .val .i32, .val .i32], []⟩ := by
  cases h; exact ⟨⟨_, by assumption⟩, rfl⟩

/-- `Instr_ok/memory.init` (`6-typing:450`): the memory exists and the data
segment index is in range. -/
theorem memoryInit_inv {x : DataIdx} (h : InstrOk C (.memoryInit x) it) :
    (∃ mt, C.mems[0]? = some mt) ∧ C.datas[x.toNat]? = some () ∧
      it = ⟨[.val .i32, .val .i32, .val .i32], []⟩ := by
  cases h with
  | memoryInit hm hx => exact ⟨⟨_, hm⟩, hx, rfl⟩

/-- `Instr_ok/data.drop` (`6-typing:455`). -/
theorem dataDrop_inv {x : DataIdx} (h : InstrOk C (.dataDrop x) it) :
    C.datas[x.toNat]? = some () ∧ it = ⟨[], []⟩ := by
  cases h with
  | dataDrop hx => exact ⟨hx, rfl⟩

/-! ### Loads and stores

The alignment premises of `6-typing:468-532` bound `2^(memarg.ALIGN)` by `N/8`
for the accessed width `N`, which is `intLoadWidth`/`intStoreWidth` above. -/

/-- `Instr_ok/load-val` (`6-typing:468`) and `/load-pack` (`6-typing:473`). -/
theorem intLoad_inv {t : IntType} {p : Option (PackSize × Signedness)} {arg : MemArg}
    (h : InstrOk C (.intLoad t p arg) it) :
    (∃ mt, C.mems[0]? = some mt) ∧
      MemArgOk arg (intLoadWidth t p) ∧ IntLoadNarrows t p ∧
      it = ⟨[.val .i32], [.val (.num (.int t))]⟩ := by
  cases h with
  | intLoadVal hm ha => exact ⟨⟨_, hm⟩, ha, trivial, rfl⟩
  | intLoadPack hm hsz ha => exact ⟨⟨_, hm⟩, ha, hsz, rfl⟩

/-- `Instr_ok/load-val` (`6-typing:468`), floating-point case: a float load
never packs. -/
theorem floatLoad_inv {t : FloatType} {arg : MemArg} (h : InstrOk C (.floatLoad t arg) it) :
    (∃ mt, C.mems[0]? = some mt) ∧ MemArgOk arg t.width ∧
      it = ⟨[.val .i32], [.val (.num (.float t))]⟩ := by
  cases h with
  | floatLoadVal hm ha => exact ⟨⟨_, hm⟩, ha, rfl⟩

/-- `Instr_ok/store-val` (`6-typing:487`) and `/store-pack` (`6-typing:492`). -/
theorem intStore_inv {t : IntType} {p : Option PackSize} {arg : MemArg}
    (h : InstrOk C (.intStore t p arg) it) :
    (∃ mt, C.mems[0]? = some mt) ∧
      MemArgOk arg (intStoreWidth t p) ∧ IntStoreNarrows t p ∧
      it = ⟨[.val .i32, .val (.num (.int t))], []⟩ := by
  cases h with
  | intStoreVal hm ha => exact ⟨⟨_, hm⟩, ha, trivial, rfl⟩
  | intStorePack hm hsz ha => exact ⟨⟨_, hm⟩, ha, hsz, rfl⟩

/-- `Instr_ok/store-val` (`6-typing:487`), floating-point case. -/
theorem floatStore_inv {t : FloatType} {arg : MemArg} (h : InstrOk C (.floatStore t arg) it) :
    (∃ mt, C.mems[0]? = some mt) ∧ MemArgOk arg t.width ∧
      it = ⟨[.val .i32, .val (.num (.float t))], []⟩ := by
  cases h with
  | floatStoreVal hm ha => exact ⟨⟨_, hm⟩, ha, rfl⟩

/-- The alignment bound `$(2^(memarg.ALIGN) <= M/8 * N)` of `Instr_ok/vload-pack`
(`6-typing:502`) is the generic bound at the accessed width: `M/8 * N` is `8`
for each of `SHAPE 8 X 8`, `SHAPE 16 X 4` and `SHAPE 32 X 2`, and so is
`64/8`. -/
theorem _root_.Silmaril.Wasm.V2.Validation.MemArgOk.of_packShape {arg : MemArg}
    {o : VecLoadOp} {m n : Nat} (hop : VecLoadOp.packShape o = some (m, n))
    (ha : MemArgOkPack arg m n) : MemArgOk arg (VecLoadOp.accessWidth (some o)) := by
  cases o <;>
    simp only [VecLoadOp.packShape, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hop <;>
    obtain ⟨rfl, rfl⟩ := hop <;>
    simpa [VecLoadOp.accessWidth, MemArgOk, MemArgOkPack] using ha

/-- The alignment bound of `Instr_ok/vload-zero` (`6-typing:512`) at the
accessed width. -/
theorem _root_.Silmaril.Wasm.V2.Validation.MemArgOk.of_zeroWidth {arg : MemArg}
    {o : VecLoadOp} {n : Nat} (hop : VecLoadOp.zeroWidth o = some n)
    (ha : MemArgOk arg n) : MemArgOk arg (VecLoadOp.accessWidth (some o)) := by
  cases o <;>
    simp only [VecLoadOp.zeroWidth, Option.some.injEq, reduceCtorEq] at hop <;>
    subst hop <;> simpa [VecLoadOp.accessWidth] using ha

/-- `Instr_ok/vload-val`, `/vload-pack`, `/vload-splat`, `/vload-zero`
(`6-typing:497-515`). The four rules bound the alignment by four different
expressions, all of which equal `VecLoadOp.accessWidth / 8`; in particular
`M/8 * N` of `/vload-pack` is `8` for each of the three packed shapes, which is
`64/8`. -/
theorem vecLoad_inv {op : Option VecLoadOp} {arg : MemArg}
    (h : InstrOk C (.vecLoad op arg) it) :
    (∃ mt, C.mems[0]? = some mt) ∧ MemArgOk arg (VecLoadOp.accessWidth op) ∧
      it = ⟨[.val .i32], [.val .v128]⟩ := by
  cases h with
  | vloadVal hm ha => exact ⟨⟨_, hm⟩, ha, rfl⟩
  | vloadPack hm hop ha => exact ⟨⟨_, hm⟩, MemArgOk.of_packShape hop ha, rfl⟩
  | vloadSplat hm ha => exact ⟨⟨_, hm⟩, ha, rfl⟩
  | vloadZero hm hop ha => exact ⟨⟨_, hm⟩, MemArgOk.of_zeroWidth hop ha, rfl⟩

/-- `Instr_ok/vload_lane` (`6-typing:517`). -/
theorem vecLoadLane_inv {sz : PackSize} {arg : MemArg} {i : LaneIdx}
    (h : InstrOk C (.vecLoadLane sz arg i) it) :
    (∃ mt, C.mems[0]? = some mt) ∧ MemArgOk arg sz.width ∧ i.val < 128 / sz.width ∧
      it = ⟨[.val .i32, .val .v128], [.val .v128]⟩ := by
  cases h with
  | vloadLane hm ha hi => exact ⟨⟨_, hm⟩, ha, hi, rfl⟩

/-- `Instr_ok/vstore` (`6-typing:523`). -/
theorem vecStore_inv {arg : MemArg} (h : InstrOk C (.vecStore arg) it) :
    (∃ mt, C.mems[0]? = some mt) ∧ MemArgOk arg 128 ∧
      it = ⟨[.val .i32, .val .v128], []⟩ := by
  cases h with
  | vstore hm ha => exact ⟨⟨_, hm⟩, ha, rfl⟩

/-- `Instr_ok/vstore_lane` (`6-typing:528`). -/
theorem vecStoreLane_inv {sz : PackSize} {arg : MemArg} {i : LaneIdx}
    (h : InstrOk C (.vecStoreLane sz arg i) it) :
    (∃ mt, C.mems[0]? = some mt) ∧ MemArgOk arg sz.width ∧ i.val < 128 / sz.width ∧
      it = ⟨[.val .i32, .val .v128], []⟩ := by
  cases h with
  | vstoreLane hm ha hi => exact ⟨⟨_, hm⟩, ha, hi, rfl⟩

end InstrOk

/-! ## The same premises from a one-instruction sequence

These are the forms the soundness proof actually applies, since it meets
instructions inside an `InstrsOk` derivation. Each is `InstrsOk.singleton_elim`
composed with the corresponding `InstrOk` lemma; the recovered premises mention
only the context and the immediates, so the framing and subsumption that
`singleton_inv` absorbs cannot disturb them. -/

namespace InstrsOk

variable {C : Context} {it : InstrType}

/-- A global written by a well-typed `global.set` exists and is mutable. -/
theorem globalSet_mut {x : GlobalIdx} (h : InstrsOk C [.globalSet x] it) :
    ∃ gt, C.globals[x.toNat]? = some gt ∧ gt.mutability = .var := by
  refine h.singleton_elim fun _ h' => ?_
  obtain ⟨gt, hx, hmut, -⟩ := h'.globalSet_inv
  exact ⟨gt, hx, hmut⟩

/-- The table of a well-typed `call_indirect` exists and holds `FUNCREF`. -/
theorem callIndirect_funcref {x : TableIdx} {y : TypeIdx}
    (h : InstrsOk C [.callIndirect x y] it) :
    ∃ tt, C.tables[x.toNat]? = some tt ∧ tt.element = .funcref := by
  refine h.singleton_elim fun _ h' => ?_
  obtain ⟨tt, -, hx, hrt, -, -⟩ := h'.callIndirect_inv
  exact ⟨tt, hx, hrt⟩

/-- The two tables of a well-typed `table.copy` agree on their element type. -/
theorem tableCopy_elements {x₁ x₂ : TableIdx} (h : InstrsOk C [.tableCopy x₁ x₂] it) :
    ∃ tt₁ tt₂, C.tables[x₁.toNat]? = some tt₁ ∧ C.tables[x₂.toNat]? = some tt₂ ∧
      tt₁.element = tt₂.element := by
  refine h.singleton_elim fun _ h' => ?_
  obtain ⟨tt₁, tt₂, hx₁, hx₂, hrt, -⟩ := h'.tableCopy_inv
  exact ⟨tt₁, tt₂, hx₁, hx₂, hrt⟩

/-- The table and the segment of a well-typed `table.init` agree. -/
theorem tableInit_elements {x₁ : TableIdx} {x₂ : ElemIdx}
    (h : InstrsOk C [.tableInit x₁ x₂] it) :
    ∃ tt rt, C.tables[x₁.toNat]? = some tt ∧ C.elems[x₂.toNat]? = some rt ∧
      tt.element = rt := by
  refine h.singleton_elim fun _ h' => ?_
  obtain ⟨tt, rt, hx₁, hx₂, hrt, -⟩ := h'.tableInit_inv
  exact ⟨tt, rt, hx₁, hx₂, hrt⟩

/-- A well-typed `ref.func` names a declared function. -/
theorem refFunc_declared {x : FuncIdx} (h : InstrsOk C [.refFunc x] it) :
    (∃ ft, C.funcs[x.toNat]? = some ft) ∧ x ∈ C.refs := by
  refine h.singleton_elim fun _ h' => ?_
  obtain ⟨hf, hr, -⟩ := h'.refFunc_inv
  exact ⟨hf, hr⟩

/-- Every memory instruction witnesses `C.MEMS[0]`. -/
theorem memoryInit_mem {x : DataIdx} (h : InstrsOk C [.memoryInit x] it) :
    (∃ mt, C.mems[0]? = some mt) ∧ C.datas[x.toNat]? = some () := by
  refine h.singleton_elim fun _ h' => ?_
  obtain ⟨hm, hx, -⟩ := h'.memoryInit_inv
  exact ⟨hm, hx⟩

/-- A well-typed integer load has a memory and a legal alignment. -/
theorem intLoad_access {t : IntType} {p : Option (PackSize × Signedness)} {arg : MemArg}
    (h : InstrsOk C [.intLoad t p arg] it) :
    (∃ mt, C.mems[0]? = some mt) ∧
      MemArgOk arg (intLoadWidth t p) := by
  refine h.singleton_elim fun _ h' => ?_
  obtain ⟨hm, ha, -, -⟩ := h'.intLoad_inv
  exact ⟨hm, ha⟩

/-- A well-typed integer store has a memory and a legal alignment. -/
theorem intStore_access {t : IntType} {p : Option PackSize} {arg : MemArg}
    (h : InstrsOk C [.intStore t p arg] it) :
    (∃ mt, C.mems[0]? = some mt) ∧
      MemArgOk arg (intStoreWidth t p) := by
  refine h.singleton_elim fun _ h' => ?_
  obtain ⟨hm, ha, -, -⟩ := h'.intStore_inv
  exact ⟨hm, ha⟩

/-- A well-typed vector load has a memory and a legal alignment. -/
theorem vecLoad_access {op : Option VecLoadOp} {arg : MemArg}
    (h : InstrsOk C [.vecLoad op arg] it) :
    (∃ mt, C.mems[0]? = some mt) ∧ MemArgOk arg (VecLoadOp.accessWidth op) := by
  refine h.singleton_elim fun _ h' => ?_
  obtain ⟨hm, ha, -⟩ := h'.vecLoad_inv
  exact ⟨hm, ha⟩

end InstrsOk

/-! ## Syntactic side conditions

`InstrOk.immediatesValid` and `InstrsOk.immediatesValid` are proved in
`Silmaril/Wasm/V2/Validation/Instructions.lean`; this is their `Expr_ok`
corollary (`6-typing:149`). -/

/-- Every instruction of a well-typed expression satisfies the side conditions
of its syntax production. -/
theorem ExprOk.immediatesValid {C : Context} {e : Expr} {ts : CResultType}
    (h : ExprOk C e ts) : e.all Instr.immediatesValid = true :=
  InstrsOk.immediatesValid h

end Silmaril.Wasm.V2.Validation
