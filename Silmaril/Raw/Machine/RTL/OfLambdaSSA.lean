module

public import Silmaril.Raw.Machine.RTL.ToLambdaSSA

/-!
# A lambda-SSA region as an SSA-form RTL function

Flattening is the converse of nesting: the `cfg` binders disappear, every block
of every `cfg` becomes one entry of a single block list, de Bruijn labels become
absolute block indices, `let₁` and `let₂` become straight-line ops, and `case`
becomes a conditional terminator. Fresh registers and fresh block labels come
from counters.

## What the sketch `ofLambdaSSA (r : Region) (h : r.Scoped labels n) : Func Nat`
## cannot do

* **Scope is not enough; the fragment matters.** A general lambda-SSA region over
  `Opcode sigs` may bind a value of any type — a coproduct, a nested product, the
  result of `inl` — and an RTL register holds a 64-bit word and nothing else. Only
  the *RTL fragment* translates: every bound value is a packed tuple of words,
  every label carries a packed tuple, and every `case` eliminates the `unit + unit`
  that the branch opcode produces. Rather than carve the fragment out with a
  second typing judgment, the compiler is partial — `ofLambdaSSA?` — and
  `Compiles` is the decidable statement that it succeeded. A region compiles
  exactly when it is in the fragment, which is the cleanest way to say it.
* **A `cfg`'s block arities are not determined by its syntax.**
  `Region.HasType.cfg` chooses the family `R` of block parameter types
  existentially, and the syntax of a `cfg` records only how many blocks it has.
  A block that is never branched to has no syntactic trace of its parameter's
  width at all. The arities are therefore supplied as data, by an annotation tree
  `Ann` running alongside the region. For a region in the image of `toLambdaSSA`
  the annotation is determined — that is part of `Canonical` — so the headline
  bijection is unaffected.

## The shape of the output

Block `0` is the entry block, whose parameters are the function's. Every other
block comes from a `cfg` block or from one side of a `case`. A `case` branch
takes no parameters: it is dominated by the block that branches to it, so it may
read that block's registers directly, which is precisely what `UsesDominated`
allows.

## What the compiler undoes rather than flattens

Two shapes that `Machine/RTL/ToLambdaSSA.lean` introduces are artefacts of the
nesting rather than structure of the function, and flattening them literally
would make the round trip add blocks without bound. Both are recognised here.

* **The wrapper `cfg`.** `toLambdaSSA` wraps every function in one outermost
  `cfg (br 0 (var 0)) 1 …`, so that a back edge to the entry block has a label
  like any other transfer. Compiled by the general `cfg` case, that wrapper's
  entry region `br 0 (var 0)` becomes a real forwarding block. `rootOps` matches
  the wrapper at the root and compiles its body directly as the entry block,
  under the function's own parameter registers, so no forwarding block appears.
  The body sees only the block's argument: the function's argument below it
  shares those registers, which a back edge to block zero overwrites, so a body
  that reads it is refused (`aliasRegion_not_compiles`) rather than miscompiled.
  `toLambdaSSA` never emits such a body. A root `cfg` of any other shape, and
  every nested `cfg`, still goes through `regionOps`.
* **The two-way `case`.** `Term.toRegion` sends a conditional to
  `case (op test c) (br …) (br …)`, and the general `case` case compiles a
  `case` into a three-block diamond. `condOf` matches the two-branch shape and
  emits `Term.cond` directly. The diamond remains the fallback, because a `case`
  of the fragment need not be a conditional branch: an arm may be a `let₁`
  chain, may branch out of the function to the return or the trap label, or may
  carry an argument whose computation needs an op emitted, and a terminator
  accommodates none of those.

## Two corrections to the compiler, and why

* **An opcode's operands are checked against its arity.** `opOf` already matched
  every opcode against exactly the operand and destination registers its arity
  provides — every opcode but `call`, whose arity is not a literal but
  `(sigAt sigs f).params`. Without that check `Compiles` did not imply
  `Func.CallsMatch`: a region could apply a binary callee to no operands at all
  and still compile. The `call` arm of `opOf` now carries the check the other
  arms get from their patterns, so `ofLambdaSSA_callsMatch` is true as stated and
  `Compiles` still characterises the fragment, since an opcode applied to the
  wrong number of operands is not in it.
* **Allocation order follows the nesting.** A `cfg` block's parameter registers
  are allocated when that block is compiled rather than all at the `cfg` node,
  and a `case`'s false branch takes the label allocated after its body rather
  than one allocated alongside the true branch's. Neither changes which function
  is produced up to the numbering of registers and labels; both make every stage
  of the compilation spend a *contiguous interval* of fresh names, which is the
  invariant `Grew` records and the one every freshness result rests on. The one
  exception is a `cfg`'s block labels, which must be allocated before its entry
  region is compiled because that region may branch to them; they are handled
  separately, by `foldl_grew_cfg`.

## What is proved here

`ofLambdaSSA_sig`, `ofLambdaSSA_callsMatch`, and three of the four conjuncts of
`Func.WellFormed`: `ofLambdaSSA_wellFormedSig`, `ofLambdaSSA_singleAssignment`
and `ofLambdaSSA_argsMatch`. `Func.UsesDominated` is *not* proved; it is a
hypothesis of `ofLambdaSSA_wellFormed_of_usesDominated`, whose docstring says
plainly why. Semantics preservation is proved only for the region that branches
immediately to the trap label — `ofLambdaSSA_eval_iff_trap` and
`ofLambdaSSA_diverges_iff_trap` — and those docstrings likewise say what the
general statement would need.
-/

@[expose] public section

namespace Silmaril.Machine.RTL.SSA

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

/-! ## Annotations -/

/-- The block-parameter widths that a region's syntax does not determine, as a
plain tree running alongside the region. Only `cfg` carries data; the other
constructors are present so that the tree and the region can be matched. -/
inductive Ann where
  | br
  | case (left right : Ann)
  | let₁ (body : Ann)
  | let₂ (body : Ann)
  | cfg (widths : List Nat) (entry : Ann) (blocks : List Ann)

/-! ## The compiler's state -/

/-- Where a lambda-SSA label goes once the `cfg`s are flattened: to a block of
the function, or out of the function by returning or trapping. -/
inductive Target where
  | block (label : Label)
  | ret
  | trap
  deriving DecidableEq, Repr

/-- The compiler's state: the next unused register, the next unused block label,
and the blocks emitted so far with the labels they were given. -/
structure Emit where
  nextReg : Nat
  nextLabel : Nat
  blocks : List (Nat × Block Nat)

/-- `n` fresh registers starting at `first`. -/
def freshRegs (first n : Nat) : List Nat := (List.range n).map (fun i => first + i)

/-! ## Opcodes back to ops -/

/-- The RTL op an opcode performs on the given argument and destination
registers, when their numbers match the opcode's arity. -/
def opOf {sigs : List Signature} : Opcode sigs → List Nat → List Nat → Option (Op Nat)
  | .const v, [], [d] => some (.const d v)
  | .move, [s], [d] => some (.move d s)
  | .unary o, [s], [d] => some (.unary o d s)
  | .binary o, [a, b], [d] => some (.binary o d a b)
  | .load w e off, [b], [d] => some (.load w e d b off)
  | .store w off, [b, s], [] => some (.store w b off s)
  | .call c, as, ds => if as.length = (sigAt sigs c).params then some (.call c as ds) else none
  | _, _, _ => none

/-- An op built by `opOf` defines exactly the destinations it was given. -/
theorem opOf_defs {sigs : List Signature} {f : Opcode sigs} {as ds : List Nat} {o : Op Nat}
    (h : opOf f as ds = some o) : o.defs = ds := by
  unfold opOf at h
  split at h <;>
    first
      | (simp only [Option.some.injEq] at h; subst h; simp [Op.defs])
      | (split at h
         · simp only [Option.some.injEq] at h; subst h; simp [Op.defs]
         · simp at h)
      | simp at h

/-- An op built by `opOf` reads exactly the arguments it was given. -/
theorem opOf_uses {sigs : List Signature} {f : Opcode sigs} {as ds : List Nat} {o : Op Nat}
    (h : opOf f as ds = some o) : o.uses = as := by
  unfold opOf at h
  split at h <;>
    first
      | (simp only [Option.some.injEq] at h; subst h; simp [Op.uses])
      | (split at h
         · simp only [Option.some.injEq] at h; subst h; simp [Op.uses]
         · simp at h)
      | simp at h

/-- An op built by `opOf` was given the opcode's arity in arguments. -/
theorem opOf_arity {sigs : List Signature} {f : Opcode sigs} {as ds : List Nat} {o : Op Nat}
    (h : opOf f as ds = some o) : as.length = f.arity := by
  unfold opOf at h
  split at h <;>
    first
      | (simp only [Option.some.injEq] at h; subst h; simp [Opcode.arity])
      | (split at h
         · rename_i hlen; simpa [Opcode.arity] using hlen
         · simp at h)
      | simp at h

/-! ## Expressions -/

/-- Compile a term to the registers holding the components of its value,
emitting the ops its opcodes need. A term outside the RTL fragment — an
injection, an `abort`, a `case`, or the branch opcode outside a terminator —
has no translation and gives `none`. -/
def tmRegs {sigs : List Signature} (env : List (List Nat)) (t : Tm (Opcode sigs))
    (e : Emit) : Option (List Nat × List (Op Nat) × Emit) :=
  match t with
  | .var i => (env[i]?).map fun g => (g, [], e)
  | .unit => some ([], [], e)
  | .pair a b =>
      (tmRegs env a e).bind fun (ra, opa, e₁) =>
        (tmRegs env b e₁).map fun (rb, opb, e₂) => (ra ++ rb, opa ++ opb, e₂)
  | .op f a =>
      match f with
      | .test => none
      | f =>
        (tmRegs env a e).bind fun (ra, opa, e₁) =>
          let ds := freshRegs e₁.nextReg f.results
          (opOf f ra ds).map fun o =>
            (ds, opa ++ [o], { e₁ with nextReg := e₁.nextReg + f.results })
  | .let₁ a b =>
      (tmRegs env a e).bind fun (ra, opa, e₁) =>
        (tmRegs (ra :: env) b e₁).map fun (rb, opb, e₂) => (rb, opa ++ opb, e₂)
  | .let₂ a b =>
      (tmRegs env a e).bind fun (ra, opa, e₁) =>
        match ra with
        | [] => none
        | r :: rest =>
          (tmRegs (rest :: [r] :: env) b e₁).map fun (rb, opb, e₂) => (rb, opa ++ opb, e₂)
  | .inl _ | .inr _ | .case .. | .abort _ => none

/-- The branch opcode has no translation as a term. -/
theorem tmRegs_op_test {sigs : List Signature} (env : List (List Nat))
    (a : Tm (Opcode sigs)) (e : Emit) : tmRegs env (.op .test a) e = none := by
  rw [tmRegs]

/-- Every other opcode compiles its argument and then emits one op writing
freshly allocated destinations. -/
theorem tmRegs_op {sigs : List Signature} {f : Opcode sigs} (hf : f ≠ .test)
    (env : List (List Nat)) (a : Tm (Opcode sigs)) (e : Emit) :
    tmRegs env (.op f a) e =
      (tmRegs env a e).bind fun (ra, opa, e₁) =>
        let ds := freshRegs e₁.nextReg f.results
        (opOf f ra ds).map fun o =>
          (ds, opa ++ [o], { e₁ with nextReg := e₁.nextReg + f.results }) := by
  rw [tmRegs]
  exact fun h => hf h

/-! ## Regions

A `case` on the branch opcode whose two arms are both branches is a conditional
branch, and `Term.cond` says so directly. `condArm` and `condOf` recognise that
shape; `regionOps` keeps the three-block diamond as the fallback, because a
`case` of the fragment need not have it. Either arm may be a `let₁` chain
computing the arguments it passes on, either may branch out of the function to
the return or the trap label, and either may supply arguments that take an op to
compute; `Term.cond` accommodates none of those, since the block it terminates
is closed by the time the arms are reached. -/

/-- One arm of a conditional branch: the block it transfers to and the registers
it carries there, when the arm is a branch to a block of the function whose
argument tuple is already in registers.

The arm is compiled under one more binder than its surroundings, because
`Region.case` binds the `unit` payload of the injection; the tuple bound there is
empty, exactly as in the diamond. `none` whenever the arm is anything else: a
branch out of the function, a branch of the wrong width, a branch whose argument
needs an op emitted for it, or a region that is not a branch at all. -/
def condArm {sigs : List Signature} (r : Region (Opcode sigs)) (a : Ann)
    (env : List (List Nat)) (labels : List (Target × Nat)) (e : Emit) :
    Option (Nat × List Nat × Emit) :=
  match r, a with
  | .br ℓ arg, .br =>
      (labels[ℓ]?).bind fun (tgt, w) =>
        match tgt with
        | .block t =>
            (tmRegs ([] :: env) arg e).bind fun (rs, opsA, e₁) =>
              match opsA with
              | [] => if rs.length = w then some (t, rs, e₁) else none
              | _ => none
        | _ => none
  | _, _ => none

/-- A `case` whose two arms are both conditional-branch arms is a conditional
terminator, carrying the straight-line prefix `ops` that the discriminant left
behind. -/
def condOf {sigs : List Signature} (left right : Region (Opcode sigs)) (al ar : Ann)
    (c : Nat) (ops : List (Op Nat)) (env : List (List Nat)) (labels : List (Target × Nat))
    (e : Emit) : Option (List (Op Nat) × Term Nat × Emit) :=
  (condArm left al env labels e).bind fun (t₁, rs₁, e₁) =>
    (condArm right ar env labels e₁).map fun (t₂, rs₂, e₂) =>
      (ops, Term.cond c t₁ rs₁ t₂ rs₂, e₂)

/-- Compile a region into the straight-line prefix and the terminator of the
block it begins, emitting every block its nested `cfg`s and `case`s need.
`labels` maps each lambda-SSA label to its target and the number of words that
target expects. -/
def regionOps {sigs : List Signature} (r : Region (Opcode sigs)) (a : Ann)
    (env : List (List Nat)) (labels : List (Target × Nat)) (e : Emit) :
    Option (List (Op Nat) × Term Nat × Emit) :=
  match r, a with
  | .br ℓ arg, .br =>
      (labels[ℓ]?).bind fun (tgt, w) =>
        (tmRegs env arg e).bind fun (rs, ops, e₁) =>
          if rs.length = w then
            match tgt with
            | .block t => some (ops, .jump t rs, e₁)
            | .ret => some (ops, .ret rs, e₁)
            | .trap => some (ops, .trap, e₁)
          else none
  | .let₁ v body, .let₁ ab =>
      (tmRegs env v e).bind fun (rv, ops, e₁) =>
        (regionOps body ab (rv :: env) labels e₁).map fun (ops', t, e₂) => (ops ++ ops', t, e₂)
  | .let₂ v body, .let₂ ab =>
      (tmRegs env v e).bind fun (rv, ops, e₁) =>
        match rv with
        | [] => none
        | r :: rest =>
          (regionOps body ab (rest :: [r] :: env) labels e₁).map
            fun (ops', t, e₂) => (ops ++ ops', t, e₂)
  | .case discr left right, .case al ar =>
      match discr with
      | .op .test arg =>
          (tmRegs env arg e).bind fun (rs, ops, e₁) =>
            match rs with
            | [c] =>
              match condOf left right al ar c ops env labels e₁ with
              | some res => some res
              | none =>
                (regionOps left al ([] :: env) labels
                    { e₁ with nextLabel := e₁.nextLabel + 1 }).bind fun (opsL, tL, e₃) =>
                  (regionOps right ar ([] :: env) labels
                      { e₃ with blocks := (e₁.nextLabel, ⟨[], opsL, tL⟩) :: e₃.blocks }).map
                    fun (opsR, tR, e₄) =>
                      (ops, Term.cond c e₁.nextLabel [] e₄.nextLabel [],
                        { e₄ with
                          nextLabel := e₄.nextLabel + 1,
                          blocks := (e₄.nextLabel, ⟨[], opsR, tR⟩) :: e₄.blocks })
            | _ => none
      | _ => none
  | .cfg entry k blocks, .cfg ws ae abs =>
      if ws.length = k then
        let base := e.nextLabel
        let inner : List (Target × Nat) :=
          (List.finRange k).map (fun i => (Target.block (base + i.val), ws.getD i.val 0))
        let labels' := inner ++ labels
        let e₀ : Emit := { e with nextLabel := base + k }
        (regionOps entry ae env labels' e₀).bind fun (ops, t, e₁) =>
          ((List.finRange k).foldl
            (fun acc i => acc.bind fun e' =>
              (regionOps (blocks i) (abs.getD i.val .br)
                  (freshRegs e'.nextReg (ws.getD i.val 0) :: env) labels'
                  { e' with nextReg := e'.nextReg + ws.getD i.val 0 }).map
                fun (opsB, tB, e'') =>
                  { e'' with
                    blocks :=
                      (base + i.val,
                        ⟨freshRegs e'.nextReg (ws.getD i.val 0), opsB, tB⟩) :: e''.blocks })
            (some e₁)).map fun e₂ => (ops, t, e₂)
      else none
  | _, _ => none

/-- Assemble the emitted blocks into a contiguous block list; a label that was
allocated but never filled becomes an unreachable trap. -/
def assemble (count : Nat) (bs : List (Nat × Block Nat)) : List (Block Nat) :=
  (List.range count).map fun l => (bs.lookup l).getD ⟨[], [], .trap⟩

/-- Compile the region at the root of a function into the ops and the
terminator of its entry block.

`toLambdaSSA` wraps every function in one outermost `cfg (br 0 (var 0)) 1 …`, so
that a back edge to the entry block has a label like any other transfer. That
wrapper is an artefact of the nesting and not a block of the function, so it is
recognised here and undone: its body is compiled directly as the entry block,
under the function's own parameter registers and with block zero standing for
the wrapper's single label. The body's environment holds only the block's
argument. The function's argument, one index further out, would share the
parameter registers, and a back edge to block zero overwrites them, so a body
that reads it is refused instead of compiled with the overwritten value. Every
other `cfg` — and a root `cfg` of any other shape — goes through `regionOps`'s
general case, which does make a block of the `cfg`'s entry region. -/
def rootOps (sigs : List Signature) (r : Region (Opcode sigs)) (a : Ann)
    (params results : Nat) : Option (List (Op Nat) × Term Nat × Emit) :=
  match r, a with
  | .cfg (.br 0 (.var 0)) 1 blocks, .cfg [w] .br [ab] =>
      if w = params then
        regionOps (blocks 0) ab [freshRegs 0 params]
          [(.block 0, params), (.ret, results), (.trap, 0)]
          { nextReg := params, nextLabel := 1, blocks := [] }
      else none
  | _, _ =>
      regionOps r a [freshRegs 0 params] [(.ret, results), (.trap, 0)]
        { nextReg := params, nextLabel := 1, blocks := [] }

/-- **A lambda-SSA region as an SSA-form RTL function**, when the region is in
the RTL fragment. `params` and `results` are the function's signature: the entry
block receives `params` registers holding the components of the region's single
argument, and a branch to the return label carries `results` words. -/
def ofLambdaSSA? (sigs : List Signature) (r : Region (Opcode sigs)) (a : Ann)
    (params results : Nat) : Option (Func Nat) :=
  (rootOps sigs r a params results).map
    fun (ops, t, e) =>
      { sig := ⟨params, results⟩, entry := 0,
        blocks := assemble e.nextLabel ((0, ⟨freshRegs 0 params, ops, t⟩) :: e.blocks) }

/-- The region is in the RTL fragment with the given annotation and signature. -/
def Compiles (sigs : List Signature) (r : Region (Opcode sigs)) (a : Ann)
    (params results : Nat) : Prop := (ofLambdaSSA? sigs r a params results).isSome

/-- Membership of the RTL fragment is decidable: run the compiler and look. -/
instance (sigs : List Signature) (r : Region (Opcode sigs)) (a : Ann) (params results : Nat) :
    Decidable (Compiles sigs r a params results) := inferInstanceAs (Decidable (_ = _))

/-- The flattened function, with a trapping one-block function standing in for a
region outside the fragment. -/
def ofLambdaSSA (sigs : List Signature) (r : Region (Opcode sigs)) (a : Ann)
    (params results : Nat) : Func Nat :=
  (ofLambdaSSA? sigs r a params results).getD
    { sig := ⟨params, results⟩, entry := 0, blocks := [⟨freshRegs 0 params, [], .trap⟩] }

/-! ## Fresh registers and emitted blocks -/

/-- Allocating `n` registers produces `n` registers. -/
@[simp] theorem freshRegs_length (first n : Nat) : (freshRegs first n).length = n := by
  simp [freshRegs]

/-- A register is freshly allocated at `first` exactly when it is one of the `n`
registers starting there. -/
theorem mem_freshRegs {first n r : Nat} : r ∈ freshRegs first n ↔ first ≤ r ∧ r < first + n := by
  simp only [freshRegs, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro h
    exact ⟨r - first, by omega, by omega⟩

/-- Freshly allocated registers are distinct. -/
theorem freshRegs_nodup (first n : Nat) : (freshRegs first n).Nodup := by
  refine List.Nodup.map ?_ List.nodup_range
  intro a b h
  have h' : first + a = first + b := h
  omega

/-- The registers a list of labelled blocks defines. -/
def blocksDefs (bs : List (Nat × Block Nat)) : List Nat := bs.flatMap fun p => p.2.defs

/-- No blocks define nothing. -/
@[simp] theorem blocksDefs_nil : blocksDefs [] = [] := rfl

/-- One more block defines what it defines. -/
@[simp] theorem blocksDefs_cons (p : Nat × Block Nat) (bs : List (Nat × Block Nat)) :
    blocksDefs (p :: bs) = p.2.defs ++ blocksDefs bs := rfl

/-- Concatenated blocks define the concatenation of what they define. -/
@[simp] theorem blocksDefs_append (bs bs' : List (Nat × Block Nat)) :
    blocksDefs (bs ++ bs') = blocksDefs bs ++ blocksDefs bs' := by
  simp [blocksDefs]

/-- Disjoint lists concatenate without duplicates. -/
theorem nodup_append_of_disj {A B : List Nat} (hA : A.Nodup) (hB : B.Nodup)
    (h : ∀ r ∈ A, r ∉ B) : (A ++ B).Nodup :=
  List.nodup_append.mpr ⟨hA, hB, fun a ha _b hb hab => h a ha (hab ▸ hb)⟩

/-! ## How the compiler's state grows

Every lemma about the compiler rests on one relation: passing from `e` to `e'`
only ever appends to the block list, only ever increases the two counters, and
spends the registers and labels of the interval it opened on distinct new
definitions. The relation is reflexive and transitive, which is what lets the
`cfg` case's fold be handled by a single lemma. -/

/-- **How the compiler's state grows.** `Grew e ops e'` says that passing from
`e` to `e'` emitted `ops` into the block under construction and finished the
blocks that `e'.blocks` has beyond `e.blocks`: the two counters only grew, each
finished block carries a label allocated in the interval, those labels are
distinct, and every register newly defined — by one of `ops` or by one of those
blocks — is a distinct register allocated in the interval. -/
def Grew (e : Emit) (ops : List (Op Nat)) (e' : Emit) : Prop :=
  e.nextReg ≤ e'.nextReg ∧ e.nextLabel ≤ e'.nextLabel ∧
    ∃ pre : List (Nat × Block Nat), e'.blocks = pre ++ e.blocks ∧
      (∀ p ∈ pre, e.nextLabel ≤ p.1 ∧ p.1 < e'.nextLabel) ∧
      (pre.map Prod.fst).Nodup ∧
      (∀ r ∈ ops.flatMap Op.defs ++ blocksDefs pre, e.nextReg ≤ r ∧ r < e'.nextReg) ∧
      (ops.flatMap Op.defs ++ blocksDefs pre).Nodup

/-- Emitting nothing is growth. -/
theorem Grew.refl (e : Emit) : Grew e [] e :=
  ⟨Nat.le_refl _, Nat.le_refl _, [], rfl, by simp, by simp, by simp, by simp⟩

/-- Growth is transitive: the second stage's registers and labels come after the
first stage's, so the definitions of the two stages stay distinct. -/
theorem Grew.trans {e e₁ e₂ : Emit} {ops₁ ops₂ : List (Op Nat)}
    (h₁ : Grew e ops₁ e₁) (h₂ : Grew e₁ ops₂ e₂) : Grew e (ops₁ ++ ops₂) e₂ := by
  obtain ⟨hr₁, hl₁, pre₁, hb₁, hk₁, hkn₁, hd₁, hdn₁⟩ := h₁
  obtain ⟨hr₂, hl₂, pre₂, hb₂, hk₂, hkn₂, hd₂, hdn₂⟩ := h₂
  obtain ⟨hnA₁, hnB₁, hdisj₁⟩ := List.nodup_append.mp hdn₁
  obtain ⟨hnA₂, hnB₂, hdisj₂⟩ := List.nodup_append.mp hdn₂
  have hA₁ : ∀ r ∈ ops₁.flatMap Op.defs, e.nextReg ≤ r ∧ r < e₁.nextReg :=
    fun r hr => hd₁ r (List.mem_append_left _ hr)
  have hB₁ : ∀ r ∈ blocksDefs pre₁, e.nextReg ≤ r ∧ r < e₁.nextReg :=
    fun r hr => hd₁ r (List.mem_append_right _ hr)
  have hA₂ : ∀ r ∈ ops₂.flatMap Op.defs, e₁.nextReg ≤ r ∧ r < e₂.nextReg :=
    fun r hr => hd₂ r (List.mem_append_left _ hr)
  have hB₂ : ∀ r ∈ blocksDefs pre₂, e₁.nextReg ≤ r ∧ r < e₂.nextReg :=
    fun r hr => hd₂ r (List.mem_append_right _ hr)
  refine ⟨Nat.le_trans hr₁ hr₂, Nat.le_trans hl₁ hl₂, pre₂ ++ pre₁,
    by rw [hb₂, hb₁, List.append_assoc], ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ⟨Nat.le_trans hl₁ (hk₂ p hp).1, (hk₂ p hp).2⟩
    · exact ⟨(hk₁ p hp).1, Nat.lt_of_lt_of_le (hk₁ p hp).2 hl₂⟩
  · rw [List.map_append]
    refine nodup_append_of_disj hkn₂ hkn₁ ?_
    intro x hx hx'
    obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hx'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    have h1 : e₁.nextLabel ≤ u.1 := (hk₂ u hu).1
    have h2 : u.1 < e₁.nextLabel := hqp ▸ (hk₁ q hq).2
    exact absurd h1 (Nat.not_le.mpr h2)
  · intro r hr
    rw [List.flatMap_append, blocksDefs_append] at hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · have h := hA₁ r hr
        omega
      · have h := hA₂ r hr
        omega
    · rcases List.mem_append.mp hr with hr | hr
      · have h := hB₂ r hr
        omega
      · have h := hB₁ r hr
        omega
  · rw [List.flatMap_append, blocksDefs_append]
    refine nodup_append_of_disj (nodup_append_of_disj hnA₁ hnA₂ ?_)
      (nodup_append_of_disj hnB₂ hnB₁ ?_) ?_
    · intro r hr hr'
      have h1 := hA₁ r hr
      have h2 := hA₂ r hr'
      omega
    · intro r hr hr'
      have h1 := hB₂ r hr
      have h2 := hB₁ r hr'
      omega
    · intro r hr hr'
      rcases List.mem_append.mp hr with hr | hr
      · rcases List.mem_append.mp hr' with hr' | hr'
        · have h1 := hA₁ r hr
          have h2 := hB₂ r hr'
          omega
        · exact hdisj₁ r hr r hr' rfl
      · rcases List.mem_append.mp hr' with hr' | hr'
        · exact hdisj₂ r hr r hr' rfl
        · have h1 := hA₂ r hr
          have h2 := hB₁ r hr'
          omega

/-! ## Folding over a `cfg`'s blocks -/

/-- A fold of failing steps fails. -/
theorem foldl_bind_none {α : Type} (F : α → Emit → Option Emit) :
    ∀ l : List α, l.foldl (fun acc i => acc.bind (F i)) none = none
  | [] => rfl
  | _ :: rest => by
      rw [List.foldl_cons]
      exact foldl_bind_none F rest

/-- A reflexive transitive relation that every step of a fold establishes holds
of the whole fold. -/
theorem foldl_bind_rel {α : Type} (F : α → Emit → Option Emit) (Q : Emit → Emit → Prop)
    (hrefl : ∀ e, Q e e) (htrans : ∀ a b c, Q a b → Q b c → Q a c)
    (hF : ∀ i e e', F i e = some e' → Q e e') :
    ∀ (l : List α) (e e' : Emit),
      l.foldl (fun acc i => acc.bind (F i)) (some e) = some e' → Q e e' := by
  intro l
  induction l with
  | nil =>
    intro e e' h
    obtain rfl := Option.some.inj h
    exact hrefl e
  | cons i rest ih =>
    intro e e' h
    rw [List.foldl_cons] at h
    have h' : rest.foldl (fun acc i => acc.bind (F i)) (F i e) = some e' := h
    cases hFi : F i e with
    | none =>
      rw [hFi, foldl_bind_none] at h'
      exact absurd h' (by simp)
    | some e₂ =>
      rw [hFi] at h'
      exact htrans _ _ _ (hF i e e₂ hFi) (ih e₂ e' h')

/-! ## Compiling a term -/

/-- What compiling a term does to the compiler's state: it finishes no blocks,
and spends a fresh interval of registers on the destinations of the ops it
emits. -/
def GrewTm (e : Emit) (ops : List (Op Nat)) (e' : Emit) : Prop :=
  e'.blocks = e.blocks ∧ e'.nextLabel = e.nextLabel ∧ e.nextReg ≤ e'.nextReg ∧
    (∀ r ∈ ops.flatMap Op.defs, e.nextReg ≤ r ∧ r < e'.nextReg) ∧
    (ops.flatMap Op.defs).Nodup

/-- Emitting no ops leaves the state alone. -/
theorem GrewTm.refl (e : Emit) : GrewTm e [] e :=
  ⟨rfl, rfl, Nat.le_refl _, by simp, by simp⟩

/-- Compiling one term after another. -/
theorem GrewTm.trans {e e₁ e₂ : Emit} {ops₁ ops₂ : List (Op Nat)}
    (h₁ : GrewTm e ops₁ e₁) (h₂ : GrewTm e₁ ops₂ e₂) : GrewTm e (ops₁ ++ ops₂) e₂ := by
  obtain ⟨hb₁, hl₁, hr₁, hd₁, hn₁⟩ := h₁
  obtain ⟨hb₂, hl₂, hr₂, hd₂, hn₂⟩ := h₂
  refine ⟨by rw [hb₂, hb₁], by rw [hl₂, hl₁], Nat.le_trans hr₁ hr₂, ?_, ?_⟩
  · intro r hr
    rw [List.flatMap_append] at hr
    rcases List.mem_append.mp hr with hr | hr
    · have h := hd₁ r hr
      exact ⟨h.1, Nat.lt_of_lt_of_le h.2 hr₂⟩
    · have h := hd₂ r hr
      exact ⟨Nat.le_trans hr₁ h.1, h.2⟩
  · rw [List.flatMap_append]
    refine nodup_append_of_disj hn₁ hn₂ ?_
    intro r hr hr'
    have h1 := hd₁ r hr
    have h2 := hd₂ r hr'
    omega

/-- Compiling a term is a special case of growth, with no blocks finished. -/
theorem GrewTm.toGrew {e e' : Emit} {ops : List (Op Nat)} (h : GrewTm e ops e') :
    Grew e ops e' := by
  obtain ⟨hb, hl, hr, hd, hn⟩ := h
  exact ⟨hr, Nat.le_of_eq hl.symm, [], by rw [hb]; simp, by simp, by simp,
    by simpa using hd, by simpa using hn⟩

/-- **Compiling a term grows the compiler's state**: every destination it writes
is a register freshly allocated during the compilation. -/
theorem tmRegs_grew {sigs : List Signature} (t : Tm (Opcode sigs)) :
    ∀ (env : List (List Nat)) (e : Emit) (x : List Nat × List (Op Nat) × Emit),
      tmRegs env t e = some x → GrewTm e x.2.1 x.2.2 := by
  induction t with
  | var i =>
    intro env e x h
    rw [tmRegs, Option.map_eq_some_iff] at h
    obtain ⟨g, -, rfl⟩ := h
    exact GrewTm.refl e
  | unit =>
    intro env e x h
    rw [tmRegs] at h
    obtain rfl := Option.some.inj h
    exact GrewTm.refl e
  | pair a b iha ihb =>
    intro env e x h
    rw [tmRegs, Option.bind_eq_some_iff] at h
    obtain ⟨y, hy, h⟩ := h
    obtain ⟨ra, opa, e₁⟩ := y
    rw [Option.map_eq_some_iff] at h
    obtain ⟨z, hz, rfl⟩ := h
    obtain ⟨rb, opb, e₂⟩ := z
    exact (iha env e _ hy).trans (ihb env e₁ _ hz)
  | op f a ih =>
    intro env e x h
    by_cases hf : f = Opcode.test
    · subst hf
      rw [tmRegs_op_test] at h
      exact absurd h (by simp)
    rw [tmRegs_op hf, Option.bind_eq_some_iff] at h
    obtain ⟨y, hy, h⟩ := h
    obtain ⟨ra, opa, e₁⟩ := y
    rw [Option.map_eq_some_iff] at h
    obtain ⟨o, ho, rfl⟩ := h
    refine (ih env e _ hy).trans ⟨rfl, rfl, Nat.le_add_right _ _, ?_, ?_⟩
    · intro r hr
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, opOf_defs ho] at hr
      have hm := mem_freshRegs.mp hr
      exact ⟨hm.1, hm.2⟩
    · rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, opOf_defs ho]
      exact freshRegs_nodup _ _
  | let₁ a b iha ihb =>
    intro env e x h
    rw [tmRegs, Option.bind_eq_some_iff] at h
    obtain ⟨y, hy, h⟩ := h
    obtain ⟨ra, opa, e₁⟩ := y
    rw [Option.map_eq_some_iff] at h
    obtain ⟨z, hz, rfl⟩ := h
    obtain ⟨rb, opb, e₂⟩ := z
    exact (iha env e _ hy).trans (ihb (ra :: env) e₁ _ hz)
  | let₂ a b iha ihb =>
    intro env e x h
    rw [tmRegs, Option.bind_eq_some_iff] at h
    obtain ⟨y, hy, h⟩ := h
    obtain ⟨ra, opa, e₁⟩ := y
    cases ra with
    | nil => exact absurd h (by simp)
    | cons r rest =>
      rw [Option.map_eq_some_iff] at h
      obtain ⟨z, hz, rfl⟩ := h
      obtain ⟨rb, opb, e₂⟩ := z
      exact (iha env e _ hy).trans (ihb (rest :: [r] :: env) e₁ _ hz)
  | inl a ih => intro env e x h; rw [tmRegs] at h; exact absurd h (by simp)
  | inr a ih => intro env e x h; rw [tmRegs] at h; exact absurd h (by simp)
  | case a l r iha ihl ihr => intro env e x h; rw [tmRegs] at h; exact absurd h (by simp)
  | abort a ih => intro env e x h; rw [tmRegs] at h; exact absurd h (by simp)

/-- **A conditional-branch arm transfers to a label the compiler was given**, at
the width recorded for that label, and leaves the compiler's state alone: it
emits no op and finishes no block. -/
theorem condArm_eq {sigs : List Signature} {r : Region (Opcode sigs)} {a : Ann}
    {env : List (List Nat)} {labels : List (Target × Nat)} {e e' : Emit} {t : Nat}
    {rs : List Nat} (h : condArm r a env labels e = some (t, rs, e')) :
    (Target.block t, rs.length) ∈ labels ∧ GrewTm e [] e' := by
  unfold condArm at h
  split at h
  · rw [Option.bind_eq_some_iff] at h
    obtain ⟨p, hp, h⟩ := h
    have hpm : p ∈ labels := List.mem_of_getElem? hp
    obtain ⟨tgt, w⟩ := p
    cases tgt with
    | block tb =>
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨y, hrs, h⟩ := h
      obtain ⟨rs', opsA, e₁⟩ := y
      cases opsA with
      | nil =>
        dsimp only at h
        split_ifs at h with hw
        rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨by rw [hw]; exact hpm, tmRegs_grew _ _ _ _ hrs⟩
      | cons => exact absurd h (by simp)
    | ret => exact absurd h (by simp)
    | trap => exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **A conditional branch keeps the prefix it was given and emits nothing
more.** Its two targets are labels the compiler was given, carrying tuples of
the widths recorded for them, and the compiler's state is otherwise untouched,
so a `case` of this shape needs no block of its own. -/
theorem condOf_eq {sigs : List Signature} {left right : Region (Opcode sigs)} {al ar : Ann}
    {c : Nat} {ops ops' : List (Op Nat)} {env : List (List Nat)}
    {labels : List (Target × Nat)} {e e' : Emit} {t : Term Nat}
    (h : condOf left right al ar c ops env labels e = some (ops', t, e')) :
    ops' = ops ∧ GrewTm e [] e' ∧
      ∃ t₁ t₂ rs₁ rs₂, t = .cond c t₁ rs₁ t₂ rs₂ ∧
        (Target.block t₁, rs₁.length) ∈ labels ∧ (Target.block t₂, rs₂.length) ∈ labels := by
  rw [condOf, Option.bind_eq_some_iff] at h
  obtain ⟨y, hL, h⟩ := h
  obtain ⟨t₁, rs₁, e₁⟩ := y
  rw [Option.map_eq_some_iff] at h
  obtain ⟨z, hR, hz⟩ := h
  obtain ⟨t₂, rs₂, e₂⟩ := z
  rw [Prod.mk.injEq, Prod.mk.injEq] at hz
  obtain ⟨rfl, rfl, rfl⟩ := hz
  obtain ⟨hm₁, hg₁⟩ := condArm_eq hL
  obtain ⟨hm₂, hg₂⟩ := condArm_eq hR
  exact ⟨rfl, by simpa using hg₁.trans hg₂, t₁, t₂, rs₁, rs₂, rfl, hm₁, hm₂⟩

/-! ## Finishing a block -/

/-- Finishing a block whose label was allocated immediately before the region
that fills it, as the `case` arm's true branch is. -/
theorem Grew.pushBlock {e e' : Emit} {ops : List (Op Nat)} {t : Term Nat}
    (h : Grew { e with nextLabel := e.nextLabel + 1 } ops e') :
    Grew e [] { e' with blocks := (e.nextLabel, ⟨[], ops, t⟩) :: e'.blocks } := by
  obtain ⟨hr, hl, pre, hb, hk, hkn, hd, hdn⟩ := h
  dsimp only at hl hr hd hb hk
  refine ⟨?_, ?_, (e.nextLabel, ⟨[], ops, t⟩) :: pre, ?_, ?_, ?_, ?_, ?_⟩ <;> (try dsimp only)
  · exact hr
  · omega
  · rw [hb]
    rfl
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨Nat.le_refl _, by omega⟩
    · have hkp := hk p hp
      omega
  · rw [List.map_cons]
    refine List.nodup_cons.mpr ⟨?_, hkn⟩
    intro hmem
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hmem
    have hkq := hk q hq
    omega
  · simpa [Block.defs] using hd
  · simpa [Block.defs] using hdn

/-- Finishing a block at a label allocated once the region that fills it has
been compiled, as the `case` arm's false branch is. -/
theorem Grew.pushBlockEnd {e e' : Emit} {ops : List (Op Nat)} {t : Term Nat}
    (h : Grew e ops e') :
    Grew e []
      { e' with
        nextLabel := e'.nextLabel + 1,
        blocks := (e'.nextLabel, ⟨[], ops, t⟩) :: e'.blocks } := by
  obtain ⟨hr, hl, pre, hb, hk, hkn, hd, hdn⟩ := h
  refine ⟨?_, ?_, (e'.nextLabel, ⟨[], ops, t⟩) :: pre, ?_, ?_, ?_, ?_, ?_⟩ <;> (try dsimp only)
  · exact hr
  · omega
  · rw [hb]
    rfl
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hl, by omega⟩
    · have hkp := hk p hp
      omega
  · rw [List.map_cons]
    refine List.nodup_cons.mpr ⟨?_, hkn⟩
    intro hmem
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hmem
    have hkq := hk q hq
    omega
  · simpa [Block.defs] using hd
  · simpa [Block.defs] using hdn

/-- Labels allocated before a stage began are still allocated inside it. -/
theorem Grew.ofBumpLabel {e e' : Emit} {ops : List (Op Nat)} {n : Nat}
    (h : Grew { e with nextLabel := e.nextLabel + n } ops e') : Grew e ops e' := by
  obtain ⟨hr, hl, pre, hb, hk, hkn, hd, hdn⟩ := h
  dsimp only at hl hr hd hb hk
  refine ⟨hr, by omega, pre, hb, ?_, hkn, hd, hdn⟩
  intro p hp
  have hkp := hk p hp
  omega

/-- **The fold over a `cfg`'s blocks grows the state.** The labels of the
`cfg`'s own blocks were allocated before the fold began, so they lie below the
interval the fold opens and have to be tracked separately from it. -/
theorem foldl_grew_cfg {α : Type} (F : α → Emit → Option Emit) (key : α → Nat)
    (hF : ∀ i e e', key i < e.nextLabel → F i e = some e' →
      e.nextReg ≤ e'.nextReg ∧ e.nextLabel ≤ e'.nextLabel ∧
        ∃ pre, e'.blocks = pre ++ e.blocks ∧
          (∀ p ∈ pre, p.1 = key i ∨ (e.nextLabel ≤ p.1 ∧ p.1 < e'.nextLabel)) ∧
          (pre.map Prod.fst).Nodup ∧
          (∀ r ∈ blocksDefs pre, e.nextReg ≤ r ∧ r < e'.nextReg) ∧ (blocksDefs pre).Nodup) :
    ∀ (l : List α) (e e' : Emit), (l.map key).Nodup → (∀ i ∈ l, key i < e.nextLabel) →
      l.foldl (fun acc i => acc.bind (F i)) (some e) = some e' →
      e.nextReg ≤ e'.nextReg ∧ e.nextLabel ≤ e'.nextLabel ∧
        ∃ pre, e'.blocks = pre ++ e.blocks ∧
          (∀ p ∈ pre, (∃ i ∈ l, p.1 = key i) ∨ (e.nextLabel ≤ p.1 ∧ p.1 < e'.nextLabel)) ∧
          (pre.map Prod.fst).Nodup ∧
          (∀ r ∈ blocksDefs pre, e.nextReg ≤ r ∧ r < e'.nextReg) ∧
          (blocksDefs pre).Nodup := by
  intro l
  induction l with
  | nil =>
    intro e e' _ _ h
    obtain rfl := Option.some.inj h
    exact ⟨Nat.le_refl _, Nat.le_refl _, [], rfl, by simp, by simp, by simp, by simp⟩
  | cons i rest ih =>
    intro e e' hnd hkey h
    rw [List.foldl_cons] at h
    have h' : rest.foldl (fun acc j => acc.bind (F j)) (F i e) = some e' := h
    cases hFi : F i e with
    | none =>
      rw [hFi, foldl_bind_none] at h'
      exact absurd h' (by simp)
    | some e₃ =>
      rw [hFi] at h'
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hnotin, hnd'⟩ := hnd
      obtain ⟨hr₁, hl₁, pre₁, hb₁, hk₁, hkn₁, hd₁, hdn₁⟩ :=
        hF i e e₃ (hkey i List.mem_cons_self) hFi
      have hkey' : ∀ j ∈ rest, key j < e₃.nextLabel := by
        intro j hj
        have := hkey j (List.mem_cons_of_mem _ hj)
        omega
      obtain ⟨hr₂, hl₂, pre₂, hb₂, hk₂, hkn₂, hd₂, hdn₂⟩ := ih e₃ e' hnd' hkey' h'
      have hdisj : ∀ x ∈ pre₂.map Prod.fst, x ∉ pre₁.map Prod.fst := by
        intro x hx hx'
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        obtain ⟨u, hu, hue⟩ := List.mem_map.mp hx'
        rcases hk₂ q hq with ⟨j, hj, hjq⟩ | hq'
        · have hkj := hkey j (List.mem_cons_of_mem _ hj)
          rcases hk₁ u hu with hu' | hu'
          · exact hnotin (List.mem_map.mpr ⟨j, hj, by rw [← hjq, ← hue]; exact hu'⟩)
          · omega
        · rcases hk₁ u hu with hu' | hu'
          · have := hkey i List.mem_cons_self
            omega
          · omega
      refine ⟨by omega, by omega, pre₂ ++ pre₁,
        by rw [hb₂, hb₁, List.append_assoc], ?_, ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · rcases hk₂ p hp with ⟨j, hj, hjp⟩ | hp'
          · exact Or.inl ⟨j, List.mem_cons_of_mem _ hj, hjp⟩
          · exact Or.inr ⟨by omega, hp'.2⟩
        · rcases hk₁ p hp with hp' | hp'
          · exact Or.inl ⟨i, List.mem_cons_self, hp'⟩
          · exact Or.inr ⟨hp'.1, by omega⟩
      · rw [List.map_append]
        exact nodup_append_of_disj hkn₂ hkn₁ hdisj
      · intro r hr
        rw [blocksDefs_append] at hr
        rcases List.mem_append.mp hr with hr | hr
        · have := hd₂ r hr
          omega
        · have := hd₁ r hr
          omega
      · rw [blocksDefs_append]
        refine nodup_append_of_disj hdn₂ hdn₁ ?_
        intro r hr hr'
        have h1 := hd₂ r hr
        have h2 := hd₁ r hr'
        omega

set_option linter.unusedTactic false in
/-- **Compiling a region grows the compiler's state**: every block it finishes
carries a label allocated during the compilation, those labels are distinct, and
every register it defines — by a straight-line op or by one of those blocks — is
a distinct register allocated during the compilation. -/
theorem regionOps_grew {sigs : List Signature} (r : Region (Opcode sigs)) (a : Ann)
    (env : List (List Nat)) (labels : List (Target × Nat)) (e : Emit) :
    ∀ x, regionOps r a env labels e = some x → Grew e x.1 x.2.2 := by
  induction r, a, env, labels, e using regionOps.induct with
  | case1 env labels e ℓ arg =>
    intro x h
    rw [regionOps, Option.bind_eq_some_iff] at h
    obtain ⟨p, -, h⟩ := h
    obtain ⟨tgt, w⟩ := p
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨y, hrs, h⟩ := h
    obtain ⟨rs, ops, e₁⟩ := y
    have hg := (tmRegs_grew arg env e _ hrs).toGrew
    dsimp only at h
    split_ifs at h
    cases tgt with
    | block t =>
      obtain rfl := Option.some.inj h
      exact hg
    | ret =>
      obtain rfl := Option.some.inj h
      exact hg
    | trap =>
      obtain rfl := Option.some.inj h
      exact hg
  | case2 env labels e v body ab ih =>
    intro x h
    rw [regionOps, Option.bind_eq_some_iff] at h
    obtain ⟨y, hrv, h⟩ := h
    obtain ⟨rv, ops, e₁⟩ := y
    rw [Option.map_eq_some_iff] at h
    obtain ⟨z, hbody, rfl⟩ := h
    obtain ⟨ops', t, e₂⟩ := z
    exact (tmRegs_grew v env e _ hrv).toGrew.trans (ih rv e₁ _ hbody)
  | case3 env labels e v body ab ih =>
    intro x h
    rw [regionOps, Option.bind_eq_some_iff] at h
    obtain ⟨y, hrv, h⟩ := h
    obtain ⟨rv, ops, e₁⟩ := y
    cases rv with
    | nil => exact absurd h (by simp)
    | cons rr rest =>
      rw [Option.map_eq_some_iff] at h
      obtain ⟨z, hbody, rfl⟩ := h
      obtain ⟨ops', t, e₂⟩ := z
      exact (tmRegs_grew v env e _ hrv).toGrew.trans (ih e₁ rr rest _ hbody)
  | case4 env labels e left right al ar arg ihL ihR =>
    intro x h
    rw [regionOps, Option.bind_eq_some_iff] at h
    obtain ⟨y, hrs, h⟩ := h
    obtain ⟨rs, ops, e₁⟩ := y
    have hg := (tmRegs_grew arg env e _ hrs).toGrew
    cases rs with
    | nil => exact absurd h (by simp)
    | cons c rest =>
      cases rest with
      | cons _ _ => exact absurd h (by simp)
      | nil =>
        dsimp only at h
        cases hcond : condOf left right al ar c ops env labels e₁ with
        | some res =>
          obtain ⟨ops', t', e''⟩ := res
          rw [hcond] at h
          dsimp only at h
          obtain rfl := Option.some.inj h
          obtain ⟨rfl, hgc, -⟩ := condOf_eq hcond
          simpa using hg.trans hgc.toGrew
        | none =>
          rw [hcond] at h
          dsimp only at h
          rw [Option.bind_eq_some_iff] at h
          obtain ⟨y, hL, h⟩ := h
          obtain ⟨opsL, tL, e₃⟩ := y
          rw [Option.map_eq_some_iff] at h
          obtain ⟨z, hR, rfl⟩ := h
          obtain ⟨opsR, tR, e₄⟩ := z
          have gL := Grew.pushBlock (t := tL) (ihL e₁ _ hL)
          have gR := Grew.pushBlockEnd (t := tR) (ihR e₁ opsL tL e₃ _ hR)
          have hall := hg.trans (gL.trans gR)
          simpa using hall
  | case5 env labels e discr left right al ar hne =>
    intro x h
    rw [regionOps] at h
    exact absurd h (by simp)
    all_goals assumption
  | case6 env labels e entry ws ae abs base blocks inner labels' e₀ ihentry ihblocks =>
    intro x h
    rw [regionOps] at h
    split_ifs at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨y, hentry, h⟩ := h
    obtain ⟨ops, t, e₁⟩ := y
    rw [Option.map_eq_some_iff] at h
    obtain ⟨e₂, hfold, rfl⟩ := h
    have G0 : Grew { e with nextLabel := e.nextLabel + ws.length } ops e₁ := ihentry _ hentry
    obtain ⟨hr₀, hl₀, preE, hbE, hkE, hknE, hdE, hdnE⟩ := G0
    dsimp only at hr₀ hl₀ hbE hkE hdE
    have KEY : e₁.nextReg ≤ e₂.nextReg ∧ e₁.nextLabel ≤ e₂.nextLabel ∧
        ∃ pre, e₂.blocks = pre ++ e₁.blocks ∧
          (∀ p ∈ pre, (∃ i ∈ List.finRange ws.length, p.1 = e.nextLabel + i.val) ∨
            (e₁.nextLabel ≤ p.1 ∧ p.1 < e₂.nextLabel)) ∧
          (pre.map Prod.fst).Nodup ∧
          (∀ r ∈ blocksDefs pre, e₁.nextReg ≤ r ∧ r < e₂.nextReg) ∧
          (blocksDefs pre).Nodup := by
      refine foldl_grew_cfg _ (fun i : Fin ws.length => e.nextLabel + i.val) ?_
        (List.finRange ws.length) e₁ e₂ ?_ ?_ hfold
      · intro i u u' hlt hFu
        rw [Option.map_eq_some_iff] at hFu
        obtain ⟨z, hB, rfl⟩ := hFu
        obtain ⟨opsB, tB, e₃⟩ := z
        obtain ⟨hr, hl, preB, hbB, hkB, hknB, hdB, hdnB⟩ := ihblocks i u _ hB
        dsimp only at hr hl hbB hkB hdB hlt ⊢
        refine ⟨by omega, hl, (e.nextLabel + i.val,
          ⟨freshRegs u.nextReg (ws.getD i.val 0), opsB, tB⟩) :: preB, by rw [hbB]; rfl,
          ?_, ?_, ?_, ?_⟩
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inl rfl
          · have hkq := hkB q hq
            exact Or.inr ⟨by omega, by omega⟩
        · rw [List.map_cons]
          refine List.nodup_cons.mpr ⟨?_, hknB⟩
          intro hmem
          obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hmem
          have hkq := hkB q hq
          omega
        · intro rr hrr
          rw [blocksDefs_cons] at hrr
          rcases List.mem_append.mp hrr with hrr | hrr
          · rcases List.mem_append.mp hrr with hrr | hrr
            · have := mem_freshRegs.mp hrr
              omega
            · have := hdB rr (List.mem_append_left _ hrr)
              omega
          · have := hdB rr (List.mem_append_right _ hrr)
            omega
        · rw [blocksDefs_cons]
          refine (List.append_assoc _ _ _) ▸ nodup_append_of_disj (freshRegs_nodup _ _) hdnB ?_
          intro rr hrr hrr'
          have h1 := mem_freshRegs.mp hrr
          have h2 := hdB rr hrr'
          omega
      · refine List.Nodup.map ?_ (List.nodup_finRange _)
        intro i j hij
        have hij' : e.nextLabel + i.val = e.nextLabel + j.val := hij
        exact Fin.ext (by omega)
      · intro i _
        show e.nextLabel + i.val < e₁.nextLabel
        have hi : i.val < ws.length := i.isLt
        omega
    obtain ⟨hrF, hlF, preF, hbF, hkF, hknF, hdF, hdnF⟩ := KEY
    show Grew e ops e₂
    refine ⟨by omega, by omega, preF ++ preE,
      by rw [hbF, hbE, List.append_assoc], ?_, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · rcases hkF p hp with ⟨i, -, hip⟩ | hp'
        · have hi : i.val < ws.length := i.isLt
          exact ⟨by omega, by omega⟩
        · exact ⟨by omega, hp'.2⟩
      · have hkp := hkE p hp
        exact ⟨by omega, by omega⟩
    · rw [List.map_append]
      refine nodup_append_of_disj hknF hknE ?_
      intro xx hxx hxx'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hxx
      obtain ⟨u, hu, hue⟩ := List.mem_map.mp hxx'
      have hE := hkE u hu
      rcases hkF q hq with ⟨i, -, hiq⟩ | hq'
      · have hi : i.val < ws.length := i.isLt
        omega
      · omega
    · intro rr hrr
      rw [blocksDefs_append] at hrr
      rcases List.mem_append.mp hrr with hrr | hrr
      · have := hdE rr (List.mem_append_left _ hrr)
        omega
      · rcases List.mem_append.mp hrr with hrr | hrr
        · have := hdF rr hrr
          omega
        · have := hdE rr (List.mem_append_right _ hrr)
          omega
    · rw [blocksDefs_append]
      obtain ⟨hnA, hnBE, hdisjE⟩ := List.nodup_append.mp hdnE
      refine nodup_append_of_disj hnA (nodup_append_of_disj hdnF hnBE ?_) ?_
      · intro rr hrr hrr'
        have h1 := hdF rr hrr
        have h2 := hdE rr (List.mem_append_right _ hrr')
        omega
      · intro rr hrr hrr'
        rcases List.mem_append.mp hrr' with hrr' | hrr'
        · have h1 := hdE rr (List.mem_append_left _ hrr)
          have h2 := hdF rr hrr'
          omega
        · exact hdisjE rr hrr rr hrr' rfl
  | case7 env labels e entry k blocks ws ae abs hne =>
    intro x h
    rw [regionOps] at h
    simp [hne] at h
  | case8 t a env labels e k1 k2 k3 k4 k5 =>
    intro x h
    rw [regionOps] at h
    exact absurd h (by simp)
    all_goals assumption

/-! ## Calls name their callee's arity -/

/-- Every call of every block emitted so far names its callee's declared
arity. -/
def BlocksCallsMatch (sigs : List Signature) (bs : List (Nat × Block Nat)) : Prop :=
  ∀ p ∈ bs, OpsCallsMatch sigs p.2.ops

/-- An empty op list has no calls to get wrong. -/
theorem opsCallsMatch_nil {sigs : List Signature} :
    OpsCallsMatch sigs ([] : List (Op Nat)) := by
  intro o ho
  exact absurd ho (by simp)

/-- Concatenating two op lists whose calls are correct. -/
theorem OpsCallsMatch.append {sigs : List Signature} {o₁ o₂ : List (Op Nat)}
    (h₁ : OpsCallsMatch sigs o₁) (h₂ : OpsCallsMatch sigs o₂) :
    OpsCallsMatch sigs (o₁ ++ o₂) := by
  intro o ho
  rcases List.mem_append.mp ho with h | h
  · exact h₁ o h
  · exact h₂ o h

/-- Only the call opcode builds a call. -/
theorem opOf_eq_call {sigs : List Signature} {f : Opcode sigs} {as ds : List Nat}
    {c : FuncId} {args res : List Nat} (h : opOf f as ds = some (.call c args res)) :
    f = .call c := by
  unfold opOf at h
  split at h <;> simp_all

/-- A call built by `opOf` names its callee's arity: `opOf` checked the argument
registers against the opcode's operand count, and the destinations were
allocated from its result count. -/
theorem opOf_callsMatch {sigs : List Signature} {f : Opcode sigs} {as ds : List Nat}
    {o : Op Nat} (h : opOf f as ds = some o) (hds : ds.length = f.results) :
    OpsCallsMatch sigs [o] := by
  rintro o' ho' c args res rfl
  rw [List.mem_singleton] at ho'
  subst ho'
  have hf : f = .call c := opOf_eq_call h
  subst hf
  refine ⟨?_, ?_⟩
  · rw [show args = as from opOf_uses h]
    exact opOf_arity h
  · rw [show res = ds from opOf_defs h]
    exact hds

/-- **Every call a term's compilation emits names its callee's arity.** -/
theorem tmRegs_callsMatch {sigs : List Signature} (t : Tm (Opcode sigs)) :
    ∀ (env : List (List Nat)) (e : Emit) (x : List Nat × List (Op Nat) × Emit),
      tmRegs env t e = some x → OpsCallsMatch sigs x.2.1 := by
  induction t with
  | var i =>
    intro env e x h
    rw [tmRegs, Option.map_eq_some_iff] at h
    obtain ⟨g, -, rfl⟩ := h
    exact opsCallsMatch_nil
  | unit =>
    intro env e x h
    rw [tmRegs] at h
    obtain rfl := Option.some.inj h
    exact opsCallsMatch_nil
  | pair a b iha ihb =>
    intro env e x h
    rw [tmRegs, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ra, opa, e₁⟩, hy, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨rb, opb, e₂⟩, hz, rfl⟩ := h
    exact (iha env e _ hy).append (ihb env e₁ _ hz)
  | op f a ih =>
    intro env e x h
    by_cases hf : f = Opcode.test
    · subst hf
      rw [tmRegs_op_test] at h
      exact absurd h (by simp)
    rw [tmRegs_op hf, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ra, opa, e₁⟩, hy, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨o, ho, rfl⟩ := h
    exact (ih env e _ hy).append (opOf_callsMatch ho (freshRegs_length _ _))
  | let₁ a b iha ihb =>
    intro env e x h
    rw [tmRegs, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ra, opa, e₁⟩, hy, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨rb, opb, e₂⟩, hz, rfl⟩ := h
    exact (iha env e _ hy).append (ihb (ra :: env) e₁ _ hz)
  | let₂ a b iha ihb =>
    intro env e x h
    rw [tmRegs, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ra, opa, e₁⟩, hy, h⟩ := h
    cases ra with
    | nil => exact absurd h (by simp)
    | cons r rest =>
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨rb, opb, e₂⟩, hz, rfl⟩ := h
      exact (iha env e _ hy).append (ihb (rest :: [r] :: env) e₁ _ hz)
  | inl a ih => intro env e x h; rw [tmRegs] at h; exact absurd h (by simp)
  | inr a ih => intro env e x h; rw [tmRegs] at h; exact absurd h (by simp)
  | case a l r iha ihl ihr => intro env e x h; rw [tmRegs] at h; exact absurd h (by simp)
  | abort a ih => intro env e x h; rw [tmRegs] at h; exact absurd h (by simp)

set_option linter.unusedTactic false in
/-- **Every call the compiler emits names its callee's arity**, for a region as
for a term: the destinations came from the opcode's result count and the
arguments were checked against its operand count. -/
theorem regionOps_callsMatch {sigs : List Signature} (r : Region (Opcode sigs)) (a : Ann)
    (env : List (List Nat)) (labels : List (Target × Nat)) (e : Emit) :
    ∀ x, regionOps r a env labels e = some x → BlocksCallsMatch sigs e.blocks →
      OpsCallsMatch sigs x.1 ∧ BlocksCallsMatch sigs x.2.2.blocks := by
  induction r, a, env, labels, e using regionOps.induct with
  | case1 env labels e ℓ arg =>
    intro x h hbs
    rw [regionOps, Option.bind_eq_some_iff] at h
    obtain ⟨p, -, h⟩ := h
    obtain ⟨tgt, w⟩ := p
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨y, hrs, h⟩ := h
    obtain ⟨rs, ops, e₁⟩ := y
    have hops := tmRegs_callsMatch arg env e _ hrs
    have hblk : e₁.blocks = e.blocks := (tmRegs_grew arg env e _ hrs).1
    dsimp only at h
    split_ifs at h
    cases tgt with
    | block t =>
      obtain rfl := Option.some.inj h
      exact ⟨hops, by rw [hblk]; exact hbs⟩
    | ret =>
      obtain rfl := Option.some.inj h
      exact ⟨hops, by rw [hblk]; exact hbs⟩
    | trap =>
      obtain rfl := Option.some.inj h
      exact ⟨hops, by rw [hblk]; exact hbs⟩
  | case2 env labels e v body ab ih =>
    intro x h hbs
    rw [regionOps, Option.bind_eq_some_iff] at h
    obtain ⟨y, hrv, h⟩ := h
    obtain ⟨rv, ops, e₁⟩ := y
    rw [Option.map_eq_some_iff] at h
    obtain ⟨z, hbody, rfl⟩ := h
    obtain ⟨ops', t, e₂⟩ := z
    have h1 := tmRegs_callsMatch v env e _ hrv
    have hblk : e₁.blocks = e.blocks := (tmRegs_grew v env e _ hrv).1
    obtain ⟨h2, h3⟩ := ih rv e₁ _ hbody (by rw [hblk]; exact hbs)
    exact ⟨h1.append h2, h3⟩
  | case3 env labels e v body ab ih =>
    intro x h hbs
    rw [regionOps, Option.bind_eq_some_iff] at h
    obtain ⟨y, hrv, h⟩ := h
    obtain ⟨rv, ops, e₁⟩ := y
    have h1 := tmRegs_callsMatch v env e _ hrv
    have hblk : e₁.blocks = e.blocks := (tmRegs_grew v env e _ hrv).1
    cases rv with
    | nil => exact absurd h (by simp)
    | cons rr rest =>
      rw [Option.map_eq_some_iff] at h
      obtain ⟨z, hbody, rfl⟩ := h
      obtain ⟨ops', t, e₂⟩ := z
      obtain ⟨h2, h3⟩ := ih e₁ rr rest _ hbody (by rw [hblk]; exact hbs)
      exact ⟨h1.append h2, h3⟩
  | case4 env labels e left right al ar arg ihL ihR =>
    intro x h hbs
    rw [regionOps, Option.bind_eq_some_iff] at h
    obtain ⟨y, hrs, h⟩ := h
    obtain ⟨rs, ops, e₁⟩ := y
    have h1 := tmRegs_callsMatch arg env e _ hrs
    have hblk : e₁.blocks = e.blocks := (tmRegs_grew arg env e _ hrs).1
    cases rs with
    | nil => exact absurd h (by simp)
    | cons c rest =>
      cases rest with
      | cons _ _ => exact absurd h (by simp)
      | nil =>
        dsimp only at h
        cases hcond : condOf left right al ar c ops env labels e₁ with
        | some res =>
          obtain ⟨ops', t', e''⟩ := res
          rw [hcond] at h
          dsimp only at h
          obtain rfl := Option.some.inj h
          obtain ⟨rfl, hgc, -⟩ := condOf_eq hcond
          exact ⟨h1, by rw [hgc.1, hblk]; exact hbs⟩
        | none =>
          rw [hcond] at h
          dsimp only at h
          rw [Option.bind_eq_some_iff] at h
          obtain ⟨y, hL, h⟩ := h
          obtain ⟨opsL, tL, e₃⟩ := y
          rw [Option.map_eq_some_iff] at h
          obtain ⟨z, hR, rfl⟩ := h
          obtain ⟨opsR, tR, e₄⟩ := z
          obtain ⟨g1, g2⟩ := ihL e₁ _ hL (by rw [hblk]; exact hbs)
          have hbs' : BlocksCallsMatch sigs ((e₁.nextLabel, ⟨[], opsL, tL⟩) :: e₃.blocks) := by
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact g1
            · exact g2 q hq
          obtain ⟨g3, g4⟩ := ihR e₁ opsL tL e₃ _ hR hbs'
          refine ⟨h1, ?_⟩
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact g3
          · exact g4 q hq
  | case5 env labels e discr left right al ar hne =>
    intro x h hbs
    rw [regionOps] at h
    exact absurd h (by simp)
    all_goals assumption
  | case6 env labels e entry ws ae abs base blocks inner labels' e₀ ihentry ihblocks =>
    intro x h hbs
    rw [regionOps] at h
    split_ifs at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨y, hentry, h⟩ := h
    obtain ⟨ops, t, e₁⟩ := y
    rw [Option.map_eq_some_iff] at h
    obtain ⟨e₂, hfold, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ihentry _ hentry hbs
    refine ⟨h1, ?_⟩
    refine foldl_bind_rel _
      (fun u v => BlocksCallsMatch sigs u.blocks → BlocksCallsMatch sigs v.blocks)
      (fun _ hh => hh) (fun _ _ _ hab hbc hh => hbc (hab hh)) ?_ _ e₁ e₂ hfold h2
    intro i e' e'' hstep
    rw [Option.map_eq_some_iff] at hstep
    obtain ⟨y, hB, rfl⟩ := hstep
    obtain ⟨opsB, tB, e₃⟩ := y
    intro hh
    obtain ⟨g1, g2⟩ := ihblocks i e' _ hB hh
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact g1
    · exact g2 q hq
  | case7 env labels e entry k blocks ws ae abs hne =>
    intro x h hbs
    rw [regionOps] at h
    simp [hne] at h
  | case8 t a env labels e k1 k2 k3 k4 k5 =>
    intro x h hbs
    rw [regionOps] at h
    exact absurd h (by simp)
    all_goals assumption

/-! ## Terminators -/

/-- A terminator names only labels that have been allocated, and returns the
declared number of values. -/
def TermOk (results bound : Nat) (t : Term Nat) : Prop :=
  (∀ l ∈ t.successors, l < bound) ∧ ∀ vs, t = .ret vs → vs.length = results

/-- Allocating more labels is no obstacle. -/
theorem TermOk.mono {results b b' : Nat} {t : Term Nat} (h : TermOk results b t) (hb : b ≤ b') :
    TermOk results b' t := ⟨fun l hl => Nat.lt_of_lt_of_le (h.1 l hl) hb, h.2⟩

/-- Every label the compiler was given goes to an allocated block or out of the
function, and the return label carries the declared number of values. -/
def TargetsOk (results bound : Nat) (labels : List (Target × Nat)) : Prop :=
  ∀ p ∈ labels, (∀ l, p.1 = Target.block l → l < bound) ∧ (p.1 = Target.ret → p.2 = results)

/-- Allocating more labels is no obstacle. -/
theorem TargetsOk.mono {results b b' : Nat} {labels : List (Target × Nat)}
    (h : TargetsOk results b labels) (hb : b ≤ b') : TargetsOk results b' labels :=
  fun p hp => ⟨fun l hl => Nat.lt_of_lt_of_le ((h p hp).1 l hl) hb, (h p hp).2⟩

set_option linter.unusedTactic false in
/-- **Every terminator the compiler emits names an allocated label**, and every
`ret` it emits returns the declared number of values, because `regionOps` checks
each branch's width against its target's recorded width. -/
theorem regionOps_terms {sigs : List Signature} {results : Nat} (r : Region (Opcode sigs))
    (a : Ann) (env : List (List Nat)) (labels : List (Target × Nat)) (e : Emit) :
    ∀ (ops : List (Op Nat)) (t : Term Nat) (e' : Emit),
      regionOps r a env labels e = some (ops, t, e') → TargetsOk results e.nextLabel labels →
      (∀ p ∈ e.blocks, TermOk results e.nextLabel p.2.term) →
      TermOk results e'.nextLabel t ∧
        ∀ p ∈ e'.blocks, TermOk results e'.nextLabel p.2.term := by
  induction r, a, env, labels, e using regionOps.induct with
  | case1 env labels e ℓ arg =>
    intro ops₀ t₀ e' h htg hbl
    rw [regionOps, Option.bind_eq_some_iff] at h
    obtain ⟨p, hp, h⟩ := h
    have hpm : p ∈ labels := List.mem_of_getElem? hp
    obtain ⟨tgt, w⟩ := p
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨y, hrs, h⟩ := h
    obtain ⟨rs, ops, e₁⟩ := y
    have hblk : e₁.blocks = e.blocks := (tmRegs_grew arg env e _ hrs).1
    have hlab : e₁.nextLabel = e.nextLabel := (tmRegs_grew arg env e _ hrs).2.1
    dsimp only at h
    split_ifs at h with hw
    cases tgt with
    | block t =>
      rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨⟨?_, by simp⟩, ?_⟩
      · intro l hl
        rw [Term.successors, List.mem_singleton] at hl
        rw [hlab, hl]
        exact (htg _ hpm).1 t rfl
      · intro q hq
        rw [hblk] at hq
        exact (hbl q hq).mono (Nat.le_of_eq hlab.symm)
    | ret =>
      rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨⟨by simp [Term.successors], ?_⟩, ?_⟩
      · intro vs hvs
        rw [Term.ret.injEq] at hvs
        subst hvs
        rw [hw]
        exact (htg _ hpm).2 rfl
      · intro q hq
        rw [hblk] at hq
        exact (hbl q hq).mono (Nat.le_of_eq hlab.symm)
    | trap =>
      rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨⟨by simp [Term.successors], by simp⟩, ?_⟩
      intro q hq
      rw [hblk] at hq
      exact (hbl q hq).mono (Nat.le_of_eq hlab.symm)
  | case2 env labels e v body ab ih =>
    intro ops₀ t₀ e' h htg hbl
    rw [regionOps, Option.bind_eq_some_iff] at h
    obtain ⟨y, hrv, h⟩ := h
    obtain ⟨rv, ops, e₁⟩ := y
    have hblk : e₁.blocks = e.blocks := (tmRegs_grew v env e _ hrv).1
    have hlab : e₁.nextLabel = e.nextLabel := (tmRegs_grew v env e _ hrv).2.1
    rw [Option.map_eq_some_iff] at h
    obtain ⟨z, hbody, hz⟩ := h
    obtain ⟨ops', t, e₂⟩ := z
    rw [Prod.mk.injEq, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl, rfl⟩ := hz
    exact ih rv e₁ _ _ _ hbody (by rw [hlab]; exact htg) (by rw [hblk, hlab]; exact hbl)
  | case3 env labels e v body ab ih =>
    intro ops₀ t₀ e' h htg hbl
    rw [regionOps, Option.bind_eq_some_iff] at h
    obtain ⟨y, hrv, h⟩ := h
    obtain ⟨rv, ops, e₁⟩ := y
    have hblk : e₁.blocks = e.blocks := (tmRegs_grew v env e _ hrv).1
    have hlab : e₁.nextLabel = e.nextLabel := (tmRegs_grew v env e _ hrv).2.1
    cases rv with
    | nil => exact absurd h (by simp)
    | cons rr rest =>
      rw [Option.map_eq_some_iff] at h
      obtain ⟨z, hbody, hz⟩ := h
      obtain ⟨ops', t, e₂⟩ := z
      rw [Prod.mk.injEq, Prod.mk.injEq] at hz
      obtain ⟨rfl, rfl, rfl⟩ := hz
      exact ih e₁ rr rest _ _ _ hbody (by rw [hlab]; exact htg) (by rw [hblk, hlab]; exact hbl)
  | case4 env labels e left right al ar arg ihL ihR =>
    intro ops₀ t₀ e' h htg hbl
    rw [regionOps, Option.bind_eq_some_iff] at h
    obtain ⟨y, hrs, h⟩ := h
    obtain ⟨rs, ops, e₁⟩ := y
    have hblk : e₁.blocks = e.blocks := (tmRegs_grew arg env e _ hrs).1
    have hlab : e₁.nextLabel = e.nextLabel := (tmRegs_grew arg env e _ hrs).2.1
    cases rs with
    | nil => exact absurd h (by simp)
    | cons c rest =>
      cases rest with
      | cons _ _ => exact absurd h (by simp)
      | nil =>
        dsimp only at h
        cases hcond : condOf left right al ar c ops env labels e₁ with
        | some res =>
          obtain ⟨ops', t', e''⟩ := res
          rw [hcond] at h
          dsimp only at h
          rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨rfl, hgc, t₁, t₂, rs₁, rs₂, rfl, hm₁, hm₂⟩ := condOf_eq hcond
          have hnl : e''.nextLabel = e.nextLabel := by rw [hgc.2.1, hlab]
          refine ⟨⟨?_, by simp⟩, ?_⟩
          · intro l hl
            rw [Term.successors] at hl
            rw [hnl]
            rcases List.mem_cons.mp hl with hl1 | hl1
            · rw [hl1]
              exact (htg _ hm₁).1 t₁ rfl
            · rw [List.mem_singleton] at hl1
              rw [hl1]
              exact (htg _ hm₂).1 t₂ rfl
          · intro q hq
            rw [hgc.1, hblk] at hq
            exact (hbl q hq).mono (Nat.le_of_eq hnl.symm)
        | none =>
          rw [hcond] at h
          dsimp only at h
          rw [Option.bind_eq_some_iff] at h
          obtain ⟨y, hL, h⟩ := h
          obtain ⟨opsL, tL, e₃⟩ := y
          rw [Option.map_eq_some_iff] at h
          obtain ⟨z, hR, hz⟩ := h
          obtain ⟨opsR, tR, e₄⟩ := z
          rw [Prod.mk.injEq, Prod.mk.injEq] at hz
          obtain ⟨rfl, rfl, rfl⟩ := hz
          have hmL : e₁.nextLabel + 1 ≤ e₃.nextLabel := (regionOps_grew left al _ _ _ _ hL).2.1
          have hmR : e₃.nextLabel ≤ e₄.nextLabel := (regionOps_grew right ar _ _ _ _ hR).2.1
          have htgL : TargetsOk results (e₁.nextLabel + 1) labels := htg.mono (by omega)
          have hblL : ∀ p ∈ e₁.blocks, TermOk results (e₁.nextLabel + 1) p.2.term := by
            intro q hq
            rw [hblk] at hq
            exact (hbl q hq).mono (by omega)
          obtain ⟨gL, gLb⟩ := ihL e₁ _ _ _ hL htgL hblL
          have htgR : TargetsOk results e₃.nextLabel labels := htg.mono (by omega)
          have hblR : ∀ p ∈ (e₁.nextLabel, (⟨[], opsL, tL⟩ : Block Nat)) :: e₃.blocks,
              TermOk results e₃.nextLabel p.2.term := by
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact gL
            · exact gLb q hq
          obtain ⟨gR, gRb⟩ := ihR e₁ opsL tL e₃ _ _ _ hR htgR hblR
          refine ⟨⟨?_, by simp⟩, ?_⟩
          · intro l hl
            rw [Term.successors] at hl
            rcases List.mem_cons.mp hl with hl1 | hl1
            · rw [hl1]
              show e₁.nextLabel < e₄.nextLabel + 1
              omega
            · rw [List.mem_singleton] at hl1
              rw [hl1]
              show e₄.nextLabel < e₄.nextLabel + 1
              omega
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact gR.mono (Nat.le_succ _)
            · exact (gRb q hq).mono (Nat.le_succ _)
  | case5 env labels e discr left right al ar hne =>
    intro ops₀ t₀ e' h htg hbl
    rw [regionOps] at h
    exact absurd h (by simp)
    all_goals assumption
  | case6 env labels e entry ws ae abs base blocks inner labels' e₀ ihentry ihblocks =>
    intro ops₀ t₀ e' h htg hbl
    rw [regionOps] at h
    split_ifs at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨y, hentry, h⟩ := h
    obtain ⟨ops, t, e₁⟩ := y
    rw [Option.map_eq_some_iff] at h
    obtain ⟨e₂, hfold, hz⟩ := h
    rw [Prod.mk.injEq, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl, rfl⟩ := hz
    have htg' : TargetsOk results (e.nextLabel + ws.length)
        ((List.finRange ws.length).map
          (fun i => (Target.block (e.nextLabel + i.val), ws.getD i.val 0)) ++ labels) := by
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
        refine ⟨?_, by simp⟩
        intro l hl
        have hi : i.val < ws.length := i.isLt
        have heq : e.nextLabel + i.val = l := Target.block.inj hl
        have hlt : e.nextLabel + i.val < e.nextLabel + ws.length := by omega
        rw [← heq]
        exact hlt
      · exact ⟨fun l hl => Nat.lt_of_lt_of_le ((htg q hq).1 l hl) (by omega), (htg q hq).2⟩
    have hmE : e.nextLabel + ws.length ≤ e₁.nextLabel :=
      (regionOps_grew entry ae _ _ _ _ hentry).2.1
    have hblE : ∀ p ∈ e.blocks, TermOk results (e.nextLabel + ws.length) p.2.term :=
      fun q hq => (hbl q hq).mono (by omega)
    obtain ⟨gE, gEb⟩ := ihentry _ _ _ hentry htg' hblE
    have KEY : (e₁.nextLabel ≤ e₂.nextLabel) ∧
        ((TargetsOk results e₁.nextLabel
            ((List.finRange ws.length).map
              (fun i => (Target.block (e.nextLabel + i.val), ws.getD i.val 0)) ++ labels) ∧
          ∀ p ∈ e₁.blocks, TermOk results e₁.nextLabel p.2.term) →
          (TargetsOk results e₂.nextLabel
            ((List.finRange ws.length).map
              (fun i => (Target.block (e.nextLabel + i.val), ws.getD i.val 0)) ++ labels) ∧
          ∀ p ∈ e₂.blocks, TermOk results e₂.nextLabel p.2.term)) := by
      refine foldl_bind_rel _
        (fun u v => (u.nextLabel ≤ v.nextLabel) ∧
          ((TargetsOk results u.nextLabel
              ((List.finRange ws.length).map
                (fun i => (Target.block (e.nextLabel + i.val), ws.getD i.val 0)) ++ labels) ∧
            ∀ p ∈ u.blocks, TermOk results u.nextLabel p.2.term) →
            (TargetsOk results v.nextLabel
              ((List.finRange ws.length).map
                (fun i => (Target.block (e.nextLabel + i.val), ws.getD i.val 0)) ++ labels) ∧
            ∀ p ∈ v.blocks, TermOk results v.nextLabel p.2.term)))
        (fun _ => ⟨Nat.le_refl _, fun hh => hh⟩)
        (fun _ _ _ hab hbc => ⟨Nat.le_trans hab.1 hbc.1, fun hh => hbc.2 (hab.2 hh)⟩) ?_
        _ e₁ e₂ hfold
      intro i u u' hstep
      rw [Option.map_eq_some_iff] at hstep
      obtain ⟨z, hB, rfl⟩ := hstep
      obtain ⟨opsB, tB, e₃⟩ := z
      have hmB : u.nextLabel ≤ e₃.nextLabel := (regionOps_grew (blocks i) _ _ _ _ _ hB).2.1
      refine ⟨hmB, ?_⟩
      rintro ⟨htu, hbu⟩
      obtain ⟨gB, gBb⟩ := ihblocks i u _ _ _ hB htu hbu
      refine ⟨htu.mono hmB, ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact gB
      · exact gBb q hq
    obtain ⟨hmono, hKEY⟩ := KEY
    obtain ⟨-, hfin⟩ := hKEY ⟨htg'.mono hmE, gEb⟩
    exact ⟨gE.mono hmono, hfin⟩
  | case7 env labels e entry k blocks ws ae abs hne =>
    intro ops₀ t₀ e' h htg hbl
    rw [regionOps] at h
    simp [hne] at h
  | case8 t a env labels e k1 k2 k3 k4 k5 =>
    intro ops₀ t₀ e' h htg hbl
    rw [regionOps] at h
    exact absurd h (by simp)
    all_goals assumption

/-! ## Block arguments -/

/-- Every transfer of a terminator names a block of `B` whose parameter count is
the number of arguments supplied to it. -/
def ArgsOk (B : List (Nat × Block Nat)) (t : Term Nat) : Prop :=
  ∀ tgt as, (tgt, as) ∈ t.args → ∃ b, B.lookup tgt = some b ∧ b.params.length = as.length

/-- Compiling a region only ever adds blocks. -/
theorem regionOps_blocks_suffix {sigs : List Signature} {r : Region (Opcode sigs)} {a : Ann}
    {env : List (List Nat)} {labels : List (Target × Nat)} {e e' : Emit} {ops : List (Op Nat)}
    {t : Term Nat} (h : regionOps r a env labels e = some (ops, t, e')) :
    ∀ p ∈ e.blocks, p ∈ e'.blocks := by
  obtain ⟨-, -, pre, hb, -, -, -, -⟩ := regionOps_grew r a env labels e _ h
  intro p hp
  rw [hb]
  exact List.mem_append_right _ hp

/-- Every step of a fold establishes its own property, and later steps preserve
it: this is how the `cfg` case knows that each of its blocks was filled. -/
theorem foldl_bind_filled {α : Type} (F : α → Emit → Option Emit) (P : α → Emit → Prop)
    (hmono : ∀ i j u v, F i u = some v → P j u → P j v)
    (hF : ∀ i u v, F i u = some v → P i v) :
    ∀ (l : List α) (u v : Emit), l.foldl (fun acc i => acc.bind (F i)) (some u) = some v →
      ∀ i ∈ l, P i v := by
  intro l
  induction l with
  | nil => intro u v _ i hi; exact absurd hi (by simp)
  | cons i rest ih =>
    intro u v h j hj
    rw [List.foldl_cons] at h
    have h' : rest.foldl (fun acc k => acc.bind (F k)) (F i u) = some v := h
    cases hFi : F i u with
    | none =>
      rw [hFi, foldl_bind_none] at h'
      exact absurd h' (by simp)
    | some u₂ =>
      rw [hFi] at h'
      rcases List.mem_cons.mp hj with hjeq | hj
      · rw [hjeq]
        exact foldl_bind_rel F (fun x y => P i x → P i y) (fun _ hh => hh)
          (fun _ _ _ hab hbc hh => hbc (hab hh)) (fun k x y hk => hmono k i x y hk) rest u₂ v h'
          (hF i u u₂ hFi)
      · exact ih u₂ v h' j hj

set_option linter.unusedTactic false in
/-- **Every transfer the compiler emits supplies its target's parameters.** A
branch to a label it was given was checked against that label's recorded width,
and a branch to a block it finished itself goes to a block whose parameters it
allocated from that same width. -/
theorem regionOps_args {sigs : List Signature} (r : Region (Opcode sigs)) (a : Ann)
    (env : List (List Nat)) (labels : List (Target × Nat)) (e : Emit) :
    ∀ (ops : List (Op Nat)) (t : Term Nat) (e' : Emit),
      regionOps r a env labels e = some (ops, t, e') →
      ∀ B : List (Nat × Block Nat),
        (∀ p ∈ e'.blocks, B.lookup p.1 = some p.2) →
        (∀ tgt w, (Target.block tgt, w) ∈ labels →
          ∃ b, B.lookup tgt = some b ∧ b.params.length = w) →
        (∀ p ∈ e.blocks, ArgsOk B p.2.term) →
        ArgsOk B t ∧ ∀ p ∈ e'.blocks, ArgsOk B p.2.term := by
  induction r, a, env, labels, e using regionOps.induct with
  | case1 env labels e ℓ arg =>
    intro ops₀ t₀ e' h B hlook hlab hbl
    rw [regionOps, Option.bind_eq_some_iff] at h
    obtain ⟨p, hp, h⟩ := h
    have hpm : p ∈ labels := List.mem_of_getElem? hp
    obtain ⟨tgt, w⟩ := p
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨y, hrs, h⟩ := h
    obtain ⟨rs, ops, e₁⟩ := y
    have hblk : e₁.blocks = e.blocks := (tmRegs_grew arg env e _ hrs).1
    dsimp only at h
    split_ifs at h with hw
    cases tgt with
    | block tb =>
      rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨?_, by rw [hblk]; exact hbl⟩
      intro u as hu
      rw [Term.args, List.mem_singleton, Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      obtain ⟨b, hb, hblen⟩ := hlab _ w hpm
      refine ⟨b, hb, ?_⟩
      rw [hblen]
      omega
    | ret =>
      rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨fun u as hu => absurd hu (by simp [Term.args]), by rw [hblk]; exact hbl⟩
    | trap =>
      rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨fun u as hu => absurd hu (by simp [Term.args]), by rw [hblk]; exact hbl⟩
  | case2 env labels e v body ab ih =>
    intro ops₀ t₀ e' h B hlook hlab hbl
    rw [regionOps, Option.bind_eq_some_iff] at h
    obtain ⟨y, hrv, h⟩ := h
    obtain ⟨rv, ops, e₁⟩ := y
    have hblk : e₁.blocks = e.blocks := (tmRegs_grew v env e _ hrv).1
    rw [Option.map_eq_some_iff] at h
    obtain ⟨z, hbody, hz⟩ := h
    obtain ⟨ops', t, e₂⟩ := z
    rw [Prod.mk.injEq, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl, rfl⟩ := hz
    exact ih rv e₁ _ _ _ hbody B hlook hlab (by rw [hblk]; exact hbl)
  | case3 env labels e v body ab ih =>
    intro ops₀ t₀ e' h B hlook hlab hbl
    rw [regionOps, Option.bind_eq_some_iff] at h
    obtain ⟨y, hrv, h⟩ := h
    obtain ⟨rv, ops, e₁⟩ := y
    have hblk : e₁.blocks = e.blocks := (tmRegs_grew v env e _ hrv).1
    cases rv with
    | nil => exact absurd h (by simp)
    | cons rr rest =>
      rw [Option.map_eq_some_iff] at h
      obtain ⟨z, hbody, hz⟩ := h
      obtain ⟨ops', t, e₂⟩ := z
      rw [Prod.mk.injEq, Prod.mk.injEq] at hz
      obtain ⟨rfl, rfl, rfl⟩ := hz
      exact ih e₁ rr rest _ _ _ hbody B hlook hlab (by rw [hblk]; exact hbl)
  | case4 env labels e left right al ar arg ihL ihR =>
    intro ops₀ t₀ e' h B hlook hlab hbl
    rw [regionOps, Option.bind_eq_some_iff] at h
    obtain ⟨y, hrs, h⟩ := h
    obtain ⟨rs, ops, e₁⟩ := y
    have hblk : e₁.blocks = e.blocks := (tmRegs_grew arg env e _ hrs).1
    cases rs with
    | nil => exact absurd h (by simp)
    | cons c rest =>
      cases rest with
      | cons _ _ => exact absurd h (by simp)
      | nil =>
        dsimp only at h
        cases hcond : condOf left right al ar c ops env labels e₁ with
        | some res =>
          obtain ⟨ops', t', e''⟩ := res
          rw [hcond] at h
          dsimp only at h
          rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨rfl, hgc, t₁, t₂, rs₁, rs₂, rfl, hm₁, hm₂⟩ := condOf_eq hcond
          refine ⟨?_, ?_⟩
          · intro u as hu
            rw [Term.args] at hu
            rcases List.mem_cons.mp hu with hu | hu
            · rw [Prod.mk.injEq] at hu
              obtain ⟨rfl, rfl⟩ := hu
              exact hlab _ _ hm₁
            · rw [List.mem_singleton, Prod.mk.injEq] at hu
              obtain ⟨rfl, rfl⟩ := hu
              exact hlab _ _ hm₂
          · intro q hq
            rw [hgc.1, hblk] at hq
            exact hbl q hq
        | none =>
          rw [hcond] at h
          dsimp only at h
          rw [Option.bind_eq_some_iff] at h
          obtain ⟨y, hL, h⟩ := h
          obtain ⟨opsL, tL, e₃⟩ := y
          rw [Option.map_eq_some_iff] at h
          obtain ⟨z, hR, hz⟩ := h
          obtain ⟨opsR, tR, e₄⟩ := z
          rw [Prod.mk.injEq, Prod.mk.injEq] at hz
          obtain ⟨rfl, rfl, rfl⟩ := hz
          have hmemL : (e₁.nextLabel, (⟨[], opsL, tL⟩ : Block Nat)) ∈ e₄.blocks :=
            regionOps_blocks_suffix hR _ List.mem_cons_self
          have hsub : ∀ p ∈ e₃.blocks, p ∈ e₄.blocks := fun p hp =>
            regionOps_blocks_suffix hR p (List.mem_cons_of_mem _ hp)
          have hlook₄ : ∀ p ∈ e₄.blocks, B.lookup p.1 = some p.2 := fun p hp =>
            hlook p (List.mem_cons_of_mem _ hp)
          have hlook₃ : ∀ p ∈ e₃.blocks, B.lookup p.1 = some p.2 := fun p hp =>
            hlook₄ p (hsub p hp)
          obtain ⟨gL, gLb⟩ := ihL e₁ _ _ _ hL B hlook₃ hlab (by rw [hblk]; exact hbl)
          have hblR : ∀ p ∈ (e₁.nextLabel, (⟨[], opsL, tL⟩ : Block Nat)) :: e₃.blocks,
              ArgsOk B p.2.term := by
            intro q hq
            rcases List.mem_cons.mp hq with hq | hq
            · rw [hq]
              exact gL
            · exact gLb q hq
          obtain ⟨gR, gRb⟩ := ihR e₁ opsL tL e₃ _ _ _ hR B hlook₄ hlab hblR
          refine ⟨?_, ?_⟩
          · intro u as hu
            rw [Term.args] at hu
            rcases List.mem_cons.mp hu with hu | hu
            · rw [Prod.mk.injEq] at hu
              obtain ⟨rfl, rfl⟩ := hu
              exact ⟨⟨[], opsL, tL⟩, hlook₄ _ hmemL, rfl⟩
            · rw [List.mem_singleton, Prod.mk.injEq] at hu
              obtain ⟨rfl, rfl⟩ := hu
              exact ⟨⟨[], opsR, tR⟩, hlook _ List.mem_cons_self, rfl⟩
          · intro q hq
            rcases List.mem_cons.mp hq with hq | hq
            · rw [hq]
              exact gR
            · exact gRb q hq
  | case5 env labels e discr left right al ar hne =>
    intro ops₀ t₀ e' h B hlook hlab hbl
    rw [regionOps] at h
    exact absurd h (by simp)
    all_goals assumption
  | case6 env labels e entry ws ae abs base blocks inner labels' e₀ ihentry ihblocks =>
    intro ops₀ t₀ e' h B hlook hlab hbl
    rw [regionOps] at h
    split_ifs at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨y, hentry, h⟩ := h
    obtain ⟨ops, t, e₁⟩ := y
    rw [Option.map_eq_some_iff] at h
    obtain ⟨e₂, hfold, hz⟩ := h
    rw [Prod.mk.injEq, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl, rfl⟩ := hz
    have hgrow : ∀ p ∈ e₁.blocks, p ∈ e₂.blocks := by
      refine foldl_bind_rel _ (fun u v => ∀ p ∈ u.blocks, p ∈ v.blocks)
        (fun _ _ hh => hh) (fun _ _ _ hab hbc q hq => hbc q (hab q hq)) ?_ _ e₁ e₂ hfold
      intro i u u' hstep
      rw [Option.map_eq_some_iff] at hstep
      obtain ⟨z, hB, rfl⟩ := hstep
      obtain ⟨opsB, tB, e₃⟩ := z
      intro q hq
      exact List.mem_cons_of_mem _ (regionOps_blocks_suffix hB q hq)
    have hfilled : ∀ i ∈ List.finRange ws.length,
        ∃ blk, (e.nextLabel + i.val, blk) ∈ e₂.blocks ∧ blk.params.length = ws.getD i.val 0 := by
      refine foldl_bind_filled _
        (fun i u => ∃ blk, (e.nextLabel + i.val, blk) ∈ u.blocks ∧
          blk.params.length = ws.getD i.val 0) ?_ ?_ _ e₁ e₂ hfold
      · intro i j u v hstep hP
        rw [Option.map_eq_some_iff] at hstep
        obtain ⟨z, hB, rfl⟩ := hstep
        obtain ⟨opsB, tB, e₃⟩ := z
        obtain ⟨blk, hmem, hlen⟩ := hP
        exact ⟨blk, List.mem_cons_of_mem _ (regionOps_blocks_suffix hB _ hmem), hlen⟩
      · intro i u v hstep
        rw [Option.map_eq_some_iff] at hstep
        obtain ⟨z, hB, rfl⟩ := hstep
        obtain ⟨opsB, tB, e₃⟩ := z
        exact ⟨⟨freshRegs u.nextReg (ws.getD i.val 0), opsB, tB⟩, List.mem_cons_self,
          freshRegs_length _ _⟩
    have hlab' : ∀ tgt w, (Target.block tgt, w) ∈
        (List.finRange ws.length).map
          (fun i => (Target.block (e.nextLabel + i.val), ws.getD i.val 0)) ++ labels →
        ∃ b, B.lookup tgt = some b ∧ b.params.length = w := by
      intro tgt w hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨i, hi, hiq⟩ := List.mem_map.mp hq
        rw [Prod.mk.injEq, Target.block.injEq] at hiq
        obtain ⟨rfl, rfl⟩ := hiq
        obtain ⟨blk, hmem, hlen⟩ := hfilled i hi
        exact ⟨blk, hlook _ hmem, hlen⟩
      · exact hlab tgt w hq
    obtain ⟨gE, gEb⟩ := ihentry _ _ _ hentry B (fun q hq => hlook q (hgrow q hq)) hlab'
      (by rw [show e₀.blocks = e.blocks from rfl]; exact hbl)
    refine ⟨gE, ?_⟩
    have KEY := foldl_bind_rel _
      (fun u v => ((∀ q ∈ v.blocks, B.lookup q.1 = some q.2) →
          (∀ q ∈ u.blocks, B.lookup q.1 = some q.2)) ∧
        ((∀ q ∈ v.blocks, B.lookup q.1 = some q.2) →
          (∀ q ∈ u.blocks, ArgsOk B q.2.term) → ∀ q ∈ v.blocks, ArgsOk B q.2.term))
      (fun _ => ⟨fun hh => hh, fun _ hh => hh⟩)
      (fun _ _ _ hab hbc =>
        ⟨fun hw => hab.1 (hbc.1 hw), fun hw hu => hbc.2 hw (hab.2 (hbc.1 hw) hu)⟩)
      ?step _ e₁ e₂ hfold
    · exact KEY.2 hlook gEb
    · intro i u u' hstep
      rw [Option.map_eq_some_iff] at hstep
      obtain ⟨z, hB, rfl⟩ := hstep
      obtain ⟨opsB, tB, e₃⟩ := z
      have hsub : ∀ q ∈ u.blocks, q ∈ e₃.blocks := fun q hq => regionOps_blocks_suffix hB q hq
      refine ⟨fun hw q hq => hw q (List.mem_cons_of_mem _ (hsub q hq)), ?_⟩
      intro hw hu
      have hlook₃ : ∀ q ∈ e₃.blocks, B.lookup q.1 = some q.2 :=
        fun q hq => hw q (List.mem_cons_of_mem _ hq)
      obtain ⟨gB, gBb⟩ := ihblocks i u _ _ _ hB B hlook₃ hlab' hu
      intro q hq
      rcases List.mem_cons.mp hq with hq | hq
      · rw [hq]
        exact gB
      · exact gBb q hq
  | case7 env labels e entry k blocks ws ae abs hne =>
    intro ops₀ t₀ e' h B hlook hlab hbl
    rw [regionOps] at h
    simp [hne] at h
  | case8 t a env labels e k1 k2 k3 k4 k5 =>
    intro ops₀ t₀ e' h B hlook hlab hbl
    rw [regionOps] at h
    exact absurd h (by simp)
    all_goals assumption

/-! ## Assembling the emitted blocks -/

/-- A looked-up entry is an entry. -/
theorem mem_of_lookup {bs : List (Nat × Block Nat)} {l : Nat} {b : Block Nat}
    (h : bs.lookup l = some b) : (l, b) ∈ bs := by
  induction bs with
  | nil => exact absurd h (by simp)
  | cons q rest ih =>
    obtain ⟨k, v⟩ := q
    rw [List.lookup] at h
    split at h
    · rename_i hk
      obtain rfl := Option.some.inj h
      have hlk : l = k := by simpa using hk
      subst hlk
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- The assembled block list has one entry per allocated label. -/
@[simp] theorem assemble_length (count : Nat) (bs : List (Nat × Block Nat)) :
    (assemble count bs).length = count := by
  simp [assemble]

/-- Every assembled block is either an emitted one or the unreachable trap that
stands in for a label that was never filled. -/
theorem mem_assemble {count : Nat} {bs : List (Nat × Block Nat)} {b : Block Nat}
    (h : b ∈ assemble count bs) :
    b = ⟨[], [], .trap⟩ ∨ ∃ l, (l, b) ∈ bs := by
  rw [assemble, List.mem_map] at h
  obtain ⟨l, -, rfl⟩ := h
  cases hl : bs.lookup l with
  | none => exact Or.inl rfl
  | some b' => exact Or.inr ⟨l, mem_of_lookup hl⟩

/-- A symmetric pairwise relation holds between any two distinct members. -/
theorem pairwise_forall_of_ne {α : Type} {R : α → α → Prop} {l : List α}
    (hsym : ∀ a b, R a b → R b a) (h : l.Pairwise R) :
    ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b := by
  induction l with
  | nil => intro a ha; exact absurd ha (by simp)
  | cons c rest ih =>
    rw [List.pairwise_cons] at h
    intro a ha b hb hab
    rcases List.mem_cons.mp ha with hac | ha2
    · rcases List.mem_cons.mp hb with hbc | hb2
      · exact absurd (hac.trans hbc.symm) hab
      · rw [hac]
        exact h.1 b hb2
    · rcases List.mem_cons.mp hb with hbc | hb2
      · rw [hbc]
        exact hsym _ _ (h.1 a ha2)
      · exact ih h.2 a ha2 b hb2 hab

/-- **Assembling distinctly labelled blocks keeps their definitions distinct.**
Each allocated label contributes the block emitted for it, or the empty trap, so
the assembled list defines exactly what the emitted blocks defined. -/
theorem assemble_nodup_defs {count : Nat} {bs : List (Nat × Block Nat)}
    (hnd : (blocksDefs bs).Nodup) :
    ((assemble count bs).flatMap Block.defs).Nodup := by
  rw [blocksDefs, List.nodup_flatMap] at hnd
  rw [assemble, List.flatMap_map, List.nodup_flatMap]
  refine ⟨?_, List.Pairwise.imp ?_ (List.nodup_range (n := count))⟩
  · intro l _
    cases hl : bs.lookup l with
    | none => simp [Block.defs]
    | some b =>
      have hb := hnd.1 (l, b) (mem_of_lookup hl)
      simpa [hl] using hb
  · intro u v huv x hx0 hx0'
    have hx : x ∈ ((bs.lookup u).getD (⟨[], [], .trap⟩ : Block Nat)).defs := hx0
    have hx' : x ∈ ((bs.lookup v).getD (⟨[], [], .trap⟩ : Block Nat)).defs := hx0'
    clear hx0 hx0'
    cases hu : bs.lookup u with
    | none => rw [hu] at hx; simp [Block.defs] at hx
    | some bu =>
      cases hv : bs.lookup v with
      | none => rw [hv] at hx'; simp [Block.defs] at hx'
      | some bv =>
        rw [hu] at hx
        rw [hv] at hx'
        exact pairwise_forall_of_ne (fun _ _ hpq => List.Disjoint.symm hpq) hnd.2
          (u, bu) (mem_of_lookup hu) (v, bv) (mem_of_lookup hv) (by simp [huv]) hx hx'

/-- The block at an allocated label. -/
theorem assemble_getElem? {count : Nat} {bs : List (Nat × Block Nat)} {l : Nat} (hl : l < count) :
    (assemble count bs)[l]? = some ((bs.lookup l).getD ⟨[], [], .trap⟩) := by
  have hr : (List.range count)[l]? = some l := by simp [hl]
  rw [assemble, List.getElem?_map, hr]
  rfl

/-- A terminator that names only allocated labels and returns the declared
number of values passes the signature check. -/
theorem okIn_of_termOk {results n : Nat} {t : Term Nat} (h : TermOk results n t) :
    t.okIn results n = true := by
  obtain ⟨hs, hr⟩ := h
  cases t with
  | jump tgt as =>
    have h1 := hs tgt (by simp [Term.successors])
    simp [Term.okIn, Term.successors, h1]
  | cond c t₁ a₁ t₂ a₂ =>
    have h1 := hs t₁ (by simp [Term.successors])
    have h2 := hs t₂ (by simp [Term.successors])
    simp [Term.okIn, Term.successors, h1, h2]
  | ret vs =>
    have h1 := hr vs rfl
    simp [Term.okIn, Term.successors, h1]
  | trap => simp [Term.okIn, Term.successors]

/-- A member of a distinctly keyed association list is found by lookup. -/
theorem lookup_of_mem {bs : List (Nat × Block Nat)} (hnd : (bs.map Prod.fst).Nodup)
    {p : Nat × Block Nat} (hp : p ∈ bs) : bs.lookup p.1 = some p.2 := by
  induction bs with
  | nil => exact absurd hp (by simp)
  | cons q rest ih =>
    obtain ⟨k, v⟩ := q
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hp with hp | hp
    · rw [hp]
      simp [List.lookup]
    · have hne : ¬ (p.1 = k) := by
        intro hc
        exact hnd.1 (List.mem_map.mpr ⟨p, hp, hc⟩)
      have hbeq : (p.1 == k) = false := by simp [hne]
      rw [List.lookup, hbeq]
      exact ih hnd.2 hp

/-- Checking every block's calls one at a time decides `CallsMatch`. -/
theorem callsMatch_of_blocks {sigs : List Signature} {fn : Func Nat}
    (h : ∀ b ∈ fn.blocks, OpsCallsMatch sigs b.ops) : fn.CallsMatch sigs := by
  rw [Func.CallsMatch, Func.callsMatch, List.all_eq_true]
  intro b hb
  rw [List.all_eq_true]
  intro o ho
  cases o
  case call f args res =>
    obtain ⟨h1, h2⟩ := h b hb _ ho f args res rfl
    simp [h1, h2]
  all_goals rfl

/-! ## Well-formedness -/

/-- A successfully compiled function has the signature it was asked for. -/
theorem ofLambdaSSA?_sig {sigs : List Signature} {r : Region (Opcode sigs)} {a : Ann}
    {params results : Nat} {fn : Func Nat}
    (h : ofLambdaSSA? sigs r a params results = some fn) : fn.sig = ⟨params, results⟩ := by
  rw [ofLambdaSSA?, Option.map_eq_some_iff] at h
  obtain ⟨⟨ops, t, e⟩, -, rfl⟩ := h
  rfl

/-- The flattened function has the signature it was asked for. -/
theorem ofLambdaSSA_sig {sigs : List Signature} {r : Region (Opcode sigs)} {a : Ann}
    {params results : Nat} :
    (ofLambdaSSA sigs r a params results).sig = ⟨params, results⟩ := by
  rw [ofLambdaSSA]
  cases h : ofLambdaSSA? sigs r a params results with
  | none => rfl
  | some fn => exact ofLambdaSSA?_sig h

/-- The root of a function is compiled by `regionOps` from the initial state,
under a label list that names only block `0` and only at the function's own
parameter width. Which region and which annotation they are depends on whether
the root was the wrapper `cfg`, and nothing downstream needs to know. -/
theorem rootOps_eq {sigs : List Signature} {r : Region (Opcode sigs)} {a : Ann}
    {params results : Nat} {ops : List (Op Nat)} {t : Term Nat} {e : Emit}
    (h : rootOps sigs r a params results = some (ops, t, e)) :
    ∃ (r' : Region (Opcode sigs)) (a' : Ann) (env : List (List Nat))
      (labels : List (Target × Nat)),
      regionOps r' a' env labels { nextReg := params, nextLabel := 1, blocks := [] }
          = some (ops, t, e) ∧
        TargetsOk results 1 labels ∧
        ∀ tgt w, (Target.block tgt, w) ∈ labels → tgt = 0 ∧ w = params := by
  have hbase : TargetsOk results 1 [(Target.ret, results), (Target.trap, 0)] := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨fun l hl => absurd hl (by simp), fun _ => rfl⟩
    · exact ⟨fun l hl => absurd hl (by simp), fun hc => absurd hc (by simp)⟩
  have hbase' : ∀ tgt w, (Target.block tgt, w) ∈ [(Target.ret, results), (Target.trap, 0)] →
      tgt = 0 ∧ w = params := by
    intro tgt w hq
    exact absurd hq (by simp)
  unfold rootOps at h
  split at h
  · split at h
    · rename_i hw
      subst hw
      refine ⟨_, _, _, _, h, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨fun l hl => Nat.lt_one_iff.mpr (Target.block.inj hl).symm,
            fun hc => absurd hc (by simp)⟩
        · exact hbase p hp
      · intro tgt w' hq
        rcases List.mem_cons.mp hq with hq | hq
        · obtain ⟨hq₁, rfl⟩ := Prod.mk.inj hq
          exact ⟨Target.block.inj hq₁, rfl⟩
        · exact hbase' tgt w' hq
    · exact absurd h (by simp)
  · exact ⟨r, a, _, _, h, hbase, hbase'⟩

/-- The shape of a successful compilation: block `0` holds the ops and the
terminator of the region compiled at the root, and the blocks beyond it are the
ones the compilation finished. -/
theorem ofLambdaSSA?_eq {sigs : List Signature} {r : Region (Opcode sigs)} {a : Ann}
    {params results : Nat} {fn : Func Nat}
    (h : ofLambdaSSA? sigs r a params results = some fn) :
    ∃ (r' : Region (Opcode sigs)) (a' : Ann) (env : List (List Nat))
      (labels : List (Target × Nat)) (ops : List (Op Nat)) (t : Term Nat) (e : Emit),
      regionOps r' a' env labels { nextReg := params, nextLabel := 1, blocks := [] }
          = some (ops, t, e) ∧
        TargetsOk results 1 labels ∧
        (∀ tgt w, (Target.block tgt, w) ∈ labels → tgt = 0 ∧ w = params) ∧
      fn = { sig := ⟨params, results⟩, entry := 0,
             blocks := assemble e.nextLabel ((0, ⟨freshRegs 0 params, ops, t⟩) :: e.blocks) } := by
  rw [ofLambdaSSA?, Option.map_eq_some_iff] at h
  obtain ⟨y, hroot, rfl⟩ := h
  obtain ⟨ops, t, e⟩ := y
  obtain ⟨r', a', env, labels, hreg, htg, hlab⟩ := rootOps_eq hroot
  exact ⟨r', a', env, labels, ops, t, e, hreg, htg, hlab, rfl⟩

/-- **No register of the flattened function is assigned twice.** Every
destination is freshly allocated from a counter that only increases, and the
entry block's parameters are the registers below where that counter started. -/
theorem ofLambdaSSA_singleAssignment {sigs : List Signature} {r : Region (Opcode sigs)}
    {a : Ann} {params results : Nat} (h : Compiles sigs r a params results) :
    (ofLambdaSSA sigs r a params results).SingleAssignment := by
  obtain ⟨fn, hfn⟩ := Option.isSome_iff_exists.mp h
  have hofl : ofLambdaSSA sigs r a params results = fn := by rw [ofLambdaSSA, hfn]; rfl
  obtain ⟨r₀, a₀, env₀, labels₀, ops, t, e, hreg, htg₀, hlab₀, rfl⟩ := ofLambdaSSA?_eq hfn
  rw [hofl]
  obtain ⟨hr, hl, pre, hb, hk, hkn, hd, hdn⟩ := regionOps_grew r₀ a₀ _ _ _ _ hreg
  dsimp only at hd
  have hbe : e.blocks = pre := by simpa using hb
  rw [Func.SingleAssignment, Func.allDefs]
  refine assemble_nodup_defs ?_
  rw [blocksDefs_cons, hbe]
  show ((freshRegs 0 params ++ ops.flatMap Op.defs) ++ blocksDefs pre).Nodup
  rw [List.append_assoc]
  refine nodup_append_of_disj (freshRegs_nodup _ _) hdn ?_
  intro rr hrr hrr'
  have h1 := mem_freshRegs.mp hrr
  have h2 := hd rr hrr'
  omega

/-- **The flattened function's signature data is consistent**: the entry block
exists with the declared number of parameters, every terminator names a block of
the function, and every `ret` returns the declared number of values. -/
theorem ofLambdaSSA_wellFormedSig {sigs : List Signature} {r : Region (Opcode sigs)}
    {a : Ann} {params results : Nat} (h : Compiles sigs r a params results) :
    (ofLambdaSSA sigs r a params results).WellFormedSig := by
  obtain ⟨fn, hfn⟩ := Option.isSome_iff_exists.mp h
  have hofl : ofLambdaSSA sigs r a params results = fn := by rw [ofLambdaSSA, hfn]; rfl
  obtain ⟨r₀, a₀, env₀, labels₀, ops, t, e, hreg, htg₀, hlab₀, rfl⟩ := ofLambdaSSA?_eq hfn
  rw [hofl]
  have hmL : 1 ≤ e.nextLabel := (regionOps_grew r₀ a₀ _ _ _ _ hreg).2.1
  obtain ⟨gT, gTb⟩ :=
    regionOps_terms r₀ a₀ _ _ _ _ _ _ hreg htg₀ (fun p hp => absurd hp (by simp))
  have hterm : ∀ b ∈ assemble e.nextLabel
      ((0, (⟨freshRegs 0 params, ops, t⟩ : Block Nat)) :: e.blocks),
      TermOk results e.nextLabel b.term := by
    intro b hb
    rcases mem_assemble hb with rfl | ⟨l, hl⟩
    · exact ⟨by simp [Term.successors], by simp⟩
    · rcases List.mem_cons.mp hl with heq | hl
      · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
        exact gT
      · exact gTb (l, b) hl
  refine ⟨?_, ?_, ?_⟩
  · show 0 < (assemble e.nextLabel
      ((0, (⟨freshRegs 0 params, ops, t⟩ : Block Nat)) :: e.blocks)).length
    rw [assemble_length]
    omega
  · have h0 :
        Func.block?
          { sig := ⟨params, results⟩,
            entry := 0,
            blocks := assemble e.nextLabel
              ((0, (⟨freshRegs 0 params, ops, t⟩ : Block Nat)) :: e.blocks) } 0
          = some ⟨freshRegs 0 params, ops, t⟩ := by
      rw [Func.block?]
      show (assemble e.nextLabel
        ((0, (⟨freshRegs 0 params, ops, t⟩ : Block Nat)) :: e.blocks))[0]? = _
      rw [assemble_getElem? (by omega)]
      simp [List.lookup]
    rw [h0]
    simp
  · rw [List.all_eq_true]
    intro b hb
    exact okIn_of_termOk ((hterm b hb).mono (Nat.le_of_eq (assemble_length _ _).symm))

/-- **Every jump of the flattened function supplies its target's parameters.**
A branch to a lambda-SSA label was checked against that label's recorded width,
and the block for that label has exactly that many parameters. -/
theorem ofLambdaSSA_argsMatch {sigs : List Signature} {r : Region (Opcode sigs)}
    {a : Ann} {params results : Nat} (h : Compiles sigs r a params results) :
    (ofLambdaSSA sigs r a params results).ArgsMatch := by
  obtain ⟨fn, hfn⟩ := Option.isSome_iff_exists.mp h
  have hofl : ofLambdaSSA sigs r a params results = fn := by rw [ofLambdaSSA, hfn]; rfl
  obtain ⟨r₀, a₀, env₀, labels₀, ops, t, e, hreg, htg₀, hlab₀, rfl⟩ := ofLambdaSSA?_eq hfn
  rw [hofl]
  obtain ⟨-, hl, pre, hb, hk, hkn, -, -⟩ := regionOps_grew r₀ a₀ _ _ _ _ hreg
  dsimp only at hl hk hb
  have hbe : e.blocks = pre := by simpa using hb
  have hkeyB : (((0, (⟨freshRegs 0 params, ops, t⟩ : Block Nat)) :: e.blocks).map
      Prod.fst).Nodup := by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, by rw [hbe]; exact hkn⟩
    intro hmem
    rw [hbe] at hmem
    obtain ⟨q, hq, hq0⟩ := List.mem_map.mp hmem
    have := hk q hq
    omega
  have hlook : ∀ p ∈ e.blocks,
      ((0, (⟨freshRegs 0 params, ops, t⟩ : Block Nat)) :: e.blocks).lookup p.1 = some p.2 :=
    fun p hp => lookup_of_mem hkeyB (List.mem_cons_of_mem _ hp)
  have hlabB : ∀ tgt w, (Target.block tgt, w) ∈ labels₀ →
      ∃ b, ((0, (⟨freshRegs 0 params, ops, t⟩ : Block Nat)) :: e.blocks).lookup tgt = some b ∧
        b.params.length = w := by
    intro tgt w hq
    obtain ⟨htgt, hw⟩ := hlab₀ tgt w hq
    subst htgt
    exact ⟨⟨freshRegs 0 params, ops, t⟩, by simp [List.lookup],
      by rw [hw]; exact freshRegs_length _ _⟩
  obtain ⟨gT, gTb⟩ :=
    regionOps_args r₀ a₀ _ _ _ _ _ _ hreg _ hlook hlabB (fun p hp => absurd hp (by simp))
  rw [Func.ArgsMatch, Func.argsMatch, List.all_eq_true]
  intro b hb'
  rw [List.all_eq_true]
  intro ta hta
  have hargs : ArgsOk ((0, (⟨freshRegs 0 params, ops, t⟩ : Block Nat)) :: e.blocks) b.term := by
    rcases mem_assemble hb' with rfl | ⟨l, hl'⟩
    · intro u as hu
      exact absurd hu (by simp [Term.args])
    · rcases List.mem_cons.mp hl' with heq | hl'
      · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
        exact gT
      · exact gTb (l, b) hl'
  obtain ⟨tb, htb, htblen⟩ := hargs ta.1 ta.2 (by rw [Prod.mk.eta]; exact hta)
  have hmemb : (ta.1, tb) ∈ (0, (⟨freshRegs 0 params, ops, t⟩ : Block Nat)) :: e.blocks :=
    mem_of_lookup htb
  have hlt : (ta.1 : Nat) < e.nextLabel := by
    rcases List.mem_cons.mp hmemb with heq | hmemb
    · have h0 : ta.1 = 0 := (Prod.mk.inj heq).1
      rw [h0]
      exact Nat.lt_of_lt_of_le Nat.zero_lt_one hl
    · exact (hk (ta.1, tb) (by rw [← hbe]; exact hmemb)).2
  have hblk : Func.block?
      { sig := ⟨params, results⟩,
        entry := 0,
        blocks := assemble e.nextLabel
          ((0, (⟨freshRegs 0 params, ops, t⟩ : Block Nat)) :: e.blocks) } ta.1 = some tb := by
    rw [Func.block?]
    show (assemble e.nextLabel
      ((0, (⟨freshRegs 0 params, ops, t⟩ : Block Nat)) :: e.blocks))[ta.1]? = _
    rw [assemble_getElem? hlt, htb]
    rfl
  rw [hblk]
  simpa using htblen

/-- **Every call of the flattened function names its callee's declared arity**,
because the opcode's arity is where its argument and result registers came from:
`opOf` checks the arguments against the operand count and allocates the
destinations from the result count. -/
theorem ofLambdaSSA_callsMatch {sigs : List Signature} {r : Region (Opcode sigs)} {a : Ann}
    {params results : Nat} (h : Compiles sigs r a params results) :
    (ofLambdaSSA sigs r a params results).CallsMatch sigs := by
  obtain ⟨fn, hfn⟩ := Option.isSome_iff_exists.mp h
  have hofl : ofLambdaSSA sigs r a params results = fn := by rw [ofLambdaSSA, hfn]; rfl
  obtain ⟨r₀, a₀, env₀, labels₀, ops, t, e, hreg, htg₀, hlab₀, rfl⟩ := ofLambdaSSA?_eq hfn
  rw [hofl]
  obtain ⟨h1, h2⟩ :=
    regionOps_callsMatch r₀ a₀ _ _ _ _ hreg (fun p hp => absurd hp (by simp))
  refine callsMatch_of_blocks ?_
  intro b hb
  rcases mem_assemble hb with rfl | ⟨l, hl⟩
  · exact opsCallsMatch_nil
  · rcases List.mem_cons.mp hl with heq | hl
    · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
      exact h1
    · exact h2 (l, b) hl

/-- **Flattening produces a well-formed SSA function**, given that its uses are
dominated. Three of the four conjuncts of `Func.WellFormed` are proved outright
from `Compiles` — `ofLambdaSSA_wellFormedSig`, `ofLambdaSSA_singleAssignment`
and `ofLambdaSSA_argsMatch` — and the fourth is assumed.

**What is not proved, and why.** `Func.UsesDominated` is not derived here. It is
true, and for the reason the module docstring gives: a label the compiler
allocates is branched to only from the code compiled inside the region that
allocated it, so the block carrying that region's own ops dominates every block
the region emits, and lambda-SSA lexical scope becomes dominance. Turning that
into a proof needs a *global* fact about the finished control-flow graph — that
no block outside a sub-compilation's label interval ever targets a label inside
it — which is a statement about the whole tree of nested compilations rather than
about any one of them, and so does not follow from an induction on `regionOps` of
the shape every other result in this file uses. Rather than weaken `Compiles`
with a dominance post-check, which would make the statement vacuous because the
fallback function of `ofLambdaSSA` is itself well formed, the conjunct is taken
as a hypothesis; it is decidable, so nothing is lost operationally. -/
theorem ofLambdaSSA_wellFormed_of_usesDominated {sigs : List Signature}
    {r : Region (Opcode sigs)} {a : Ann} {params results : Nat}
    (h : Compiles sigs r a params results)
    (hdom : (ofLambdaSSA sigs r a params results).UsesDominated) :
    (ofLambdaSSA sigs r a params results).WellFormed :=
  ⟨ofLambdaSSA_wellFormedSig h, ofLambdaSSA_singleAssignment h, hdom,
    ofLambdaSSA_argsMatch h⟩

/-! ## Semantics preservation -/

/-- The immediate branch to the trap label compiles to the one-block function
that traps at once. -/
theorem ofLambdaSSA_br_trap {sigs : List Signature} (params results : Nat) :
    ofLambdaSSA sigs (.br 1 .unit) .br params results =
      { sig := ⟨params, results⟩, entry := 0,
        blocks := [⟨freshRegs 0 params, [], .trap⟩] } := rfl

/-- A one-block trapping function can only trap, and leaves memory alone. -/
theorem exec_trapBlock {oracle : CallOracle} {sig : Signature} {ps : List Nat}
    {fr : Frame Nat} {m : Memory} {out : Exit}
    (h : Func.Exec oracle { sig := sig, entry := 0, blocks := [⟨ps, [], .trap⟩] } 0 fr m out) :
    out = .trapped m := by
  have hb0 : Func.block? { sig := sig, entry := 0, blocks := [(⟨ps, [], .trap⟩ : Block Nat)] } 0
      = some ⟨ps, [], .trap⟩ := rfl
  cases h with
  | jump hb _ hterm _ _ _ _ =>
    rw [hb0] at hb
    obtain rfl := Option.some.inj hb
    exact absurd hterm (by simp)
  | cond hb _ hterm _ _ _ _ _ =>
    rw [hb0] at hb
    obtain rfl := Option.some.inj hb
    exact absurd hterm (by simp)
  | ret hb _ hterm _ =>
    rw [hb0] at hb
    obtain rfl := Option.some.inj hb
    exact absurd hterm (by simp)
  | trap hb hops _ =>
    rw [hb0] at hb
    obtain rfl := Option.some.inj hb
    cases hops
    rfl

/-- A one-block trapping function does not run forever. -/
theorem not_diverges_trapBlock {oracle : CallOracle} {div : DivOracle} {sig : Signature}
    {ps : List Nat} {fr : Frame Nat} {m : Memory} :
    ¬ Func.Diverges oracle div { sig := sig, entry := 0, blocks := [⟨ps, [], .trap⟩] }
      ⟨0, fr, m⟩ := by
  intro h
  have hb0 : Func.block? { sig := sig, entry := 0, blocks := [(⟨ps, [], .trap⟩ : Block Nat)] } 0
      = some ⟨ps, [], .trap⟩ := rfl
  cases h.unfold with
  | call hb hops _ _ _ =>
    rw [hb0] at hb
    obtain rfl := Option.some.inj hb
    exact absurd hops (by simp)
  | jump hb _ hterm _ _ _ _ =>
    rw [hb0] at hb
    obtain rfl := Option.some.inj hb
    exact absurd hterm (by simp)
  | cond hb _ hterm _ _ _ _ _ =>
    rw [hb0] at hb
    obtain rfl := Option.some.inj hb
    exact absurd hterm (by simp)

/-- **Finite outcomes agree exactly for a region that traps at once.**

**What is proved and what is not.** The intended theorem — that finite outcomes
agree for every region of the fragment, as `toLambdaSSA_eval_iff` says in the
other direction — is not proved here. It needs a correspondence between `Tm.Eval`
on a lambda-SSA environment and `Ops.Exec` on an RTL frame, threaded through the
whole of `regionOps` and through the `cfg` case's `Region.Follow`, and that
development is not carried out in this file. What is proved is the base case in
which the region is the immediate branch to the trap label: both sides then exit
at the trap label with the memory unchanged, for an arbitrary incoming frame. -/
theorem ofLambdaSSA_eval_iff_trap {sigs : List Signature} {oracle : CallOracle}
    {params results : Nat} {fr : Frame Nat} {env : Semantics.Env Word}
    {m m' : Memory} {label : Nat} {value : Value Word} :
    Semantics.Region.Eval (Opcode.step (sigs := sigs) oracle) env (.br 1 .unit) m label value m' ↔
      (label = 0 ∧ ∃ vs, value = packValues vs ∧
          Func.Exec oracle (ofLambdaSSA sigs (.br 1 .unit) .br params results) 0 fr m
            (.returned vs m')) ∨
      (label = 1 ∧ value = .unit ∧
          Func.Exec oracle (ofLambdaSSA sigs (.br 1 .unit) .br params results) 0 fr m
            (.trapped m')) := by
  rw [ofLambdaSSA_br_trap]
  constructor
  · intro hev
    cases hev with
    | br harg =>
      cases harg
      exact Or.inr ⟨rfl, rfl, .trap rfl .nil rfl⟩
  · intro hor
    rcases hor with ⟨-, vs, -, hex⟩ | ⟨rfl, rfl, hex⟩
    · exact absurd (exec_trapBlock hex) (by simp)
    · have hq := exec_trapBlock hex
      injection hq with hm
      subst hm
      exact .br .unit

/-- **Divergence agrees exactly for a region that traps at once**: neither side
diverges.

**What is proved and what is not.** The intended theorem — that divergence agrees
for every region of the fragment — is not proved here, for the same reason as
`ofLambdaSSA_eval_iff_trap`: it rests on the same missing correspondence between
lambda-SSA evaluation and RTL execution, and additionally on a coinductive
argument relating `Semantics.External.Diverges` to `Func.Diverges`. What is
proved is the base case: the immediate branch to the trap label diverges on
neither side. -/
theorem ofLambdaSSA_diverges_iff_trap {sigs : List Signature} {oracle : CallOracle}
    {div : DivOracle} {params results : Nat} {fr : Frame Nat} {env : Semantics.Env Word}
    {m : Memory} :
    Semantics.External.Diverges (Opcode.step (sigs := sigs) oracle) (Opcode.divergent div)
        (.region env (.br 1 .unit) m) ↔
      Func.Diverges oracle div (ofLambdaSSA sigs (.br 1 .unit) .br params results)
        ⟨0, fr, m⟩ := by
  rw [ofLambdaSSA_br_trap]
  constructor
  · intro h
    cases h.unfold with
    | core hc => cases hc
    | br hbr => cases hbr
  · intro h
    exact absurd h not_diverges_trapBlock

/-! ## The swap loop, and `Machine.Lift.erase`

The block-argument eraser `Machine.Lift.erase` erases block arguments to sequential moves
and flattens blocks to nodes, giving `RTL.SSA.Func R → RTL.Func R` and a full
behavioural `iff`. It lands in `RTL.Func R` for the *same* `R`, so it has no
fresh register to route a parallel move through, and its side condition
`Lift.SequentialTransfers` rejects any transfer that writes a block parameter
before a later argument reads it.

Flattening does **not** stay inside that condition. The witness below is the
lambda-SSA swap loop: one `cfg` block of width two whose body branches to itself
with its two components exchanged. It is in the RTL fragment, it flattens to a
well-formed SSA function, and the function it flattens to has a block whose
parameters are `[0, 1]` and which jumps to itself with `[1, 0]` — exactly the
shape `Lift/Examples.lean` already rejects as `swapLoop`.

So the obstruction is neither new nor an artefact of this translation: the
lambda-SSA leg inherits `erase`'s existing restriction rather than adding to it.
It is also narrow, and structurally so. A `cfg` block's parameter is bound at
de Bruijn index zero *inside that block only* — `regionOps` compiles a `cfg`'s
entry under the ambient environment and block `i` under `params i :: env` — and
every parameter register is freshly allocated, so a branch can name the target's
parameters only when it is lexically inside the target block. Every transfer
whose source is the `cfg`'s entry or a sibling block therefore carries arguments
disjoint from its target's parameters and is sequential for free. The failures
are exactly the back edges into an enclosing block, that is, loop headers that
permute their own parameters. Widening `erase` to `R ⊕ Nat` with a scratch
register is a change to `erase`, not to this file. -/

/-- The lambda-SSA swap loop: one `cfg` block of width two that branches to
itself with its two components exchanged. -/
def swapLoopRegion : Region (Opcode []) :=
  .cfg (.br 0 (.var 0)) 1
    (fun _ => .br 0 (.pair (proj 1 (.var 0)) (.pair (proj 0 (.var 0)) .unit)))

/-- The block-parameter widths of `swapLoopRegion`: its single block is two
words wide. -/
def swapLoopAnn : Ann := .cfg [2] .br [.br]

/-- The swap loop is in the RTL fragment. -/
theorem swapLoop_compiles : Compiles [] swapLoopRegion swapLoopAnn 2 2 := by decide

/-- The swap loop flattens to a well-formed SSA function, so nothing in this
development rules it out. -/
theorem swapLoop_wellFormed :
    (ofLambdaSSA [] swapLoopRegion swapLoopAnn 2 2).WellFormed := by decide

/-- **The flattened swap loop permutes a block's parameters along its back
edge.** Its one block has parameters `[0, 1]` and jumps to itself with `[1, 0]`,
so `Lift.sequentialMoves [0, 1] [1, 0]` is false and `Lift.SequentialTransfers`
rejects this function. This is the witness that the image of `ofLambdaSSA` is not
contained in `Machine.Lift.erase`'s domain. -/
theorem swapLoop_blocks :
    (ofLambdaSSA [] swapLoopRegion swapLoopAnn 2 2).blocks =
      [⟨[0, 1], [], .jump 0 [1, 0]⟩] := rfl

/-- A loop whose exit reads the function's argument: if the block's word is
nonzero, go round again with `0`; otherwise return the function's argument
(index `2` under the `case`). -/
def aliasRegion : Region (Opcode []) :=
  .cfg (.br 0 (.var 0)) 1
    (fun _ => .case (.op .test (.var 0)) (.br 0 (.op (.const 0) .unit)) (.br 1 (.var 2)))

/-- The block-parameter widths of `aliasRegion`: one block of one word. -/
def aliasAnn : Ann := .cfg [1] .br [.case .br .br]

/-- **A wrapper body that reads the function's argument is refused.** From
argument `5` the region returns `5`, but compiled under the wrapper shortcut the
back edge would overwrite the argument's register and the function would return
`0`. -/
theorem aliasRegion_not_compiles : ¬ Compiles [] aliasRegion aliasAnn 1 1 := by decide

end Silmaril.Machine.RTL.SSA
