module

public import Silmaril.Compiler.Core.Verified.PrintMem.Defs
public import Silmaril.Compiler.Core.Verified.PrintStateLink.Defs
public import Silmaril.Compiler.Core.Verified.StrLit.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false
/-! # `main` as a block of `int` statements and `printf` calls

`StateGlobals`' statement machine with `printf` statements: `main`'s block creates `int` locals,
then runs `int x;`, `int x = e;`, `x = e;`, `if (c) A else B` (arms of any statements), nested
blocks, `printf("…")` and `printf("…%d…", e)` with `e` an `int` expression over the locals, and
`return e;` (or falls off its end). The file's global definitions are the string literals
(`StrLit.litsOf`), allocated by the startup above the locals.

The machine (`run`) computes, without running anything, the returned closed expression `T` (an
`if` selects between its arms' results at run time, `StmtIf.choose`) and the list of guarded
outputs (`PrintStateLink.GOut`): each `printf` writes its literal characters and the decimal of
its operand's closed expression, under the guard of the arms that lead to it (`armA`, `armB`: a
closed expression that is `1` exactly when the run takes those arms, `0` otherwise). The decimal
of an operand is masked by its guard (`mask`), so a skipped output is defined even when its
operand would overflow.

`run_shows`: from a state that holds the slots (`Inv`), the literals (`LookOk`, `Facts`) and the
pending statements, under a guard that is `1`, Core reaches undefined behaviour or returns `T`'s
value having appended the selected outputs (`ShowsP`); `run_off`: under a guard that is `0`, every
output's guard is a defined `0`. -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PrintState

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open Mem.Concrete (LiveInt nextIntAddress)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons)
open ReturnConst (focusMemory)
open StateExpr (Key Term term values close)
open StateMem (Local Inv Defined defsOf update ptr)
open StateStmt (isLocal isFresh killsRun assignStmt initStmt uninitStmt Keys Overflows
  killsRun_halts bound_pop fails_overflows pure_unit_reaches)
open State (Stmt closeSize maxSize)
open StateGlobals (retStmt ifParts ifParts_size seqParts seqParts_inv seqParts_size isUnit isUnit_inv
  termSize killsEnd killsEnd_reaches Falls zeroDefault main_falls EnvOk inv_withEnv ret_halts)
open IntExpr (spec)
open PrintMem (Lit lits LookOk MemOk Facts ifBinders)
open PrintStateLink (Out GOut On)
open StrMem (Keeps)

/-! ## Guards -/

/-- The guard of arm `A` of `if` (taken when the test `c == 0` is not `1`) under the guard `g`. -/
def armA (g c : IntExpr.Term) : IntExpr.Term :=
  StmtIf.choose g (.lit 0) (StmtIf.choose c (.lit 1) (.lit 0))

/-- The guard of arm `B` of `if` (taken when the test `c == 0` is `1`) under the guard `g`. -/
def armB (g c : IntExpr.Term) : IntExpr.Term :=
  StmtIf.choose g (.lit 0) (StmtIf.choose c (.lit 0) (.lit 1))

/-- The value `t` when the guard `g` is `1`, `0` otherwise. -/
def mask (g t : IntExpr.Term) : IntExpr.Term := StmtIf.choose g (.lit 0) t

/-- A guard that is a defined `0`. -/
def Off (g : IntExpr.Term) : Prop := g.Ok 0 ∧ g.val 0 = 0

/-- A guard that is a defined `1`. -/
def Act (g : IntExpr.Term) : Prop := g.Ok 0 ∧ g.val 0 = 1

theorem isInt_zero : ConvInt.IsInt 0 := by constructor <;> omega
theorem isInt_one : ConvInt.IsInt 1 := by constructor <;> omega

theorem lit_val (c : Int) : (IntExpr.Term.lit c).val 0 = c := rfl
theorem lit_ok {c : Int} (h : ConvInt.IsInt c) : (IntExpr.Term.lit c).Ok 0 := h

theorem off_choose {g : IntExpr.Term} (h : Off g) (t : IntExpr.Term) :
    Off (StmtIf.choose g (.lit 0) t) := by
  have h1 : g.val 0 ≠ 1 := by rw [h.2]; omega
  refine ⟨(StmtIf.choose_ok _ _ _ 0).mpr ⟨h.1, ?_⟩, ?_⟩
  · rw [ite_eq_right h1]; exact lit_ok isInt_zero
  · rw [StmtIf.choose_val, ite_eq_right h1]; rfl

theorem off_armA {g : IntExpr.Term} (h : Off g) (c : IntExpr.Term) : Off (armA g c) := off_choose h _
theorem off_armB {g : IntExpr.Term} (h : Off g) (c : IntExpr.Term) : Off (armB g c) := off_choose h _

theorem mask_off {g : IntExpr.Term} (h : Off g) (t : IntExpr.Term) : (mask g t).Ok 0 :=
  (off_choose h t).1

theorem mask_act {g : IntExpr.Term} (h : Act g) {t : IntExpr.Term} (ht : t.Ok 0) :
    (mask g t).Ok 0 ∧ (mask g t).val 0 = t.val 0 := by
  refine ⟨(StmtIf.choose_ok _ _ _ 0).mpr ⟨h.1, ?_⟩, ?_⟩
  · rw [ite_eq_left h.2]; exact ht
  · rw [mask, StmtIf.choose_val, ite_eq_left h.2]

/-- Under an active guard, the arm the test selects is active and the other one is off. -/
theorem arms_act {g c : IntExpr.Term} (h : Act g) (hc : c.Ok 0) :
    (c.val 0 = 1 → Act (armB g c) ∧ Off (armA g c)) ∧
    (c.val 0 ≠ 1 → Act (armA g c) ∧ Off (armB g c)) := by
  have ok01 : ∀ a b : Int, ConvInt.IsInt a → ConvInt.IsInt b →
      (StmtIf.choose c (.lit a) (.lit b)).Ok 0 := by
    intro a b ha hb
    refine (StmtIf.choose_ok _ _ _ 0).mpr ⟨hc, ?_⟩
    split
    · exact lit_ok hb
    · exact lit_ok ha
  have outer : ∀ a b : Int, ConvInt.IsInt a → ConvInt.IsInt b →
      (StmtIf.choose g (.lit 0) (StmtIf.choose c (.lit a) (.lit b))).Ok 0 ∧
      (StmtIf.choose g (.lit 0) (StmtIf.choose c (.lit a) (.lit b))).val 0 =
        if c.val 0 = 1 then b else a := by
    intro a b ha hb
    refine ⟨(StmtIf.choose_ok _ _ _ 0).mpr ⟨h.1, by rw [ite_eq_left h.2]; exact ok01 a b ha hb⟩, ?_⟩
    rw [StmtIf.choose_val, ite_eq_left h.2, StmtIf.choose_val]
    split <;> rfl
  constructor
  · intro h1
    obtain ⟨oB, vB⟩ := outer 0 1 isInt_zero isInt_one
    obtain ⟨oA, vA⟩ := outer 1 0 isInt_one isInt_zero
    rw [ite_eq_left h1] at vB vA
    exact ⟨⟨oB, vB⟩, ⟨oA, vA⟩⟩
  · intro h1
    obtain ⟨oB, vB⟩ := outer 0 1 isInt_zero isInt_one
    obtain ⟨oA, vA⟩ := outer 1 0 isInt_one isInt_zero
    rw [ite_eq_right h1] at vB vA
    exact ⟨⟨oA, vA⟩, ⟨oB, vB⟩⟩

/-- Off outputs: their guards are defined `0`s and their decimals defined. -/
def AllOff (os : List GOut) : Prop := ∀ p ∈ os, Off p.1 ∧ p.2.Ok

theorem AllOff.ok {os : List GOut} (h : AllOff os) : PrintStateLink.Ok os := by
  intro p hp
  obtain ⟨⟨ok, v⟩, o⟩ := h p hp
  exact ⟨ok, .inl v, o⟩

theorem AllOff.text {os : List GOut} (h : AllOff os) : PrintStateLink.text os = "" := by
  induction os with
  | nil => exact PrintStateLink.text_nil
  | cons p os ih =>
    rw [PrintStateLink.text_cons, ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    have : ¬ On p.1 := by
      have := (h p List.mem_cons_self).1.2
      unfold On; omega
    simp [this]

theorem AllOff.append {o₁ o₂ : List GOut} (h₁ : AllOff o₁) (h₂ : AllOff o₂) : AllOff (o₁ ++ o₂) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact h₁ p hp
  · exact h₂ p hp

theorem ok_append {o₁ o₂ : List GOut} (h₁ : PrintStateLink.Ok o₁) (h₂ : PrintStateLink.Ok o₂) :
    PrintStateLink.Ok (o₁ ++ o₂) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact h₁ p hp
  · exact h₂ p hp

/-- Characters under a guard. -/
def chars (g : IntExpr.Term) (cs : List Char) : List GOut := cs.map fun c => (g, .char c)

theorem chars_off {g : IntExpr.Term} (h : Off g) (cs : List Char) : AllOff (chars g cs) := by
  intro p hp
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hp
  exact ⟨h, trivial⟩

theorem chars_ok {g : IntExpr.Term} (h : Act g) (cs : List Char) : PrintStateLink.Ok (chars g cs) := by
  intro p hp
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hp
  exact ⟨h.1, .inr h.2, trivial⟩

theorem chars_text {g : IntExpr.Term} (h : Act g) (cs : List Char) :
    PrintStateLink.text (chars g cs) = String.ofList cs := by
  induction cs with
  | nil => simp [chars, PrintStateLink.text_nil]
  | cons c cs ih =>
    rw [chars, List.map_cons, PrintStateLink.text_cons, ← chars, ih]
    have : On g := h.2
    simp only [this, ↓reduceIte, Out.text]
    rw [show c :: cs = [c] ++ cs from rfl, String.ofList_append]
    rfl

/-! ## The statements -/

/-- `printf(…);`'s outputs under the guard `g`: the characters of a plain format, or of the format
around the operand's decimal (masked by the guard). -/
def printOuts (file : File Codec.wireModel Unit Unit) (ls : List (Sym × List Int))
    (ds : Key → Option IntExpr.Term) (sz : Key → Nat) (g : IntExpr.Term) : Eff → Option (List GOut)
  | .mk _ (.bound e) =>
    match PrintfIntStmt.printfTerm file ls ∅ e with
    | some (pre, suf, t) =>
      if Defined ds t = true ∧ closeSize sz t ≤ maxSize then
        some (chars g pre ++ (g, .dec (mask g (close (defsOf ds) t))) :: chars g suf)
      else none
    | none => (PrintfStmt.printfLit file ls ∅ e).map fun cs => chars g (PrintfStd.plainText cs).toList
  | _ => none

/-- The test's binders are none of the literals' symbols. -/
def binderFree (lks : List Sym) (e : Eff) : Bool :=
  match ifBinders e with
  | some (c, b) => lks.all fun y => y.key != c.key && y.key != b.key
  | none => false

/-- Which statement `s` is: `StateGlobals.classify` with assignments only (no `x++;`). -/
def classify (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : List Sym) (s : Eff) :
    Option Stmt :=
  match retStmt file ret xs xs s with
  | some t => some (.ret t)
  | none => match assignStmt file s with
    | some (x, t) => some (.assign x t)
    | none => match initStmt file s with
      | some (x, t) => some (.init x t)
      | none => (StateStmt.uninitAny file s).map .uninit

def Shape (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : List Sym) (s : Eff) :
    Stmt → Prop
  | .ret t => retStmt file ret xs xs s = some t
  | .ifRet _ _ => False
  | .assign x t => assignStmt file s = some (x, t)
  | .init x t => initStmt file s = some (x, t)
  | .uninit x => StateStmt.uninitAny file s = some x

theorem classify_spec {file : File Codec.wireModel Unit Unit} {ret : Sym} {xs : List Sym}
    {s : Eff} {st : Stmt} (h : classify file ret xs s = some st) : Shape file ret xs s st := by
  unfold classify at h
  split at h
  next t ht => cases h; exact ht
  next =>
    split at h
    next x t hx => cases h; exact hx
    next =>
      split at h
      next x t hx => cases h; exact hx
      next =>
        cases hu : StateStmt.uninitAny file s with
        | none => simp [hu] at h
        | some x =>
          simp only [hu, Option.map_some, Option.some.injEq] at h
          subst h
          exact hu

/-- The statements of a block with the locals `xs`, the literals `ls` (symbols `lks`), the
definitions `ds` (sizes `sz`), under the guard `g`: the statement `e`, then the pending
statements `todo`. The result is the returned closed expression, the guarded outputs and what is
left of the statement budget `n`. -/
def run (file : File Codec.wireModel Unit Unit) (ret : Sym) (ls : List (Sym × List Int))
    (lks : List Sym) (xs : List Sym) (fall : Bool) :
    (Key → Option IntExpr.Term) → (Key → Nat) → Nat → IntExpr.Term → Eff → List Eff →
      Option (IntExpr.Term × List GOut × Nat)
  | _, _, 0, _, _, _ => none
  | ds, sz, n + 1, g, e, todo =>
    match _hi : ifParts file xs e with
    | some (tc, ea, eb) =>
      if Defined ds tc = true ∧ closeSize sz tc ≤ maxSize ∧ binderFree lks e = true ∧
          termSize (armA g (close (defsOf ds) tc)) ≤ maxSize ∧
          termSize (armB g (close (defsOf ds) tc)) ≤ maxSize then
        match run file ret ls lks xs fall ds sz n (armA g (close (defsOf ds) tc)) ea todo with
        | some (ta, oa, n₁) =>
          match run file ret ls lks xs fall ds sz n₁ (armB g (close (defsOf ds) tc)) eb todo with
          | some (tb, ob, n₂) =>
            if termSize (StmtIf.choose (close (defsOf ds) tc) ta tb) ≤ maxSize then
              some (StmtIf.choose (close (defsOf ds) tc) ta tb, oa ++ ob, n₂)
            else none
          | none => none
        | none => none
      else none
    | none =>
      match classify file ret xs e with
      | some (.ret t) =>
        if Defined ds t = true ∧ closeSize sz t ≤ maxSize then some (close (defsOf ds) t, [], n)
        else none
      | some (.assign x t) =>
        if isLocal xs x = true ∧ Defined ds t = true ∧ closeSize sz t ≤ maxSize then
          match todo with
          | [] => none
          | r :: todo =>
            run file ret ls lks xs fall (update ds x.key (some (close (defsOf ds) t)))
              (fun q => if q = x.key then closeSize sz t else sz q) n g r todo
        else none
      | some (.init x t) =>
        if isLocal xs x = true ∧ Defined ds t = true ∧ closeSize sz t ≤ maxSize then
          match todo with
          | [] => none
          | r :: todo =>
            run file ret ls lks xs fall (update ds x.key (some (close (defsOf ds) t)))
              (fun q => if q = x.key then closeSize sz t else sz q) n g r todo
        else none
      | some (.uninit x) =>
        if isLocal xs x = true then
          match todo with
          | [] => none
          | r :: todo => run file ret ls lks xs fall (update ds x.key none) sz n g r todo
        else none
      | _ =>
        match printOuts file ls ds sz g e with
        | some os =>
          match todo with
          | [] => none
          | r :: todo =>
            match run file ret ls lks xs fall ds sz n g r todo with
            | some (T, os', n') => some (T, os ++ os', n')
            | none => none
        | none =>
          match _hs : seqParts e with
          | some (s, rest) =>
            if fall = true ∧ todo.isEmpty = true ∧ killsEnd file xs e = true then some (.lit 0, [], n)
            else run file ret ls lks xs fall ds sz n g s (rest :: todo)
          | none =>
            if isUnit e = true then
              match todo with
              | [] => if fall = true ∧ xs.isEmpty = true then some (.lit 0, [], n) else none
              | r :: todo => run file ret ls lks xs fall ds sz n g r todo
            else none
termination_by _ _ _ _ e todo => sizeOf e + (todo.map sizeOf).sum
decreasing_by
  all_goals first
    | (have := (ifParts_size _hi).1; omega)
    | (have := (ifParts_size _hi).2; omega)
    | (have := seqParts_size _hs; simp; omega)
    | (cases e; simp)

theorem printOuts_off {file : File Codec.wireModel Unit Unit} {ls : List (Sym × List Int)}
    {ds : Key → Option IntExpr.Term} {sz : Key → Nat} {g : IntExpr.Term} {e : Eff} {os : List GOut}
    (h : printOuts file ls ds sz g e = some os) (hg : Off g) : AllOff os := by
  unfold printOuts at h
  split at h
  · split at h
    · split at h
      · cases h
        refine (chars_off hg _).append ?_
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨hg, mask_off hg _⟩
        · exact chars_off hg _ p hp
      · cases h
    · obtain ⟨cs, -, rfl⟩ := Option.map_eq_some_iff.mp h
      exact chars_off hg _
  · cases h

theorem printOuts_inv {file : File Codec.wireModel Unit Unit} {ls : List (Sym × List Int)}
    {ds : Key → Option IntExpr.Term} {sz : Key → Nat} {g : IntExpr.Term} {e : Eff} {os : List GOut}
    (h : printOuts file ls ds sz g e = some os) :
    ∃ ann e', e = .mk ann (.bound e') ∧
      ((∃ pre suf t, PrintfIntStmt.printfTerm file ls ∅ e' = some (pre, suf, t) ∧
          Defined ds t = true ∧ os = chars g pre ++ (g, .dec (mask g (close (defsOf ds) t))) :: chars g suf) ∨
        ∃ cs, PrintfStmt.printfLit file ls ∅ e' = some cs ∧ os = chars g (PrintfStd.plainText cs).toList) := by
  unfold printOuts at h
  split at h
  · rename_i ann e'
    refine ⟨ann, e', rfl, ?_⟩
    split at h
    · rename_i pre suf t ht
      split at h
      · rename_i hd
        cases h
        exact .inl ⟨pre, suf, t, ht, hd.1, rfl⟩
      · cases h
    · obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .inr ⟨cs, hcs, rfl⟩
  · cases h

/-- **Under a guard that is `0`**, every output's guard is a defined `0`; the budget left only
decreases. -/
theorem run_off_lt {file : File Codec.wireModel Unit Unit} {ret : Sym} {ls : List (Sym × List Int)}
    {lks xs : List Sym} {fall : Bool} (N : Nat) :
    ∀ (ds : Key → Option IntExpr.Term) (sz : Key → Nat) (n : Nat) (g : IntExpr.Term) (e : Eff)
      (todo : List Eff) {T : IntExpr.Term} {os : List GOut} {n' : Nat},
      sizeOf e + (todo.map sizeOf).sum < N →
      run file ret ls lks xs fall ds sz n g e todo = some (T, os, n') →
      n' ≤ n ∧ (Off g → AllOff os) := by
  induction N with
  | zero => intro _ _ _ _ _ _ _ _ _ hN; omega
  | succ N ih =>
  intro ds sz n g e todo T os n' hN h
  have he1 : 0 < sizeOf e := by cases e; simp
  unfold run at h
  split at h
  next => cases h
  next n =>
    split at h
    next tc ea eb hi =>
      split at h
      next hd =>
        split at h
        next ta oa n₁ hA =>
          split at h
          next tb ob n₂ hB =>
            split at h
            next =>
              cases h
              have a := ih _ _ _ _ ea todo (by have := (ifParts_size hi).1; omega) hA
              have b := ih _ _ _ _ eb todo (by have := (ifParts_size hi).2; omega) hB
              exact ⟨by omega, fun hg => (a.2 (off_armA hg _)).append (b.2 (off_armB hg _))⟩
            next => cases h
          next => cases h
        next => cases h
      next => cases h
    next hi =>
      split at h
      next t hc =>
        split at h
        next => cases h; exact ⟨by omega, fun _ p hp => by cases hp⟩
        next => cases h
      next x t hc =>
        split at h
        next =>
          split at h
          next => cases h
          next r todo' =>
            have a := ih _ _ _ _ r todo' (by simp at hN ⊢; omega) h
            exact ⟨by omega, a.2⟩
        next => cases h
      next x t hc =>
        split at h
        next =>
          split at h
          next => cases h
          next r todo' =>
            have a := ih _ _ _ _ r todo' (by simp at hN ⊢; omega) h
            exact ⟨by omega, a.2⟩
        next => cases h
      next x hc =>
        split at h
        next =>
          split at h
          next => cases h
          next r todo' =>
            have a := ih _ _ _ _ r todo' (by simp at hN ⊢; omega) h
            exact ⟨by omega, a.2⟩
        next => cases h
      next =>
        split at h
        next os₀ hp =>
          split at h
          next => cases h
          next r todo' =>
            split at h
            next T' os' n'' hr =>
              cases h
              have a := ih _ _ _ _ r todo' (by simp at hN ⊢; omega) hr
              exact ⟨by omega, fun hg => (printOuts_off hp hg).append (a.2 hg)⟩
            next => cases h
        next hp =>
          split at h
          next s rest hs =>
            split at h
            next => cases h; exact ⟨by omega, fun _ p hp => by cases hp⟩
            next =>
              have a := ih _ _ _ _ s (rest :: todo) (by have := seqParts_size hs; simp at hN ⊢; omega) h
              exact ⟨by omega, a.2⟩
          next hs =>
            split at h
            next =>
              split at h
              next =>
                split at h
                next => cases h; exact ⟨by omega, fun _ p hp => by cases hp⟩
                next => cases h
              next r todo' =>
                have a := ih _ _ _ _ r todo' (by simp at hN ⊢; omega) h
                exact ⟨by omega, a.2⟩
            next => cases h

theorem run_off {file : File Codec.wireModel Unit Unit} {ret : Sym} {ls : List (Sym × List Int)}
    {lks xs : List Sym} {fall : Bool} {ds : Key → Option IntExpr.Term} {sz : Key → Nat} {n : Nat}
    {g : IntExpr.Term} {e : Eff} {todo : List Eff} {T : IntExpr.Term} {os : List GOut} {n' : Nat}
    (h : run file ret ls lks xs fall ds sz n g e todo = some (T, os, n')) :
    n' ≤ n ∧ (Off g → AllOff os) :=
  run_off_lt _ ds sz n g e todo (Nat.lt_succ_self _) h

/-! ## What a run shows -/

variable {file : Program} {labels : Labels}

/-- What a run from a statement shows: `T`'s value returned after appending the selected
outputs to `out`, every output defined, or undefined behaviour. -/
def ShowsP (s : State) (T : IntExpr.Term) (os : List GOut) (out : String) : Prop :=
  (T.Ok 0 ∧ PrintStateLink.Ok os ∧ ∃ m', m'.stdout = out ++ PrintStateLink.text os ∧
    Reaches file labels s ⟨.halt (.defined (spec (T.val 0))), [], m'⟩) ∨
  ∃ s', Reaches file labels s s' ∧ s'.control = .halt IntExpr.overflow

theorem ShowsP.pre {s s' : State} {T : IntExpr.Term} {os : List GOut} {out : String}
    (h : Reaches file labels s s') (o : ShowsP (file := file) (labels := labels) s' T os out) :
    ShowsP (file := file) (labels := labels) s T os out := by
  rcases o with ⟨ok, oks, m', hout, r⟩ | ⟨s'', r, hs⟩
  · exact .inl ⟨ok, oks, m', hout, h.trans r⟩
  · exact .inr ⟨s'', h.trans r, hs⟩

theorem ShowsP.of_shows {s : State} {T : IntExpr.Term} {out : String}
    (o : LocalExpr.Shows (file := file) (labels := labels) s 0 T out) :
    ShowsP (file := file) (labels := labels) s T [] out := by
  rcases o with ⟨ok, m', hout, r⟩ | ub
  · exact .inl ⟨ok, (fun p hp => by cases hp), m', by rw [hout, PrintStateLink.text_nil, String.append_empty], r⟩
  · exact .inr ub

theorem ShowsP.of_overflows {s : State} {T : IntExpr.Term} {os : List GOut} {out : String}
    (o : Overflows (file := file) (labels := labels) s) :
    ShowsP (file := file) (labels := labels) s T os out := .inr o

/-- The outputs of a statement before the outputs of the rest. -/
theorem ShowsP.outputs {s : State} {T : IntExpr.Term} {os os' : List GOut} {out : String}
    (ok : PrintStateLink.Ok os)
    (o : ShowsP (file := file) (labels := labels) s T os' (out ++ PrintStateLink.text os)) :
    ShowsP (file := file) (labels := labels) s T (os ++ os') out := by
  rcases o with ⟨okT, oks, m', hout, r⟩ | ub
  · refine .inl ⟨okT, ok_append ok oks, m', ?_, r⟩
    rw [hout, PrintStateLink.text_append, String.append_assoc]
  · exact .inr ub

/-- The selection shows the arm `B` when the test is `1`, the other arm's outputs being off. -/
theorem ShowsP.chooseB {s : State} {C A B : IntExpr.Term} {oa ob : List GOut} {out : String}
    (okC : C.Ok 0) (h1 : C.val 0 = 1) (off : AllOff oa)
    (o : ShowsP (file := file) (labels := labels) s B ob out) :
    ShowsP (file := file) (labels := labels) s (StmtIf.choose C A B) (oa ++ ob) out := by
  rcases o with ⟨okB, oks, m', hout, r⟩ | ub
  · left
    refine ⟨(StmtIf.choose_ok C A B 0).mpr ⟨okC, by simp [h1, okB]⟩, ok_append off.ok oks, m', ?_, ?_⟩
    · rw [hout, PrintStateLink.text_append, off.text, String.empty_append]
    · rw [StmtIf.choose_val, ite_eq_left h1]; exact r
  · exact .inr ub

/-- The selection shows the arm `A` when the test is not `1`, the other arm's outputs being off. -/
theorem ShowsP.chooseA {s : State} {C A B : IntExpr.Term} {oa ob : List GOut} {out : String}
    (okC : C.Ok 0) (h1 : C.val 0 ≠ 1) (off : AllOff ob)
    (o : ShowsP (file := file) (labels := labels) s A oa out) :
    ShowsP (file := file) (labels := labels) s (StmtIf.choose C A B) (oa ++ ob) out := by
  rcases o with ⟨okA, oks, m', hout, r⟩ | ub
  · left
    refine ⟨(StmtIf.choose_ok C A B 0).mpr ⟨okC, by simp [h1, okA]⟩, ok_append oks off.ok, m', ?_, ?_⟩
    · rw [hout, PrintStateLink.text_append, off.text, String.append_empty]
    · rw [StmtIf.choose_val, ite_eq_right h1]; exact r
  · exact .inr ub

/-! ## The pending statements -/

/-- `StateGlobals.Pending` with an environment predicate `E` for the pending statements. -/
inductive Pending (E : Env → Prop) (fall : Bool) : List Eff → List Frame → Prop
  | base {k : List Frame} : NoBoundary k → (fall = true → Falls (file := file) (labels := labels) k) →
      Pending E fall [] k
  | ann {todo : List Eff} {k : List Frame} (xs : List Access) :
      Pending E fall todo k → Pending E fall todo (.annotations xs :: k)
  | bind {todo : List Eff} {k : List Frame} {env : Env} (pann : List Annot) (ty : BaseType)
      (rest : Eff) : E env → Pending E fall todo k →
      Pending E fall (rest :: todo) (.strongBind (.mk pann (.base (none, ty))) rest env :: k)

theorem Pending.noBoundary {E : Env → Prop} {fall : Bool} {todo : List Eff} {k : List Frame}
    (p : Pending (file := file) (labels := labels) E fall todo k) : NoBoundary k := by
  induction p with
  | base hk _ => exact hk
  | ann _ _ ih => exact noBoundary_cons ih trivial
  | bind _ _ _ _ _ ih => exact noBoundary_cons ih trivial

theorem Pending.resume {E : Env → Prop} {fall : Bool} {todo : List Eff} {k : List Frame}
    (p : Pending (file := file) (labels := labels) E fall todo k) (v : Val) :
    ∀ (fr : Option (List Access)) (m : Mem.Concrete.State) (rest : Eff) (todo' : List Eff),
      todo = rest :: todo' → ∃ env k', E env ∧
        Pending (file := file) (labels := labels) E fall todo' k' ∧
        Reaches file labels ⟨.value v, (fr.map .annotations).toList ++ k, m⟩
          ⟨.effectExpr rest env, k', m⟩ := by
  induction p with
  | base _ _ => intro _ _ _ _ h; cases h
  | ann xs p ih =>
    intro fr m rest todo' h
    cases fr with
    | none => exact ih (some xs) m rest todo' h
    | some a =>
      obtain ⟨env, k', he, p', r⟩ := ih (some (a ++ xs)) m rest todo' h
      exact ⟨env, k', he, p', (Locals.annotations_merge_reaches a xs v _ m).trans r⟩
  | bind pann ty rest₀ he p _ =>
    intro fr m rest todo' h
    cases h
    cases fr with
    | none =>
      exact ⟨_, _, he, p, ReturnConst.wildcard_sequence_reaches file labels pann ty v rest₀ _ _ m⟩
    | some a =>
      exact ⟨_, _, he, .ann a p, Locals.annotations_bind_reaches a pann ty v rest₀ _ _ m⟩

theorem Pending.falls {E : Env → Prop} {fall : Bool} {todo : List Eff} {k : List Frame}
    (p : Pending (file := file) (labels := labels) E fall todo k) (hf : fall = true) :
    todo = [] → Falls (file := file) (labels := labels) k := by
  induction p with
  | base _ f => intro _; exact f hf
  | ann xs p ih =>
    intro h fr m
    cases fr with
    | none => exact ih h (some xs) m
    | some a =>
      obtain ⟨m', out, r⟩ := ih h (some (a ++ xs)) m
      exact ⟨m', out, (Locals.annotations_merge_reaches a xs .unit _ m).trans r⟩
  | bind _ _ _ _ _ _ => intro h; cases h

/-- The environments of the print machine: the slots and the literals. -/
def EOk (L : List Lit) (ls : List Local) (env : Env) : Prop := EnvOk env ls ∧ LookOk L env

theorem memOk_of_litEnv {L : List Lit} {env : Env} {m : Mem.Concrete.State} (hl : LookOk L env)
    (h : StrLit.LitEnv (lits L) env m) : MemOk L m := by
  intro o ho
  obtain ⟨id, addr, look, obj, h0, h1⟩ := h o.sym o.cs (List.mem_map_of_mem ho)
  rw [hl o ho] at look
  cases look
  exact ⟨obj, h0, h1⟩

/-! ## The statements run -/

/-- **The statements under an active guard** show `T`, the selected outputs, or undefined
behaviour. -/
theorem run_shows_lt {ret : Sym} (hret : ReturnLabel labels ret) {xs : List Sym} {fall : Bool}
    (nodup : (xs.map (·.key)).Nodup) {ls : List Local} (hls : Keys ls xs) {L : List Lit} (N : Nat) :
    ∀ (ds : Key → Option IntExpr.Term) (sz : Key → Nat) (n : Nat) (g : IntExpr.Term) (e : Eff)
      (todo : List Eff) {T : IntExpr.Term} {os : List GOut} {n' : Nat},
      sizeOf e + (todo.map sizeOf).sum < N →
      run file ret (lits L) (L.map (·.sym)) xs fall ds sz n g e todo = some (T, os, n') → Act g →
      ∀ (env : Env) (m : Mem.Concrete.State), Inv env m ls ds → LookOk L env →
      Facts L ls (64 + 32 * n) m → ∀ (k : List Frame),
      Pending (file := file) (labels := labels) (EOk L ls) fall todo k →
      ShowsP (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ T os m.stdout := by
  have cl := PrintMem.facts_closed L ls
  induction N with
  | zero => intro _ _ _ _ _ _ _ _ _ hN; omega
  | succ N ih =>
  intro ds sz n g e todo T os n' hN h hg env m inv look facts k p
  have he1 : 0 < sizeOf e := by cases e; simp
  unfold run at h
  split at h
  next => cases h
  next n =>
    have facts' : Facts L ls (64 + 32 * n) m := facts.mono (by push_cast; omega)
    split at h
    next tc ea eb hi =>
      split at h
      next hd =>
        obtain ⟨hdc, -, hfree, -, -⟩ := hd
        split at h
        next ta oa n₁ hA =>
          split at h
          next tb ob n₂ hB =>
            split at h
            next =>
              cases h
              have hbind : ∃ c₀ b₀, ifBinders e = some (c₀, b₀) := by
                unfold binderFree at hfree
                split at hfree
                · exact ⟨_, _, by assumption⟩
                · cases hfree
              obtain ⟨c₀, b₀, hcb⟩ := hbind
              have hfr : ∀ o ∈ L, o.sym.key ≠ c₀.key ∧ o.sym.key ≠ b₀.key := by
                unfold binderFree at hfree
                rw [hcb] at hfree
                intro o ho
                have := List.all_eq_true.mp hfree o.sym (List.mem_map_of_mem ho)
                simpa using this
              rcases PrintMem.if_runs hi inv hls hdc k (cl _) facts' hcb with
                ub | ⟨okc, env', m', out, inv', facts₂, hlook, reach⟩
              · exact .inr ub
              · have look' : LookOk L env' := by
                  intro o ho
                  rw [hlook o.sym (hfr o ho).1 (hfr o ho).2]
                  exact look o ho
                have okC := StateExpr.close_ok (defsOf ds) tc (inv.defs_ok hdc) okc
                have hval := StateExpr.close_val (defsOf ds) tc
                obtain ⟨hB1, hA1⟩ := arms_act hg okC
                by_cases h1 : tc.val (values (defsOf ds)) = 1
                · simp only [h1, ↓reduceIte] at reach
                  have h1' : (close (defsOf ds) tc).val 0 = 1 := by rw [hval]; exact h1
                  obtain ⟨actB, offA⟩ := hB1 h1'
                  have fB : Facts L ls (64 + 32 * n₁) m' :=
                    facts₂.mono (by have := (run_off hA).1; omega)
                  have o := ih ds sz n₁ _ eb todo (by have := (ifParts_size hi).2; omega) hB actB
                    env' m' inv' look' fB k p
                  rw [out] at o
                  exact ShowsP.pre reach (ShowsP.chooseB okC h1' ((run_off hA).2 offA) o)
                · simp only [h1, ↓reduceIte] at reach
                  have h1' : (close (defsOf ds) tc).val 0 ≠ 1 := by rw [hval]; exact h1
                  obtain ⟨actA, offB⟩ := hA1 h1'
                  have o := ih ds sz n _ ea todo (by have := (ifParts_size hi).1; omega) hA actA
                    env' m' inv' look' facts₂ k p
                  rw [out] at o
                  exact ShowsP.pre reach (ShowsP.chooseA okC h1' ((run_off hB).2 offB) o)
            next => cases h
          next => cases h
        next => cases h
      next => cases h
    next hi =>
      split at h
      next t hc =>
        split at h
        next hd =>
          cases h
          exact ShowsP.of_shows (ret_halts hret (classify_spec hc) inv hls hls (fun l hl => hl) nodup
            hd.1 p.noBoundary)
        next => cases h
      next x t hc =>
        split at h
        next hd =>
          split at h
          next => cases h
          next r todo' =>
            obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd.1
            rw [State.update_key hx] at h
            rcases PrintMem.assign_runs (classify_spec hc) inv hl hx hd.2.1 k (cl _) facts' with
              ub | ⟨-, m', out, inv', facts₂, reach⟩
            · exact .inr ub
            · obtain ⟨env', k', ⟨he, hl'⟩, p', r'⟩ := p.resume .unit none m' r todo' rfl
              have o := ih _ _ n g r todo' (by simp at hN ⊢; omega) h hg env' m'
                (inv_withEnv inv' he) hl' facts₂ k' p'
              rw [out] at o
              exact ShowsP.pre (reach.trans r') o
        next => cases h
      next x t hc =>
        split at h
        next hd =>
          split at h
          next => cases h
          next r todo' =>
            obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd.1
            rw [State.update_key hx] at h
            rcases PrintMem.init_runs (classify_spec hc) inv hl hx hd.2.1 k (cl _) facts' with
              ub | ⟨-, m', ys', out, inv', facts₂, reach⟩
            · exact .inr ub
            · obtain ⟨env', k', ⟨he, hl'⟩, p', r'⟩ := p.resume .unit (some ys') m' r todo' rfl
              have o := ih _ _ n g r todo' (by simp at hN ⊢; omega) h hg env' m'
                (inv_withEnv inv' he) hl' facts₂ k' p'
              rw [out] at o
              exact ShowsP.pre (reach.trans r') o
        next => cases h
      next x hc =>
        split at h
        next hd =>
          split at h
          next => cases h
          next r todo' =>
            obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd
            rw [State.update_key hx] at h
            obtain ⟨m', ys', out, inv', facts₂, reach⟩ :=
              PrintMem.uninitAny_runs (classify_spec hc) inv hl hx k (cl _) facts'
            obtain ⟨env', k', ⟨he, hl'⟩, p', r'⟩ := p.resume .unit (some ys') m' r todo' rfl
            have o := ih _ _ n g r todo' (by simp at hN ⊢; omega) h hg env' m'
              (inv_withEnv inv' he) hl' facts₂ k' p'
            rw [out] at o
            exact ShowsP.pre (reach.trans r') o
        next => cases h
      next =>
        split at h
        next os₀ hp =>
          split at h
          next => cases h
          next r todo' =>
            split at h
            next T' os' n'' hr =>
              cases h
              have hlit := PrintMem.litEnv look facts'.lits
              have hroom : 64 ≤ m.lastAddress := by have := facts'.room; omega
              obtain ⟨ann, e', rfl, hcase⟩ := printOuts_inv hp
              rcases hcase with ⟨pre, suf, t, ht, hdt, rfl⟩ | ⟨cs, hcs, rfl⟩
              · by_cases okt : t.Ok (values (defsOf ds))
                · obtain ⟨m', reach, out, inv', earlier', lit', dead', room'⟩ :=
                    PrintfState.printf_reaches ht inv facts'.earlier hdt okt
                      (Fold.EnvSub.empty env) hlit facts'.dead hroom ann k
                  have facts₂ : Facts L ls (64 + 32 * n) m' :=
                    ⟨dead', earlier', memOk_of_litEnv look lit', facts'.above,
                      by have := facts.room; push_cast at this; omega⟩
                  obtain ⟨env', k', ⟨he, hl'⟩, p', r'⟩ := p.resume _ none m' r todo' rfl
                  have o := ih ds sz n g r todo' (by simp at hN ⊢; omega) hr hg env' m'
                    (inv_withEnv inv' he) hl' facts₂ k' p'
                  have hM := mask_act hg (StateExpr.close_ok (defsOf ds) t (inv.defs_ok hdt) okt)
                  have htext : PrintStateLink.text
                      (chars g pre ++ (g, .dec (mask g (close (defsOf ds) t))) :: chars g suf) =
                      PrintfIntStmt.text pre suf (t.val (values (defsOf ds))) := by
                    rw [PrintStateLink.text_append, chars_text hg, PrintStateLink.text_cons,
                      chars_text hg]
                    have hon : On g := hg.2
                    simp only [hon, ↓reduceIte, Out.text, hM.2, StateExpr.close_val,
                      PrintfIntStmt.text]
                  have hok : PrintStateLink.Ok
                      (chars g pre ++ (g, .dec (mask g (close (defsOf ds) t))) :: chars g suf) := by
                    refine ok_append (chars_ok hg pre) ?_
                    intro q hq
                    rcases List.mem_cons.mp hq with rfl | hq
                    · exact ⟨hg.1, .inr hg.2, hM.1⟩
                    · exact chars_ok hg suf q hq
                  rw [out, ← htext] at o
                  exact ShowsP.pre (reach.trans r') (ShowsP.outputs hok o)
                · exact .inr (fails_overflows (PrintfIntStmt.printfTerm_fails ht okt
                    (inv.locs hdt) ann k))
              · obtain ⟨m', reach, out, keep, dead', room'⟩ := PrintfStmt.printfLit_reaches hcs
                  (Fold.EnvSub.empty env) hlit facts'.dead hroom ann k
                have inv' := PrintfState.inv_keeps inv facts'.earlier keep
                have facts₂ : Facts L ls (64 + 32 * n) m' :=
                  facts'.keeps keep dead' (by have := facts.room; push_cast at this; omega)
                obtain ⟨env', k', ⟨he, hl'⟩, p', r'⟩ := p.resume _ none m' r todo' rfl
                have o := ih ds sz n g r todo' (by simp at hN ⊢; omega) hr hg env' m'
                  (inv_withEnv inv' he) hl' facts₂ k' p'
                have htext := chars_text hg (PrintfStd.plainText cs).toList
                rw [String.ofList_toList] at htext
                rw [out, ← htext] at o
                exact ShowsP.pre (reach.trans r') (ShowsP.outputs (chars_ok hg _) o)
            next => cases h
        next hp =>
          split at h
          next s rest hs =>
            obtain ⟨ann, pann, ty, rfl⟩ := seqParts_inv hs
            split at h
            next hk =>
              cases h
              obtain ⟨hf, hnil, hke⟩ := hk
              have hnil' : todo = [] := List.isEmpty_iff.mp hnil
              obtain ⟨m', out, reach⟩ := killsEnd_reaches (file := file) (labels := labels) [] xs ls hls
                nodup hke env k m (fun l hl => inv.env l hl) (fun l hl => by simpa [StateStmt.KLive, StateStmt.isLocal] using inv.live l hl)
                (fun a ha b hb ne => (inv.apart a ha b hb ne).1)
              obtain ⟨m'', out', fin⟩ := p.falls hf hnil' none m'
              exact .inl ⟨show ConvInt.IsInt 0 by constructor <;> omega, (fun p hp => by cases hp), m'',
                by rw [out', out, PrintStateLink.text_nil, String.append_empty], reach.trans fin⟩
            next =>
              exact ShowsP.pre (ReturnConst.sequence_reaches file labels ann _ s rest env k m)
                (ih ds sz n g s (rest :: todo) (by simp at hN ⊢; omega) h hg env m inv look facts' _
                  (.bind pann ty rest ⟨inv.env, look⟩ p))
          next hs =>
            split at h
            next hu =>
              obtain ⟨ann, pann, rfl⟩ := isUnit_inv hu
              split at h
              next =>
                split at h
                next hk =>
                  cases h
                  obtain ⟨hf, hxs⟩ := hk
                  have hxs' : xs = [] := List.isEmpty_iff.mp hxs
                  obtain ⟨m', out, reach⟩ := killsEnd_reaches (file := file) (labels := labels) [] xs ls
                    hls nodup (e := .mk ann (.pure (.mk pann () (.val .unit)))) (by rw [hxs']; rfl)
                    env k m (fun l hl => inv.env l hl) (fun l hl => by simpa [StateStmt.KLive, StateStmt.isLocal] using inv.live l hl)
                    (fun a ha b hb ne => (inv.apart a ha b hb ne).1)
                  obtain ⟨m'', out', fin⟩ := p.falls hf rfl none m'
                  exact .inl ⟨show ConvInt.IsInt 0 by constructor <;> omega, (fun p hp => by cases hp),
                    m'', by rw [out', out, PrintStateLink.text_nil, String.append_empty], reach.trans fin⟩
                next => cases h
              next r todo' =>
                obtain ⟨env', k', ⟨he, hl'⟩, p', reach⟩ :=
                  p.resume .unit none (focusMemory ann m) r todo' rfl
                have o := ih ds sz n g r todo' (by simp at hN ⊢; omega) h hg env' (focusMemory ann m)
                  (inv_withEnv (inv.focus ann) he) hl' ((cl _).focus ann facts') k' p'
                rw [ReturnConst.focusMemory_stdout] at o
                exact ShowsP.pre ((pure_unit_reaches ann pann env k m).trans reach) o
            next => cases h

theorem run_shows {ret : Sym} (hret : ReturnLabel labels ret) {xs : List Sym} {fall : Bool}
    (nodup : (xs.map (·.key)).Nodup) {ls : List Local} (hls : Keys ls xs) {L : List Lit}
    {ds : Key → Option IntExpr.Term} {sz : Key → Nat} {n : Nat} {g : IntExpr.Term} {e : Eff}
    {todo : List Eff} {T : IntExpr.Term} {os : List GOut} {n' : Nat}
    (h : run file ret (lits L) (L.map (·.sym)) xs fall ds sz n g e todo = some (T, os, n'))
    (hg : Act g) (env : Env) (m : Mem.Concrete.State) (inv : Inv env m ls ds) (look : LookOk L env)
    (facts : Facts L ls (64 + 32 * n) m) (k : List Frame)
    (p : Pending (file := file) (labels := labels) (EOk L ls) fall todo k) :
    ShowsP (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ T os m.stdout :=
  run_shows_lt hret nodup hls _ ds sz n g e todo (Nat.lt_succ_self _) h hg env m inv look facts k p

/-! ## The block -/

/-- How many statements a block may visit. -/
def budget : Nat := 65536

/-- The block after the startup's literals `ls` (symbols `lks`): the creations of its `int`
locals, then its statements under the guard `1`. -/
def block (file : File Codec.wireModel Unit Unit) (ret : Sym) (ls : List (Sym × List Int))
    (lks : List Sym) (fall : Bool) : List Sym → Eff → Option (IntExpr.Term × List GOut)
  | xs, .mk _ (.sseq (.mk _ (.base (some x, _))) cr rest) =>
    if Locals.createInt cr = true ∧ isFresh xs x = true ∧ (lks.all fun y => y.key != x.key) = true ∧
        xs.length < 1024 then
      block file ret ls lks fall (xs ++ [x]) rest
    else none
  | xs, e =>
    if (xs.map (·.key)).Nodup then
      (run file ret ls lks xs fall (fun _ => none) (fun _ => 1) budget (.lit 1) e []).map
        fun r => (r.1, r.2.1)
    else none
termination_by _ e => sizeOf e
decreasing_by all_goals (simp_all; omega)

theorem keeps_focus (ann : List Annot) (m : Mem.Concrete.State) : Keeps m (focusMemory ann m) := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
  rw [hl]
  exact (Keeps.refl m).location l

/-- **The block**: creating its `int` locals below the literals keeps them, then its statements
show. -/
theorem block_shows {ret : Sym} (hret : ReturnLabel labels ret) {L : List Lit} {fall : Bool}
    (xs : List Sym) (e : Eff) {T : IntExpr.Term} {os : List GOut}
    (h : block file ret (lits L) (L.map (·.sym)) fall xs e = some (T, os)) (env : Env)
    (m : Mem.Concrete.State) (ls : List Local) (inv : Inv env m ls (fun _ => none))
    (hls : Keys ls xs) (h1024 : xs.length ≤ 1024) (look : LookOk L env) (dead : m.dead = [])
    (earlier : PrintfState.Earlier m ls) (hlits : MemOk L m) (above : PrintMem.Above L ls)
    (room : 2 ^ 47 - 8 * (ls.length : Int) ≤ m.lastAddress) (k : List Frame) (hk : NoBoundary k)
    (falls : fall = true → Falls (file := file) (labels := labels) k) :
    ShowsP (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ T os m.stdout := by
  have hlen : ls.length = xs.length := by
    have := congrArg List.length hls; simpa using this
  unfold block at h
  split at h
  next a p x ty cr rest =>
    split at h
    next hc =>
      obtain ⟨hcr, hfx, hlk, hlt⟩ := hc
      have hna : nextIntAddress m + 4 ≤ m.lastAddress ∧ m.lastAddress - 8 < nextIntAddress m := by
        unfold nextIntAddress; omega
      have hpos : 0 < nextIntAddress m := by
        have : (ls.length : Int) < 1024 := by rw [hlen]; exact_mod_cast hlt
        omega
      let REST := rest
      let K := Frame.strongBind (.mk p (.base (some x, ty))) REST env :: k
      unfold Locals.createInt at hcr
      split at hcr
      next ann l u a1 a2 c1 a3 c2 pref =>
        have create := Locals.create_reaches (file := file) (labels := labels) ann a1 a2 a3 c1 c2 l u
          pref env K m hpos
        let m₁ := Actions.created pref c2 (focusMemory ann m)
        have hC : WrapObj.Created (focusMemory ann m) m₁ := WrapObj.created_int pref c2 _
        have keep : Keeps m m₁ := (keeps_focus ann m).trans (PrintfArg.created_keeps pref c2 _)
        rw [State.focus_nextId] at create
        let nl : Local := ⟨x, m.nextId, nextIntAddress m⟩
        let env₁ := extendEnv [(x, ptr nl)] env
        have bind := ReturnLit.bind_reaches (file := file) (labels := labels) p x ty (ptr nl) REST env k m₁
        have fx : ∀ l ∈ ls, l.sym.key ≠ x.key := hls.fresh hfx
        have ids : ∀ l ∈ ls, l.id < m.nextId := earlier.ids
        have addrs : ∀ l ∈ ls, m.lastAddress ≤ l.addr := earlier.addrs
        have inv₁ : Inv env₁ m₁ (ls ++ [nl]) (fun _ => none) := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro l hl y hy
            rcases List.mem_append.mp hl with hl | hl
            · rw [ConvInt.lookup_one_other (by rw [hy]; exact fx l hl)]
              exact inv.env l hl y hy
            · obtain rfl := List.mem_singleton.mp hl
              exact ConvInt.lookup_one hy
          · intro l hl
            rcases List.mem_append.mp hl with hl | hl
            · refine hC.live (Locals.liveInt_focus ann (inv.live l hl)) ?_
              rw [State.focus_nextId]; exact Int.ne_of_lt (ids l hl)
            · obtain rfl := List.mem_singleton.mp hl
              have := hC.fresh (by rw [State.focus_dead, dead, State.focus_nextId]; simp)
              rwa [Locals.nextIntAddress_focus, State.focus_nextId] at this
          · intro a ha b hb ne
            rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
            · exact inv.apart a ha b hb ne
            · obtain rfl := List.mem_singleton.mp hb
              refine ⟨Int.ne_of_lt (ids a ha), ?_⟩
              have := addrs a ha
              show a.addr + 4 ≤ nextIntAddress m ∨ nextIntAddress m + 4 ≤ a.addr
              omega
            · obtain rfl := List.mem_singleton.mp ha
              refine ⟨Int.ne_of_gt (ids b hb), ?_⟩
              have := addrs b hb
              show nextIntAddress m + 4 ≤ b.addr ∨ b.addr + 4 ≤ nextIntAddress m
              omega
            · obtain rfl := List.mem_singleton.mp ha
              obtain rfl := List.mem_singleton.mp hb
              exact absurd rfl ne
          · intro q d hd
            cases hd
        have hls₁ : Keys (ls ++ [nl]) (xs ++ [x]) := by
          simp only [Keys, List.map_append, List.map_cons, List.map_nil] at hls ⊢
          rw [hls]
        have last₁ : m₁.lastAddress = nextIntAddress m := by
          rw [hC.last, Locals.nextIntAddress_focus]
        have next₁ : m₁.nextId = m.nextId + 1 := by rw [hC.next, State.focus_nextId]
        have look₁ : LookOk L env₁ := by
          refine PrintMem.LookOk.extend look (fun o ho => ?_) _
          have := List.all_eq_true.mp hlk o.sym (List.mem_map_of_mem ho)
          simpa using this
        have earlier₁ : PrintfState.Earlier m₁ (ls ++ [nl]) := by
          refine ⟨?_, ?_⟩
          · intro l hl
            rw [next₁]
            rcases List.mem_append.mp hl with hl | hl
            · have := ids l hl; omega
            · obtain rfl := List.mem_singleton.mp hl
              show m.nextId < m.nextId + 1
              omega
          · intro l hl
            rw [last₁]
            rcases List.mem_append.mp hl with hl | hl
            · have := addrs l hl; omega
            · obtain rfl := List.mem_singleton.mp hl
              exact le_refl _
        have lits₁ : MemOk L m₁ := fun o ho => ⟨(hlits o ho).1.keeps keep, (hlits o ho).2⟩
        have above₁ : PrintMem.Above L (ls ++ [nl]) := by
          intro o ho l hl
          rcases List.mem_append.mp hl with hl | hl
          · exact above o ho l hl
          · obtain rfl := List.mem_singleton.mp hl
            have := (hlits o ho).1.above
            show nextIntAddress m + 4 ≤ o.addr
            omega
        have room₁ : 2 ^ 47 - 8 * ((ls ++ [nl]).length : Int) ≤ m₁.lastAddress := by
          rw [last₁, List.length_append, List.length_singleton]
          push_cast
          omega
        have dead₁ : m₁.dead = [] := by rw [hC.dead, State.focus_dead, dead]
        have o := block_shows hret (xs ++ [x]) rest h env₁ m₁ (ls ++ [nl]) inv₁ hls₁
          (by simp; omega) look₁ dead₁ earlier₁ lits₁ above₁ room₁ k hk falls
        have out : m₁.stdout = m.stdout := by
          rw [hC.stdout]
          obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
          rw [hl]
        rw [out] at o
        exact ShowsP.pre ((ReturnConst.sequence_reaches file labels a _ _ REST env k m).trans
          (create.trans bind)) o
      next => cases hcr
    next => cases h
  next =>
    split at h
    next nodup =>
      cases hr : run file ret (lits L) (L.map (·.sym)) xs fall (fun _ => none) (fun _ => 1) budget
          (.lit 1) e [] with
      | none => simp [hr] at h
      | some r =>
        obtain ⟨T', os', n'⟩ := r
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have facts : Facts L ls (64 + 32 * budget) m := by
          refine ⟨(fun j hj => by rw [dead] at hj; cases hj), earlier, hlits, above, ?_⟩
          have : (ls.length : Int) ≤ 1024 := by rw [hlen]; exact_mod_cast h1024
          simp only [budget]
          push_cast
          omega
        exact run_shows hret nodup hls hr ⟨isInt_one, rfl⟩ env m inv look facts k (.base hk falls)
    next => cases h
termination_by sizeOf e

/-! ## The document -/

/-- The body of `main`: the block, then the return label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) (ls : List (Sym × List Int)) :
    Eff → Option (IntExpr.Term × List GOut)
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, (_, p))] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ StmtIf.labelFree a = true then
        block file ret ls (ls.map (·.1)) (zeroDefault p) [] a
      else none
  | _ => none

/-- The global definitions are string literals, and `main` is a block of `int` statements and
`printf` calls. -/
def recognize (doc : Codec.Document) : Option (IntExpr.Term × List GOut) := do
  let ls ← StrLit.litsOf doc.file
  let s ← doc.file.main
  let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
  recognizeBody doc.file ls body

/-- The whole-document run. -/
theorem recognize_reaches (doc : Codec.Document) {T : IntExpr.Term} {os : List GOut}
    (h : recognize doc = some (T, os)) (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels, initial doc.file enums args = .ok (s, labels) ∧
      ShowsP (file := doc.file) (labels := labels) s T os "" := by
  unfold recognize at h
  cases hls : StrLit.litsOf doc.file with
  | none => simp [hls] at h
  | some ls =>
    simp only [hls, Option.bind_eq_bind, Option.bind_some] at h
    cases main : doc.file.main with
    | none => simp [main] at h
    | some sym =>
      cases decl : doc.file.funs.lookup sym with
      | none => simp [main, decl] at h
      | some entry =>
        cases entry <;> try { simp [main, decl] at h }
        case procedure loc marker ty ps body =>
          cases ps with
          | cons p ps => simp [main, decl] at h
          | nil =>
            have hbody : recognizeBody doc.file ls body = some (T, os) := by simpa [main, decl] using h
            obtain ⟨s, m, env, xs, hinit, hout, hlit, hdead, hlast, hentry⟩ :=
              StrLit.initial_reaches_body doc.file enums args hls main decl
            obtain ⟨L, hL, look, hmem⟩ := PrintMem.of_litEnv ls hlit
            subst hL
            obtain ⟨labels, hlabels⟩ : ∃ labels : Labels, labels = Map.ofList (saves body).reverse :=
              ⟨_, rfl⟩
            rw [← hlabels] at hinit hentry
            unfold recognizeBody at hbody
            split at hbody
            · rename_i ann pann bt0 a sann ret bt r info p0 bann pann' r'
              split at hbody
              · rename_i cond
                obtain ⟨hr, hfree⟩ := cond
                have hret : ReturnLabel labels ret := by
                  rw [hlabels]
                  refine ⟨r, bann, pann', r', hr, ?_⟩
                  simp [saves, StmtIf.labelFree_saves a hfree, Map.ofList]
                let SAVE : EE :=
                  .mk sann (.save (ret, bt) [(r, (info, p0))] (.mk bann (.pure (.mk pann' () (.sym r')))))
                have hsyms : (lits L).map (·.1) = L.map (·.sym) := by simp [lits]
                rw [hsyms] at hbody
                have inv : Inv env m [] (fun _ => none) :=
                  ⟨(fun l hl => by cases hl), (fun l hl => by cases hl), (fun a ha => by cases ha),
                    (fun q d hd => by cases hd)⟩
                have o := block_shows hret [] a hbody env m [] inv rfl (by simp) look hdead
                  ⟨(fun l hl => by cases hl), (fun l hl => by cases hl)⟩ hmem
                  (fun o _ l hl => by cases hl) (by simp; omega)
                  [.strongBind (.mk pann (.base (none, bt0))) SAVE env, .annotations xs]
                  (by simp [NoBoundary, hasBoundary]) (fun hz => main_falls hr hz env xs)
                rw [hout] at o
                exact ⟨s, _, hinit, ShowsP.pre
                  (hentry.trans (ReturnConst.sequence_reaches doc.file _ ann _ a SAVE env _ m)) o⟩
              · cases hbody
            · cases hbody

/-- **Core side.** A recognised document reaches undefined behaviour, or exits with `T`'s value
after writing the selected outputs, every output defined. -/
theorem recognize_sound (doc : Codec.Document) {T : IntExpr.Term} {os : List GOut}
    (h : recognize doc = some (T, os)) (args : List String) :
    Spec.CoreUB doc args ∨ T.Ok 0 ∧ PrintStateLink.Ok os ∧
      Spec.CoreBeh doc args (.exit (T.val 0 % 256).toNat (PrintStateLink.render os)) := by
  obtain ⟨s, labels, hinit, o⟩ :=
    recognize_reaches doc h (Map.ofList (doc.enumBindings.getD [])) args
  rcases o with ⟨ok, oks, m', out, reach⟩ | ⟨s', reach, halt⟩
  · right
    refine ⟨ok, oks, ?_⟩
    have beh := Spec.CoreBeh.exit (k := (T.val 0 % 256).toNat) ⟨s, labels, hinit, reach⟩ rfl rfl
    rw [out, String.empty_append, PrintStateLink.coreBytes_text] at beh
    exact beh
  · left
    exact .inr ⟨s', _, _, ⟨s, labels, hinit, reach⟩, halt⟩

end Silmaril.Compile.Core.Verified.PrintState
