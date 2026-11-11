module

public import Silmaril.Wasm.Auto2.VCBridge.Defs

/-!
# A verified normaliser for the conditions of VC generator 4

Round 2 of `docs/projects/wasm-binaryen-tooling.md`, track vcgen (pass 2). The VC stage of `wasm-check`
(`Silmaril.Wasm.Auto2.VCBridge.vcCheck`) accepted a condition only if it is *syntactically* one of a
contract's proved conditions. This module lets it accept conditions that differ from them by

* **normalisation** (`Fm.norm`, `Tm.norm`): operands of commutative operators (`add`, `mul`,
  `and`, `or`, `xor`, `eq`, `ne`) in a fixed order (`lexLt` on `Tm.code`), `gt`/`ge` turned into
  `lt`/`le` with swapped operands, `select` of equal arms removed, `x = x` is `tt`, `x ≠ x` is
  `ff`, `tt`/`ff` absorbed by the connectives, and an implication whose conclusion is one of the
  conjuncts of its hypothesis is `tt`;
* **renaming of variables** (`Fm.rn`): a proved condition `ψ` stays valid when its `i32`, `i64`
  and memory variables are renamed (memory `0`, the memory at entry, stays itself), so a condition
  that only differs by SSA numbering is covered. The renaming is guessed by pairing the variables
  of the two formulas in order of occurrence (`guess`); the guess is not trusted: the check
  compares the renamed formula with the condition (`DecidableEq Fm`).

`accepts conds φ`: `φ.norm = tt`, or `(ψ.norm).rn σ = φ.norm` for a proved `ψ ∈ conds` and the
guessed `σ`. The definitions are in the namespace `Silmaril.Wasm.Auto2.VCGen` (so that `φ.norm`, `a.rn σ` work). Soundness (`Silmaril.Wasm.Auto2.VCNorm.Thms`): `Fm.den_norm` (normalisation preserves
the meaning), `Fm.den_rn` (renaming is a change of environment), `valid_of_accepts`, and
`allValid_of_coveredN`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCGen

open Silmaril.Wasm

/-! ## A total order on terms (untrusted: only used to choose an order) -/

def sxCode : Signedness → Nat
  | .signed => 0
  | .unsigned => 1

def tyCode : IntType → Nat
  | .i32 => 0
  | .i64 => 1

def psCode : PackSize → Nat
  | .i8 => 0
  | .i16 => 1
  | .i32 => 2
  | .i64 => 3

def unCode : IntUnOp → List Nat
  | .clz => [0]
  | .ctz => [1]
  | .popcnt => [2]
  | .extend sz => [3, psCode sz]

def binCode : IntBinOp → List Nat
  | .add => [0]
  | .sub => [1]
  | .mul => [2]
  | .div s => [3, sxCode s]
  | .rem s => [4, sxCode s]
  | .and => [5]
  | .or => [6]
  | .xor => [7]
  | .shl => [8]
  | .shr s => [9, sxCode s]
  | .rotl => [10]
  | .rotr => [11]

def relCode : IntRelOp → List Nat
  | .eq => [0]
  | .ne => [1]
  | .lt s => [2, sxCode s]
  | .gt s => [3, sxCode s]
  | .le s => [4, sxCode s]
  | .ge s => [5, sxCode s]

def MR.code : MR → List Nat
  | .v k => [0, k]
  | .cur => [1]

/-- A prefix code of a term. -/
def Tm.code : {t : IntType} → Tm t → List Nat
  | _, .var t i => [0, tyCode t, i]
  | _, .loc t j => [1, tyCode t, j]
  | _, .lit t n => [2, tyCode t, n]
  | _, .un op a => 3 :: unCode op ++ a.code
  | _, .bin op a b => 4 :: binCode op ++ a.code ++ b.code
  | _, .rel (t := t) op a b => 5 :: tyCode t :: relCode op ++ a.code ++ b.code
  | _, .eqz (t := t) a => 6 :: tyCode t :: a.code
  | _, .ite c a b => 7 :: c.code ++ a.code ++ b.code
  | _, .wrap a => 8 :: a.code
  | _, .ext sx a => 9 :: sxCode sx :: a.code
  | _, .fn k a => 10 :: k :: a.code
  | _, .fn2 k a b => 11 :: k :: a.code ++ b.code
  | _, .load t n sx m a off => 12 :: tyCode t :: n :: sxCode sx :: MR.code m ++ off :: a.code
  | _, .mfn k m a b => 13 :: k :: MR.code m ++ a.code ++ b.code

/-- Lexicographic order on codes. -/
def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a < b) || (decide (a = b) && lexLt as bs)

/-- `b` comes before `a`. -/
def before {t t' : IntType} (b : Tm t) (a : Tm t') : Bool := lexLt b.code a.code

/-! ## Normalisation -/

/-- Commutative binary operators. -/
def IntBinOp.comm : IntBinOp → Bool
  | .add | .mul | .and | .or | .xor => true
  | _ => false

/-- A binary term with normalised operands. -/
def binN {t : IntType} (op : IntBinOp) (a b : Tm t) : Tm t :=
  if IntBinOp.comm op && before b a then .bin op b a else .bin op a b

/-- A comparison term with normalised operands: `gt`/`ge` become `lt`/`le`, `eq`/`ne` ordered. -/
def relTN {t : IntType} (op : IntRelOp) (a b : Tm t) : Tm .i32 :=
  match op with
  | .gt s => .rel (.lt s) b a
  | .ge s => .rel (.le s) b a
  | .eq => if before b a then .rel .eq b a else .rel .eq a b
  | .ne => if before b a then .rel .ne b a else .rel .ne a b
  | op => .rel op a b

/-- `select` with normalised arms. -/
def iteN {t : IntType} (c : Tm .i32) (a b : Tm t) : Tm t :=
  if a = b then a else .ite c a b

/-! ## Linear arithmetic (round 2, pass 3)

A sum of multiples of atoms plus a constant, modulo `2 ^ width`: `([(c₁, a₁), …], k)` is
`c₁ * a₁ + … + k`. `Tm.lin` reads `add`, `sub`, `mul` by a literal, `shl` by a literal and
literals; any other term is an atom. Atoms are kept in the order `before` and equal atoms are
merged (`linIns`), so sums that differ by associativity, commutativity, `x + x` against `x << 1`
or `2 * x`, or the grouping of constants have the same form (`linBuild`). -/

/-- A linear form: coefficients and atoms, and a constant. -/
abbrev Lin (t : IntType) := List (Nat × Tm t) × Nat

/-- Insert `c * a`, merging it with an equal atom. -/
def linIns {t : IntType} (c : Nat) (a : Tm t) : List (Nat × Tm t) → List (Nat × Tm t)
  | [] => [(c, a)]
  | (d, b) :: r =>
    if a = b then (c + d, b) :: r
    else if before a b then (c, a) :: (d, b) :: r
    else (d, b) :: linIns c a r

/-- The sum of two linear forms. -/
def linAdd {t : IntType} (x y : Lin t) : Lin t :=
  (x.1.foldr (fun p acc => linIns p.1 p.2 acc) y.1, x.2 + y.2)

/-- A linear form times the constant `c`. -/
def linScale {t : IntType} (c : Nat) (x : Lin t) : Lin t :=
  (x.1.map fun p => (c * p.1, p.2), c * x.2)

/-- The value of a literal. -/
def Tm.litOf? {t : IntType} : Tm t → Option Nat
  | .lit _ n => some n
  | _ => none

/-- The linear form of `op a b` from those of `a` and `b`. -/
def linBin {t : IntType} (op : IntBinOp) (a b : Tm t) (la lb : Lin t) : Lin t :=
  match op with
  | .add => linAdd la lb
  | .sub => linAdd la (linScale (2 ^ t.width - 1) lb)
  | .mul => match b.litOf?, a.litOf? with
    | some n, _ => linScale n la
    | none, some n => linScale n lb
    | none, none => ([(1, .bin .mul a b)], 0)
  | .shl => match b.litOf? with
    | some n => linScale (2 ^ (n % 2 ^ t.width % t.width)) la
    | none => ([(1, .bin .shl a b)], 0)
  | op => ([(1, .bin op a b)], 0)

/-- The linear form of a term. -/
def Tm.lin : {t : IntType} → Tm t → Lin t
  | _, .lit _ n => ([], n)
  | _, .bin op a b => linBin op a b a.lin b.lin
  | _, a => ([(1, a)], 0)

/-- A monomial `c * a` (`c` reduced, nonzero). -/
def linMono {t : IntType} (c : Nat) (a : Tm t) : Tm t :=
  if c = 1 then a else .bin .mul a (.lit t c)

/-- The sum `acc + c₁ * a₁ + …` of the monomials with a nonzero coefficient. -/
def linSum {t : IntType} : Tm t → List (Nat × Tm t) → Tm t
  | acc, [] => acc
  | acc, (c, a) :: r =>
    if c % 2 ^ t.width = 0 then linSum acc r
    else linSum (.bin .add acc (linMono (c % 2 ^ t.width) a)) r

/-- The first monomial with a nonzero coefficient, then the others. -/
def linFirst {t : IntType} : List (Nat × Tm t) → Option (Tm t × List (Nat × Tm t))
  | [] => none
  | (c, a) :: r =>
    if c % 2 ^ t.width = 0 then linFirst r else some (linMono (c % 2 ^ t.width) a, r)

/-- The term of a linear form: the monomials in order, then the constant if it is nonzero. -/
def linBuild {t : IntType} (x : Lin t) : Tm t :=
  match linFirst x.1 with
  | none => .lit t (x.2 % 2 ^ t.width)
  | some (e, r) =>
    if x.2 % 2 ^ t.width = 0 then linSum e r else .bin .add (linSum e r) (.lit t (x.2 % 2 ^ t.width))

/-- The operators read as linear arithmetic. -/
def IntBinOp.arith : IntBinOp → Bool
  | .add | .sub | .mul | .shl => true
  | _ => false

/-- A binary term with normalised operands, in linear normal form for `add`, `sub`, `mul` and
`shl`. -/
def arithN {t : IntType} (op : IntBinOp) (a b : Tm t) : Tm t :=
  if IntBinOp.arith op then linBuild (binN op a b).lin else binN op a b

/-- **Normalisation of terms.** -/
def Tm.norm : {t : IntType} → Tm t → Tm t
  | _, .var t i => .var t i
  | _, .loc t j => .loc t j
  | _, .lit t n => .lit t n
  | _, .un op a => .un op a.norm
  | _, .bin op a b => arithN op a.norm b.norm
  | _, .rel op a b => relTN op a.norm b.norm
  | _, .eqz a => .eqz a.norm
  | _, .ite c a b => iteN c.norm a.norm b.norm
  | _, .wrap a => .wrap a.norm
  | _, .ext sx a => .ext sx a.norm
  | _, .fn k a => .fn k a.norm
  | _, .fn2 k a b => .fn2 k a.norm b.norm
  | _, .load t n sx m a off => .load t n sx m a.norm off
  | _, .mfn k m a b => .mfn k m a.norm b.norm

/-- A comparison formula with normalised operands. -/
def relFN {t : IntType} (op : IntRelOp) (a b : Tm t) : Fm :=
  match op with
  | .gt s => .rel (.lt s) b a
  | .ge s => .rel (.le s) b a
  | .eq => if a = b then .tt else if before b a then .rel .eq b a else .rel .eq a b
  | .ne => if a = b then .ff else if before b a then .rel .ne b a else .rel .ne a b
  | op => .rel op a b

def notN (p : Fm) : Fm :=
  if p = .tt then .ff else if p = .ff then .tt else .not p

def andN (p q : Fm) : Fm :=
  if p = .tt then q else if q = .tt then p else if p = .ff ∨ q = .ff then .ff else .and p q

def orN (p q : Fm) : Fm :=
  if p = .ff then q else if q = .ff then p else if p = .tt ∨ q = .tt then .tt else .or p q

/-- The conjuncts of a formula. -/
def Fm.conjs : Fm → List Fm
  | .and p q => p.conjs ++ q.conjs
  | p => [p]

def impN (p q : Fm) : Fm :=
  if q = .tt ∨ p = .ff then .tt else if p = .tt then q else if q ∈ p.conjs then .tt else .imp p q

def meqN (m₁ m₂ : MR) : Fm := if m₁ = m₂ then .tt else .meq m₁ m₂

/-- **Normalisation of formulas.** -/
def Fm.norm : Fm → Fm
  | .tt => .tt
  | .ff => .ff
  | .rel op a b => relFN op a.norm b.norm
  | .nz a => .nz a.norm
  | .not p => notN p.norm
  | .and p q => andN p.norm q.norm
  | .or p q => orN p.norm q.norm
  | .imp p q => impN p.norm q.norm
  | .inb m a n => .inb m a.norm n
  | .pr k m as => .pr k m (as.map Tm.norm)
  | .pr2 k m₁ m₂ as => .pr2 k m₁ m₂ (as.map Tm.norm)
  | .meq m₁ m₂ => meqN m₁ m₂
  | .st k m n a off v => .st k m n a.norm off v.norm

/-! ## Renaming of variables -/

/-- A renaming of the `i32`, `i64` and memory variables, as association lists (unlisted
variables keep their index; memory `0` is always itself). -/
structure Ren where
  r32 : List (Nat × Nat) := []
  r64 : List (Nat × Nat) := []
  rm : List (Nat × Nat) := []

def look (l : List (Nat × Nat)) (i : Nat) : Nat := (l.lookup i).getD i

def Ren.ty (σ : Ren) : IntType → Nat → Nat
  | .i32 => look σ.r32
  | .i64 => look σ.r64

def Ren.mem (σ : Ren) (k : Nat) : Nat := if k = 0 then 0 else look σ.rm k

def MR.rn (σ : Ren) : MR → MR
  | .v k => .v (σ.mem k)
  | .cur => .cur

/-- Rename the variables (and the placeholders, which denote the same environment in a closed
condition) of a term. -/
def Tm.rn (σ : Ren) : {t : IntType} → Tm t → Tm t
  | _, .var t i => .var t (σ.ty t i)
  | _, .loc t j => .loc t (σ.ty t j)
  | _, .lit t n => .lit t n
  | _, .un op a => .un op (a.rn σ)
  | _, .bin op a b => .bin op (a.rn σ) (b.rn σ)
  | _, .rel op a b => .rel op (a.rn σ) (b.rn σ)
  | _, .eqz a => .eqz (a.rn σ)
  | _, .ite c a b => .ite (c.rn σ) (a.rn σ) (b.rn σ)
  | _, .wrap a => .wrap (a.rn σ)
  | _, .ext sx a => .ext sx (a.rn σ)
  | _, .fn k a => .fn k (a.rn σ)
  | _, .fn2 k a b => .fn2 k (a.rn σ) (b.rn σ)
  | _, .load t n sx m a off => .load t n sx (m.rn σ) (a.rn σ) off
  | _, .mfn k m a b => .mfn k (m.rn σ) (a.rn σ) (b.rn σ)

def Fm.rn (σ : Ren) : Fm → Fm
  | .tt => .tt
  | .ff => .ff
  | .rel op a b => .rel op (a.rn σ) (b.rn σ)
  | .nz a => .nz (a.rn σ)
  | .not p => .not (p.rn σ)
  | .and p q => .and (p.rn σ) (q.rn σ)
  | .or p q => .or (p.rn σ) (q.rn σ)
  | .imp p q => .imp (p.rn σ) (q.rn σ)
  | .inb m a n => .inb (m.rn σ) (a.rn σ) n
  | .pr k m as => .pr k (m.rn σ) (as.map (Tm.rn σ))
  | .pr2 k m₁ m₂ as => .pr2 k (m₁.rn σ) (m₂.rn σ) (as.map (Tm.rn σ))
  | .meq m₁ m₂ => .meq (m₁.rn σ) (m₂.rn σ)
  | .st k m n a off v => .st (σ.mem k) (m.rn σ) n (a.rn σ) off (v.rn σ)

/-! ## Guessing a renaming (untrusted) -/

/-- The variables of a memory reference, in order: `(2, k)`. -/
def MR.vars : MR → List (Nat × Nat)
  | .v k => [(2, k)]
  | .cur => []

/-- The variables of a term in order of occurrence: `(0, i)` (`i32`), `(1, i)` (`i64`),
`(2, k)` (memory). -/
def Tm.vars : {t : IntType} → Tm t → List (Nat × Nat)
  | _, .var t i => [(tyCode t, i)]
  | _, .loc t j => [(tyCode t, j)]
  | _, .lit _ _ => []
  | _, .un _ a => a.vars
  | _, .bin _ a b => a.vars ++ b.vars
  | _, .rel _ a b => a.vars ++ b.vars
  | _, .eqz a => a.vars
  | _, .ite c a b => c.vars ++ a.vars ++ b.vars
  | _, .wrap a => a.vars
  | _, .ext _ a => a.vars
  | _, .fn _ a => a.vars
  | _, .fn2 _ a b => a.vars ++ b.vars
  | _, .load _ _ _ m a _ => m.vars ++ a.vars
  | _, .mfn _ m a b => m.vars ++ a.vars ++ b.vars

def Fm.vars : Fm → List (Nat × Nat)
  | .tt => []
  | .ff => []
  | .rel _ a b => a.vars ++ b.vars
  | .nz a => a.vars
  | .not p => p.vars
  | .and p q => p.vars ++ q.vars
  | .or p q => p.vars ++ q.vars
  | .imp p q => p.vars ++ q.vars
  | .inb m a _ => m.vars ++ a.vars
  | .pr _ m as => m.vars ++ (as.map Tm.vars).flatten
  | .pr2 _ m₁ m₂ as => m₁.vars ++ m₂.vars ++ (as.map Tm.vars).flatten
  | .meq m₁ m₂ => m₁.vars ++ m₂.vars
  | .st k m _ a _ v => (2, k) :: m.vars ++ a.vars ++ v.vars

/-- Pair the variables of a pattern and a target of the same shape, in order (first occurrence
wins). -/
def pairUp : List (Nat × Nat) → List (Nat × Nat) → Ren → Ren
  | (k, i) :: ps, (k', j) :: ts, σ =>
    let σ' :=
      if k ≠ k' then σ
      else if k = 0 then (if (σ.r32.lookup i).isSome then σ else { σ with r32 := (i, j) :: σ.r32 })
      else if k = 1 then (if (σ.r64.lookup i).isSome then σ else { σ with r64 := (i, j) :: σ.r64 })
      else (if (σ.rm.lookup i).isSome then σ else { σ with rm := (i, j) :: σ.rm })
    pairUp ps ts σ'
  | _, _, σ => σ

/-- The guessed renaming of `ψ` onto `φ`. -/
def guess (ψ φ : Fm) : Ren := pairUp ψ.vars φ.vars {}

/-! ## The check -/

/-- `φ` is accepted against the proved conditions `conds` (see the module docstring): its normal
form is `tt`, or the renamed normal form of a proved condition. -/
def accepts (conds : List Fm) (φ : Fm) : Bool :=
  let φ' := φ.norm
  decide (φ' = .tt) || conds.any fun ψ =>
    let ψ' := ψ.norm
    decide (ψ'.rn (guess ψ' φ') = φ')

/-- Every condition of `l` is accepted. -/
def coveredN (l conds : List Fm) : Bool := l.all (accepts conds)

end Silmaril.Wasm.Auto2.VCGen
