module

public import Silmaril.Compiler.Core.Verified.ExitCall.Defs
public import Silmaril.Compiler.Core.Verified.FoldSub.Defs
public import Silmaril.Compiler.Core.Verified.StrMem.Defs
public import Silmaril.Compiler.Core.Verified.PrintfFormat.Defs
public import Silmaril.Cerberus.Core.CallReach.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-! # `printf` in std.core: from the call of `printf_proxy` to its result

Cerberus's Core library defines `printf` as the procedure `printf_proxy` (std.core):

```
proc printf_proxy(tmp_ptr: pointer, args: [(ctype, pointer)]) : eff loaded integer :=
  let strong frmt_ptr_ = load('char*', tmp_ptr) in
  case frmt_ptr_ of
  | Specified(frmt_ptr) =>
      let strong xs = pcall(listFromStr, frmt_ptr) in
      let strong ret = pcall(<builtin_printf>, xs, args) in pure(ret)
  | Unspecified(_) => undef
proc listFromStr(str) := let strong rev_xs = pcall(rev_listFromStr_aux, str, []) in pure(reverse(rev_xs))
proc rev_listFromStr_aux(str, acc) :=
  let strong shifted = memop(PtrArrayShift, str, 'char', 0) in
  let strong c_ = load('char', shifted) in
  case c_ of
  | Specified(c) => if c = 0 then pure(acc) else
      let strong shifted = memop(PtrArrayShift, str, 'char', 1) in
      let strong ret = pcall(rev_listFromStr_aux, shifted, c :: acc) in pure(ret)
  | Unspecified(_) => undef
fun reverse(xs) := reverse_aux(xs, [])
fun reverse_aux(xs, acc) := case xs of [] => acc | x :: xs' => reverse_aux(xs', x :: acc)
```

and the builtin `printf` (`Dynamics.requestAux`, `Formatted.printFormat`) formats the list of
characters and appends the text to stdout. `stdOf file proxy` checks that the document's std.core
has exactly these bodies (syntax only: every document carries the same std.core) and returns their
symbols.

`proxy_reaches`: a call of `printf_proxy` on an argument object holding a pointer to the first
character of a string object whose characters contain no conversion (`PlainFormat`) returns the
number of characters and appends them to stdout, keeping every object (`StrMem.Keeps`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PrintfStd

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Fold (WVal WEnv PExp Doc)
open StrMem

abbrev EExp := Expr Codec.wireModel Unit Unit Sym

/-! ## The recogniser of the library -/

/-- The std.core symbols that `printf` runs through. -/
structure Std where
  proxy : Sym
  lfs : Sym
  revAux : Sym
  rev : Sym
  revAux2 : Sym
  /-- The element type of the empty list in `reverse`'s body: the type of its results. -/
  revTy : BaseType

/-- `char*` (any qualifiers and annotations). -/
def isCharPtr : Ctype → Bool
  | .mk _ (.pointer _ (.mk _ (.basic (.integer .char)))) => true
  | _ => false

/-- `char`. -/
def isChar : Ctype → Bool
  | .mk _ (.basic (.integer .char)) => true
  | _ => false

/-- Pairwise distinct symbols. -/
def distinct (xs : List Sym) : Bool := (xs.map MapKey.key).Nodup

/-! The bodies are recognised piece by piece: each piece is one small pattern. -/

/-- `let strong x = a in b`: `x`, `a` and `b`. -/
def sseqOf : EExp → Option (Sym × EExp × EExp)
  | .mk _ (.sseq (.mk _ (.base (some x, _))) a b) => some (x, a, b)
  | _ => none

/-- `pure(x)`. -/
def pureSym : EExp → Option Sym
  | .mk _ (.pure (.mk _ _ (.sym x))) => some x
  | _ => none

/-- `memop(PtrArrayShift, x, char, n)`. -/
def shiftOf : EExp → Option (Sym × Int)
  | .mk _ (.memop .ptrArrayShift [.mk _ _ (.sym x), .mk _ _ (.val (.ctype t)),
      .mk _ _ (.val (.object (.integer n)))]) => if isChar t then some (x, n) else none
  | _ => none

/-- `load(T, x)`, `T` accepted by `ok`. -/
def loadOf (ok : Ctype → Bool) : EExp → Option Sym
  | .mk _ (.action (.mk .pos (.mk _ _ (.load (.mk _ _ (.val (.ctype t))) (.mk _ _ (.sym x)) .na)))) =>
      if ok t then some x else none
  | _ => none

/-- `case x of Specified(c) => yes | Unspecified(_) => _`: `x`, `c` and `yes`. -/
def specCase : EExp → Option (Sym × Sym × EExp)
  | .mk _ (.case_ (.mk _ _ (.sym x)) [(.mk _ (.ctor .specified [.mk _ (.base (some c, _))]), yes),
      (.mk _ (.ctor .unspecified [_]), _)]) => some (x, c, yes)
  | _ => none

/-- `if x = 0 then yes else no`. -/
def ifZero : EExp → Option (Sym × EExp × EExp)
  | .mk _ (.if_ (.mk _ _ (.op .eq (.mk _ _ (.sym x)) (.mk _ _ (.val (.object (.integer 0)))))) yes no) =>
      some (x, yes, no)
  | _ => none

/-- `proc(f, [a, b :: c])`. -/
def procCons : EExp → Option (Sym × Sym × Sym × Sym)
  | .mk _ (.proc _ (.sym f) [.mk _ _ (.sym a), .mk _ _ (.ctor .cons [.mk _ _ (.sym b), .mk _ _ (.sym c)])]) =>
      some (f, a, b, c)
  | _ => none

/-- `proc(f, [a, []])`. -/
def procNil : EExp → Option (Sym × Sym)
  | .mk _ (.proc _ (.sym f) [.mk _ _ (.sym a), .mk _ _ (.ctor (.nil _) [])]) => some (f, a)
  | _ => none

/-- `proc(f, [a])`. -/
def procOne : EExp → Option (Sym × Sym)
  | .mk _ (.proc _ (.sym f) [.mk _ _ (.sym a)]) => some (f, a)
  | _ => none

/-- `proc(<builtin printf>, [a, b])`. -/
def procPrintf : EExp → Option (Sym × Sym)
  | .mk _ (.proc _ (.impl (.builtinFunction "printf")) [.mk _ _ (.sym a), .mk _ _ (.sym b)]) => some (a, b)
  | _ => none

/-- `pure(f(x))`. -/
def pureCall : EExp → Option (Sym × Sym)
  | .mk _ (.pure (.mk _ _ (.call (.sym f) [.mk _ _ (.sym x)]))) => some (f, x)
  | _ => none

/-- `printf_proxy`'s body on its parameters `tp` and `as`: the symbol of `listFromStr`. -/
def proxyCheck (tp as : Sym) (body : EExp) : Option Sym := do
  let (fp_, e1, r1) ← sseqOf body
  let tp' ← loadOf isCharPtr e1
  let (fp_', fp, r2) ← specCase r1
  let (xs, e2, r3) ← sseqOf r2
  let (lfs, fp') ← procOne e2
  let (ret, e3, r4) ← sseqOf r3
  let (xs', as') ← procPrintf e3
  let ret' ← pureSym r4
  if distinct [tp, as, fp_, fp, xs, ret] = true ∧ tp'.key = tp.key ∧ fp_'.key = fp_.key ∧
      fp'.key = fp.key ∧ xs'.key = xs.key ∧ as'.key = as.key ∧ ret'.key = ret.key
  then some lfs else none

/-- `printf_proxy`'s body: the symbol of `listFromStr`. -/
def proxyBody : FunDecl Codec.wireModel Unit Unit → Option Sym
  | .procedure _ _ _ [(tp, _), (as, _)] body => proxyCheck tp as body
  | _ => none

/-- `listFromStr`'s body on its parameter `str`: the symbols of `rev_listFromStr_aux` and
`reverse`. -/
def lfsCheck (str : Sym) (body : EExp) : Option (Sym × Sym) := do
  let (rx, e1, r1) ← sseqOf body
  let (aux, str') ← procNil e1
  let (rev, rx') ← pureCall r1
  if distinct [str, rx] = true ∧ str'.key = str.key ∧ rx'.key = rx.key then some (aux, rev) else none

/-- `listFromStr`'s body: the symbols of `rev_listFromStr_aux` and `reverse`. -/
def lfsBody : FunDecl Codec.wireModel Unit Unit → Option (Sym × Sym)
  | .procedure _ _ _ [(str, _)] body => lfsCheck str body
  | _ => none

/-- `rev_listFromStr_aux`'s body on its parameters `str` and `acc`, recursive on `self`. -/
def revAuxCheck (self str acc : Sym) (body : EExp) : Option Unit := do
  let (sh, e1, r1) ← sseqOf body
  let (str1, z) ← shiftOf e1
  let (c_, e2, r2) ← sseqOf r1
  let sh1 ← loadOf isChar e2
  let (c_1, c, ife) ← specCase r2
  let (c1, yes, no) ← ifZero ife
  let acc1 ← pureSym yes
  let (sh2, e3, r3) ← sseqOf no
  let (str2, one) ← shiftOf e3
  let (ret, e4, r4) ← sseqOf r3
  let (self', sh3, c2, acc2) ← procCons e4
  let ret1 ← pureSym r4
  if z = 0 ∧ one = 1 ∧ distinct [str, acc, sh, c_, c, sh2, ret] = true ∧ self'.key = self.key ∧
      str1.key = str.key ∧ sh1.key = sh.key ∧ c_1.key = c_.key ∧ c1.key = c.key ∧
      acc1.key = acc.key ∧ str2.key = str.key ∧ sh3.key = sh2.key ∧ c2.key = c.key ∧
      acc2.key = acc.key ∧ ret1.key = ret.key
  then some () else none

/-- `rev_listFromStr_aux`'s body, recursive on the symbol `self`. -/
def revAuxBody (self : Sym) : FunDecl Codec.wireModel Unit Unit → Bool
  | .procedure _ _ _ [(str, _), (acc, _)] body => (revAuxCheck self str acc body).isSome
  | _ => false

/-- `reverse`'s body: the symbol of `reverse_aux` and the element type of its empty list. -/
def revBody : FunDecl Codec.wireModel Unit Unit → Option (Sym × BaseType)
  | .function _ [(xs, _)] (.mk _ _ (.call (.sym aux) [.mk _ _ (.sym xs'), .mk _ _ (.ctor (.nil bt) [])])) =>
      if xs'.key = xs.key then some (aux, bt) else none
  | _ => none

/-- `reverse_aux`'s body, recursive on the symbol `self`. -/
def revAux2Body (self : Sym) : FunDecl Codec.wireModel Unit Unit → Bool
  | .function _ [(xs, _), (acc, _)] (.mk _ _ (.case_ (.mk _ _ (.sym xs1))
      [(.mk _ (.ctor (.nil _) []), .mk _ _ (.sym acc1)),
       (.mk _ (.ctor .cons [.mk _ (.base (some x, _)), .mk _ (.base (some xs2, _))]),
        .mk _ _ (.call (.sym self') [.mk _ _ (.sym xs3),
          .mk _ _ (.ctor .cons [.mk _ _ (.sym x1), .mk _ _ (.sym acc2)])]))])) =>
      distinct [xs, acc, x, xs2] && self'.key == self.key && xs1.key == xs.key &&
        acc1.key == acc.key && xs3.key == xs2.key && x1.key == x.key && acc2.key == acc.key
  | _ => false

/-! ### Inversions of the pieces -/

theorem bind_some {α β : Type} {x : Option α} {f : α → Option β} {y : β} (h : (x >>= f) = some y) :
    ∃ a, x = some a ∧ f a = some y := Option.bind_eq_some_iff.mp h

theorem sseqOf_inv {e : EExp} {x : Sym} {a b : EExp} (h : sseqOf e = some (x, a, b)) :
    ∃ ann pa bt, e = .mk ann (.sseq (.mk pa (.base (some x, bt))) a b) := by
  unfold sseqOf at h; split at h
  · cases h; exact ⟨_, _, _, rfl⟩
  · cases h

theorem pureSym_inv {e : EExp} {x : Sym} (h : pureSym e = some x) :
    ∃ ann a u, e = .mk ann (.pure (.mk a u (.sym x))) := by
  unfold pureSym at h; split at h
  · cases h; exact ⟨_, _, _, rfl⟩
  · cases h

theorem shiftOf_inv {e : EExp} {x : Sym} {n : Int} (h : shiftOf e = some (x, n)) :
    ∃ ann a1 u1 a2 u2 t a3 u3, e = .mk ann (.memop .ptrArrayShift [.mk a1 u1 (.sym x),
      .mk a2 u2 (.val (.ctype t)), .mk a3 u3 (.val (.object (.integer n)))]) ∧ isChar t = true := by
  unfold shiftOf at h; split at h
  · split at h
    · rename_i ht; cases h; exact ⟨_, _, _, _, _, _, _, _, rfl, ht⟩
    · cases h
  · cases h

theorem loadOf_inv {ok : Ctype → Bool} {e : EExp} {x : Sym} (h : loadOf ok e = some x) :
    ∃ ann l u a1 u1 t a2 u2, e = .mk ann (.action (.mk .pos (.mk l u (.load (.mk a1 u1 (.val (.ctype t)))
      (.mk a2 u2 (.sym x)) .na)))) ∧ ok t = true := by
  unfold loadOf at h; split at h
  · split at h
    · rename_i ht; cases h; exact ⟨_, _, _, _, _, _, _, _, rfl, ht⟩
    · cases h
  · cases h

theorem specCase_inv {e : EExp} {x c : Sym} {yes : EExp} (h : specCase e = some (x, c, yes)) :
    ∃ ann a u sa pa bc ua up no, e = .mk ann (.case_ (.mk a u (.sym x))
      [(.mk sa (.ctor .specified [.mk pa (.base (some c, bc))]), yes), (.mk ua (.ctor .unspecified [up]), no)]) := by
  unfold specCase at h; split at h
  · cases h; exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

theorem ifZero_inv {e : EExp} {x : Sym} {yes no : EExp} (h : ifZero e = some (x, yes, no)) :
    ∃ ann a u a1 u1 a2 u2, e = .mk ann (.if_ (.mk a u (.op .eq (.mk a1 u1 (.sym x))
      (.mk a2 u2 (.val (.object (.integer 0)))))) yes no) := by
  unfold ifZero at h; split at h
  · cases h; exact ⟨_, _, _, _, _, _, _, rfl⟩
  · cases h

theorem procCons_inv {e : EExp} {f a b c : Sym} (h : procCons e = some (f, a, b, c)) :
    ∃ ann u a1 u1 a2 u2 a3 u3 a4 u4, e = .mk ann (.proc u (.sym f) [.mk a1 u1 (.sym a),
      .mk a2 u2 (.ctor .cons [.mk a3 u3 (.sym b), .mk a4 u4 (.sym c)])]) := by
  unfold procCons at h; split at h
  · cases h; exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

theorem procNil_inv {e : EExp} {f a : Sym} (h : procNil e = some (f, a)) :
    ∃ ann u a1 u1 a2 u2 bt, e = .mk ann (.proc u (.sym f) [.mk a1 u1 (.sym a),
      .mk a2 u2 (.ctor (.nil bt) [])]) := by
  unfold procNil at h; split at h
  · cases h; exact ⟨_, _, _, _, _, _, _, rfl⟩
  · cases h

theorem procOne_inv {e : EExp} {f a : Sym} (h : procOne e = some (f, a)) :
    ∃ ann u a1 u1, e = .mk ann (.proc u (.sym f) [.mk a1 u1 (.sym a)]) := by
  unfold procOne at h; split at h
  · cases h; exact ⟨_, _, _, _, rfl⟩
  · cases h

theorem procPrintf_inv {e : EExp} {a b : Sym} (h : procPrintf e = some (a, b)) :
    ∃ ann u a1 u1 a2 u2, e = .mk ann (.proc u (.impl (.builtinFunction "printf"))
      [.mk a1 u1 (.sym a), .mk a2 u2 (.sym b)]) := by
  unfold procPrintf at h; split at h
  · cases h; exact ⟨_, _, _, _, _, _, rfl⟩
  · cases h

theorem pureCall_inv {e : EExp} {f x : Sym} (h : pureCall e = some (f, x)) :
    ∃ ann a u a1 u1, e = .mk ann (.pure (.mk a u (.call (.sym f) [.mk a1 u1 (.sym x)]))) := by
  unfold pureCall at h; split at h
  · cases h; exact ⟨_, _, _, _, _, rfl⟩
  · cases h

/-- The library procedures of `printf`, from the symbol of `printf_proxy`: each a std.core entry
(not a C function of the document) with the expected body. -/
def stdOf (file : Doc) (proxy : Sym) : Option Std := do
  let lfs ← (file.stdlib.lookup proxy).bind proxyBody
  let (aux, rev) ← (file.stdlib.lookup lfs).bind lfsBody
  let (aux2, bt) ← (file.stdlib.lookup rev).bind revBody
  if [proxy, lfs, aux].all (fun x => (file.funs.lookup x).isNone) &&
      (file.stdlib.lookup aux).any (revAuxBody aux) && (file.stdlib.lookup aux2).any (revAux2Body aux2)
  then some ⟨proxy, lfs, aux, rev, aux2, bt⟩ else none

theorem stdOf_spec {file : Doc} {proxy : Sym} {s : Std} (h : stdOf file proxy = some s) :
    s.proxy = proxy ∧ file.funs.lookup s.proxy = none ∧ file.funs.lookup s.lfs = none ∧
    file.funs.lookup s.revAux = none ∧
    (∃ d, file.stdlib.lookup s.proxy = some d ∧ proxyBody d = some s.lfs) ∧
    (∃ d, file.stdlib.lookup s.lfs = some d ∧ lfsBody d = some (s.revAux, s.rev)) ∧
    (∃ d, file.stdlib.lookup s.rev = some d ∧ revBody d = some (s.revAux2, s.revTy)) ∧
    (∃ d, file.stdlib.lookup s.revAux = some d ∧ revAuxBody s.revAux d = true) ∧
    (∃ d, file.stdlib.lookup s.revAux2 = some d ∧ revAux2Body s.revAux2 d = true) := by
  unfold stdOf at h
  cases h1 : (file.stdlib.lookup proxy).bind proxyBody with
  | none => simp [h1] at h
  | some lfs =>
    cases h2 : (file.stdlib.lookup lfs).bind lfsBody with
    | none => simp [h1, h2] at h
    | some p =>
      obtain ⟨aux, rev⟩ := p
      cases h3 : (file.stdlib.lookup rev).bind revBody with
      | none => simp [h1, h2, h3] at h
      | some q =>
        obtain ⟨aux2, bt⟩ := q
        simp only [h1, h2, h3, Option.bind_eq_bind, Option.bind_some] at h
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true, List.all_cons, List.all_nil, Option.isNone_iff_eq_none,
            Option.any_eq_true] at hc
          obtain ⟨⟨⟨f1, f2, f3, -⟩, d4, l4, b4⟩, d5, l5, b5⟩ := hc
          simp only [Option.bind_eq_some_iff] at h1 h2 h3
          obtain ⟨d1, l1, b1⟩ := h1
          obtain ⟨d2, l2, b2⟩ := h2
          obtain ⟨d3, l3, b3⟩ := h3
          exact ⟨rfl, f1, f2, f3, ⟨d1, l1, b1⟩, ⟨d2, l2, b2⟩, ⟨d3, l3, b3⟩, ⟨d4, l4, b4⟩, ⟨d5, l5, b5⟩⟩
        · cases h

/-! ## Formats without conversions -/

/-- The characters of a format string without conversions: a terminating 0, the others printable
or control ASCII (1 … 127) other than `%`. -/
def PlainFormat (cs : List Int) : Prop :=
  cs.getLast? = some 0 ∧ ∀ c ∈ cs.dropLast, 1 ≤ c ∧ c ≤ 127 ∧ c ≠ 37

instance (cs : List Int) : Decidable (PlainFormat cs) := by unfold PlainFormat; infer_instance

/-- A null-terminated ASCII string. Percent signs are allowed: reading a format
string is independent of interpreting its conversions. -/
def StringFormat (cs : List Int) : Prop :=
  cs.getLast? = some 0 ∧ ∀ c ∈ cs.dropLast, 1 ≤ c ∧ c ≤ 127

theorem PlainFormat.stringFormat {cs : List Int} (h : PlainFormat cs) : StringFormat cs :=
  ⟨h.1, fun c hc => ⟨(h.2 c hc).1, (h.2 c hc).2.1⟩⟩

/-- The text that `printf` prints for such a format. -/
def plainText (cs : List Int) : String := String.ofList (cs.dropLast.map fun c => Char.ofNat c.toNat)

/-- The characters as Core values, the first one last (`rev_listFromStr_aux`'s accumulator). -/
def revChars (cs : List Int) : List Val := (cs.map fun c => .object (.integer c)).reverse

/-! ## The runs -/

section Runs
variable {file : Program} {labels : Labels}

/-- **The builtin `printf`** on a format without conversions prints it and returns its length. -/
theorem builtin_printf_plain {cs : List Int} (hcs : PlainFormat cs) (bt bt' : BaseType)
    (k : List Frame) (m : Mem.Concrete.State) :
    ReturnConst.Reaches file labels
      ⟨.apply (.builtin "printf") [.list bt (cs.dropLast.map fun c => .object (.integer c)), .list bt' []], k, m⟩
      ⟨.value (.loaded (.specified (.integer (plainText cs).length))), k,
        {m with stdout := m.stdout ++ plainText cs}⟩ := by
  have hc : ∀ c ∈ cs.dropLast, 0 ≤ c ∧ c < 128 ∧ c ≠ 37 := by
    intro c hc
    obtain ⟨h1, h2, h3⟩ := hcs.2 c hc
    exact ⟨by omega, by omega, h3⟩
  exact PrintfFormat.builtin_plain cs.dropLast hc bt bt' k m

/-- A pure call of a symbol looks its function up by key. -/
theorem functionBody_key {a b : Sym} (h : a.key = b.key) (vs : List Val) :
    functionBody file (.sym a) vs = functionBody file (.sym b) vs := by
  simp only [functionBody, ReturnLit.lookup_key (m := file.stdlib) h,
    ReturnLit.lookup_key (m := file.funs) h]

theorem distinct_nodup {xs : List Sym} (h : distinct xs = true) : (xs.map MapKey.key).Nodup := by
  simpa [distinct] using h

/-- **`reverse_aux`** on `vs` and `acc`: `vs` reversed onto `acc`, with `acc`'s element type. -/
theorem revAux2_eval {aux2 : Sym} {d : FunDecl Codec.wireModel Unit Unit}
    (hl : file.stdlib.lookup aux2 = some d) (hb : revAux2Body aux2 d = true)
    (tags : Mem.Concrete.Tags) : ∀ (vs accs : List Val) (bt bt' : BaseType),
    ∃ body env', functionBody file (.sym aux2) [.list bt vs, .list bt' accs] = .ok (body, env') ∧
      PureEval.Eval file tags env' (.inl body) (.inl (.list bt' (vs.reverse ++ accs))) := by
  unfold revAux2Body at hb
  split at hb
  case h_2 => cases hb
  rename_i ty xs bxs acc bacc a0 u0 a1 u1 xs1 pa1 nbt a2 u2 acc1 pa2 pa3 x bx pa4 xs2 bxs2 a3 u3
    self' a4 u4 xs3 a5 u5 a6 u6 x1 a7 u7 acc2
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨hd, hself⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hb
  have nd := distinct_nodup hd
  simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.mem_nil_iff,
    or_false, not_or] at nd
  obtain ⟨⟨n1, n2, n3⟩, ⟨n4, n5⟩, n6, -⟩ := nd
  have fb : ∀ l1 l2 : Val, functionBody file (.sym aux2) [l1, l2] =
      .ok (.mk a0 u0 (.case_ (.mk a1 u1 (.sym xs1))
        [(.mk pa1 (.ctor (.nil nbt) []), .mk a2 u2 (.sym acc1)),
         (.mk pa2 (.ctor .cons [.mk pa3 (.base (some x, bx)), .mk pa4 (.base (some xs2, bxs2))]),
          .mk a3 u3 (.call (.sym self') [.mk a4 u4 (.sym xs3),
            .mk a5 u5 (.ctor .cons [.mk a6 u6 (.sym x1), .mk a7 u7 (.sym acc2)])]))]),
        extendEnv [(xs, l1), (acc, l2)] ∅) := by
    intro l1 l2
    simp [functionBody, hl, pure, Except.pure, bind, Except.bind]
  intro vs
  induction vs with
  | nil =>
    intro accs bt bt'
    refine ⟨_, _, fb _ _, ?_⟩
    have lx : (extendEnv [(xs, Value.list bt []), (acc, .list bt' accs)] (∅ : Env)).lookup xs1 =
        some (.list bt []) := by
      rw [ReturnLit.lookup_key h1]; simp [extendEnv]
    refine .case_ (xs := []) (body := .mk a2 u2 (.sym acc1)) (.sym lx)
      (by simp [selectCase, matchPattern]) (.sym ?_)
    rw [ReturnLit.lookup_key h2]
    simp [extendEnv, Map.lookup_insert_of_key_ne _ _ (Ne.symm n1)]
  | cons v vs ih =>
    intro accs bt bt'
    refine ⟨_, _, fb _ _, ?_⟩
    obtain ⟨body, env', hf, he⟩ := ih (v :: accs) bt bt'
    let E : Env := extendEnv [(xs, Value.list bt (v :: vs)), (acc, .list bt' accs)] ∅
    have lx : E.lookup xs1 = some (.list bt (v :: vs)) := by
      rw [ReturnLit.lookup_key h1]; simp [E, extendEnv]
    have sel : selectCase (Value.list bt (v :: vs))
        [((Pattern.mk pa1 (.ctor (.nil nbt) []) : Pattern Sym), (Pexpr.mk a2 u2 (.sym acc1) : PE)),
         (.mk pa2 (.ctor .cons [.mk pa3 (.base (some x, bx)), .mk pa4 (.base (some xs2, bxs2))]),
          .mk a3 u3 (.call (.sym self') [.mk a4 u4 (.sym xs3),
            .mk a5 u5 (.ctor .cons [.mk a6 u6 (.sym x1), .mk a7 u7 (.sym acc2)])]))] =
        some ([(x, v), (xs2, .list bt vs)], .mk a3 u3 (.call (.sym self') [.mk a4 u4 (.sym xs3),
            .mk a5 u5 (.ctor .cons [.mk a6 u6 (.sym x1), .mk a7 u7 (.sym acc2)])])) := by
      simp [selectCase, matchPattern, bind, Option.bind]
    refine .case_ (.sym lx) sel ?_
    let E2 : Env := extendEnv [(x, v), (xs2, .list bt vs)] E
    have l3 : E2.lookup xs3 = some (.list bt vs) := by
      rw [ReturnLit.lookup_key h3]
      simp [E2, extendEnv, Map.lookup_insert_of_key_ne _ _ (Ne.symm n6)]
    have l4 : E2.lookup x1 = some v := by
      rw [ReturnLit.lookup_key h4]; simp [E2, extendEnv]
    have l5 : E2.lookup acc2 = some (.list bt' accs) := by
      rw [ReturnLit.lookup_key h5]
      simp [E2, E, extendEnv, Map.lookup_insert_of_key_ne _ _ n4, Map.lookup_insert_of_key_ne _ _ n5,
        Map.lookup_insert_of_key_ne _ _ (Ne.symm n1)]
    have hf' : functionBody file (.sym self') [.list bt vs, .list bt' (v :: accs)] = .ok (body, env') := by
      rw [functionBody_key hself]; exact hf
    rw [show (v :: vs).reverse ++ accs = vs.reverse ++ v :: accs by simp]
    exact .call (.cons (.sym l3) (.cons (.ctor (.cons (.sym l4) (.cons (.sym l5) .nil)) rfl) .nil)) hf' he

/-- **`reverse`** of a list of values is the reversed list. Its element type is the one of the
empty list in `reverse`'s body (`Std.revTy`), not the argument's. -/
theorem reverse_eval {s : Std} {proxy : Sym} (hs : stdOf file proxy = some s) (tags : Mem.Concrete.Tags)
    (env : Env) (bt : BaseType) (vs : List Val) (ann : List Annot) (u : Unit) (a1 : List Annot)
    (u1 : Unit) (x : Sym) (hx : env.lookup x = some (.list bt vs)) :
    PureEval.Eval file tags env (.inl (.mk ann u (.call (.sym s.rev) [.mk a1 u1 (.sym x)])))
      (.inl (.list s.revTy vs.reverse)) := by
  obtain ⟨-, -, -, -, -, -, ⟨d, hl, hb⟩, -, ⟨d2, hl2, hb2⟩⟩ := stdOf_spec hs
  unfold revBody at hb
  split at hb
  case h_2 => cases hb
  rename_i ty xs bxs a0 u0 aux a1' u1' xs' a2 u2 nbt
  split at hb
  case isFalse => cases hb
  rename_i hk
  cases hb
  obtain ⟨body, env', hf, he⟩ := revAux2_eval hl2 hb2 tags vs [] bt s.revTy
  have fr : functionBody file (.sym s.rev) [.list bt vs] =
      .ok (.mk a0 u0 (.call (.sym s.revAux2) [.mk a1' u1' (.sym xs'), .mk a2 u2 (.ctor (.nil s.revTy) [])]),
        extendEnv [(xs, .list bt vs)] ∅) := by
    simp [functionBody, hl, pure, Except.pure, bind, Except.bind]
  have lx : (extendEnv [(xs, Value.list bt vs)] (∅ : Env)).lookup xs' = some (.list bt vs) := by
    rw [ReturnLit.lookup_key hk]; simp [extendEnv]
  refine .call (.cons (.sym hx) .nil) fr ?_
  rw [List.append_nil] at he
  exact .call (.cons (.sym lx) (.cons (.ctor .nil rfl) .nil)) hf he

/-! ### Steps of the library bodies -/

open SeqReach (PureEval located_next_reaches pure_symbol pure_value)

theorem isChar_inv {t : Ctype} (h : isChar t = true) : ∃ ann, t = charTy ann := by
  unfold isChar at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

/-- Entering `memop(PtrArrayShift, p, …)`: its first operand, under the focus. -/
theorem memop_enter (ann : List Annot) (p : PE) (ps : List PE) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    ReturnConst.Reaches file labels ⟨.effectExpr (.mk ann (.memop .ptrArrayShift (p :: ps))) env, k, m⟩
      ⟨.pureExpr p env, .arguments (.memop .ptrArrayShift) [] ps env :: k, SeqReach.focusMemory ann m⟩ := by
  apply located_next_reaches ann (by intro o; simp)
  simp only [request, requestAux, awaitsScheduling, arguments]
  change (match (if (SeqReach.focusMemory ann m).currentLocation == m.currentLocation then
    Request.next (.pureExpr p env) (.arguments (.memop .ptrArrayShift) [] ps env :: k)
    else .next (.setLocation (SeqReach.focusMemory ann m).currentLocation (.pureExpr p env))
      (.arguments (.memop .ptrArrayShift) [] ps env :: k)) with
    | .next (.jumping s vs env) frames => jump labels s vs env frames
    | r => r) = _
  by_cases eq : (SeqReach.focusMemory ann m).currentLocation == m.currentLocation <;> simp [eq]

/-- Entering a `load` action: its type operand, under the focus. -/
theorem load_enter (ann : List Annot) (l : Loc) (u : Unit) (p q : PE) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    ReturnConst.Reaches file labels
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.load p q .na))))) env, k, m⟩
      ⟨.pureExpr p env, .arguments (.memory .load) [] [q] env :: k, SeqReach.focusMemory ann m⟩ := by
  apply located_next_reaches ann (by intro o; simp)
  simp only [request, requestAux, awaitsScheduling, arguments]
  change (match (if (SeqReach.focusMemory ann m).currentLocation == m.currentLocation then
    Request.next (.pureExpr p env) (.arguments (.memory .load) [] [q] env :: k)
    else .next (.setLocation (SeqReach.focusMemory ann m).currentLocation (.pureExpr p env))
      (.arguments (.memory .load) [] [q] env :: k)) with
    | .next (.jumping s vs env) frames => jump labels s vs env frames
    | r => r) = _
  by_cases eq : (SeqReach.focusMemory ann m).currentLocation == m.currentLocation <;> simp [eq]

/-- Entering `proc(f, ps)`: the function pointer, then the operands, under the focus. -/
theorem proc_enter (ann : List Annot) (u : Unit) (f : Sym) (ps : List PE) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) :
    ReturnConst.Reaches file labels ⟨.effectExpr (.mk ann (.proc u (.sym f) ps)) env, k, m⟩
      ⟨.pureExpr (.mk [] () (.val (.loaded (.specified (.pointer (.function f)))))) env,
        .arguments (.directProcedure env) [] ps env :: k, SeqReach.focusMemory ann m⟩ := by
  apply located_next_reaches ann (by intro o; simp)
  simp only [request, requestAux, awaitsScheduling, arguments]
  change (match (if (SeqReach.focusMemory ann m).currentLocation == m.currentLocation then
    Request.next (.pureExpr (.mk [] () (.val (.loaded (.specified (.pointer (.function f)))))) env)
      (.arguments (.directProcedure env) [] ps env :: k)
    else .next (.setLocation (SeqReach.focusMemory ann m).currentLocation
      (.pureExpr (.mk [] () (.val (.loaded (.specified (.pointer (.function f)))))) env))
      (.arguments (.directProcedure env) [] ps env :: k)) with
    | .next (.jumping s vs env) frames => jump labels s vs env frames
    | r => r) = _
  by_cases eq : (SeqReach.focusMemory ann m).currentLocation == m.currentLocation <;> simp [eq]

/-- **A direct call** reaches the dispatch on its evaluated operands. -/
theorem proc_apply (ann : List Annot) (u : Unit) (f : Sym) {ps : List PE} {env : Env}
    {args : List Val} (hargs : List.Forall₂ (fun p v => PureEval file labels p env v) ps args)
    (k : List Frame) (m : Mem.Concrete.State) :
    ReturnConst.Reaches file labels ⟨.effectExpr (.mk ann (.proc u (.sym f) ps)) env, k, m⟩
      ⟨.apply (.directProcedure env) (.loaded (.specified (.pointer (.function f))) :: args), k,
        SeqReach.focusMemory ann m⟩ :=
  (proc_enter ann u f ps env k m).trans ((pure_value [] _ env _ _).trans
    (by simpa [runtimeValue, runtimeLoaded, runtimeObject] using
      CallReach.arguments_reaches hargs (.directProcedure env) [] _ k _))

theorem focus_strObj {m : Mem.Concrete.State} {id addr : Int} {cs : List Int} (h : StrObj m id addr cs)
    (ann : List Annot) : StrObj (SeqReach.focusMemory ann m) id addr cs := by
  unfold SeqReach.focusMemory
  split
  · split
    · exact h
    · exact h.keeps ((Keeps.refl m).location _)
  · exact h

/-- **Shifting a pointer into a string object** by `n` characters. -/
theorem shift_reaches (ann a1 a2 a3 : List Annot) (u1 u2 u3 : Unit) {str : Sym} {env : Env}
    {t : Ctype} (ht : isChar t = true) (n : Int) {m : Mem.Concrete.State} {sid saddr : Int}
    {cs : List Int} (hs : StrObj m sid saddr cs) (i : Int)
    (hl : env.lookup str = some (.object (.pointer (.allocated sid (saddr + i)))))
    (h0 : 0 ≤ i + n) (h1 : i + n ≤ cs.length) {a' : Int} (ha : a' = saddr + i + n) (k : List Frame) :
    ReturnConst.Reaches file labels
      ⟨.effectExpr (.mk ann (.memop .ptrArrayShift [.mk a1 u1 (.sym str), .mk a2 u2 (.val (.ctype t)),
        .mk a3 u3 (.val (.object (.integer n)))])) env, k, m⟩
      ⟨.value (.object (.pointer (.allocated sid a'))), k, SeqReach.focusMemory ann m⟩ := by
  subst ha
  obtain ⟨tann, rfl⟩ := isChar_inv ht
  cases u1; cases u2; cases u3
  refine (memop_enter ann _ _ env k m).trans ((pure_symbol a1 str env _ hl _ _).trans ?_)
  refine (CallReach.arguments_reaches (.cons (pure_value a2 _ env) (.cons (pure_value a3 _ env) .nil))
    (.memop .ptrArrayShift) [] _ k _).trans ?_
  apply SeqReach.next_reaches (by intro o; simp)
  have := shift_char ⟨file.tagDefs, (SeqReach.focusMemory ann m).enumTypes⟩ tann (focus_strObj hs ann) i n h0 h1
  simp [request, requestAux, awaitsScheduling, runtimeValue, runtimeObject, this, pure, Except.pure,
    bind, Except.bind]

/-- The access annotation the dynamics records for a load of `size` bytes at `addr` under `k`. -/
def loadAnn (k : List Frame) (addr size : Int) : List Access :=
  [⟨k.findSome? (fun f => match f with | .excluded n => some n | _ => none), [], false, addr, size⟩]

/-- **Loading a character** of a string object. -/
theorem loadChar_reaches (ann a3 a4 : List Annot) (l : Loc) (u u3 u4 : Unit) {s1 : Sym} {env : Env}
    {t : Ctype} (ht : isChar t = true) {m : Mem.Concrete.State} {sid saddr : Int} {cs : List Int}
    (hs : StrObj m sid saddr cs) (i : Nat) (hi : i < cs.length) (hc : 0 ≤ cs[i] ∧ cs[i] < 128)
    (hl : env.lookup s1 = some (.object (.pointer (.allocated sid (saddr + i))))) (k : List Frame) :
    ReturnConst.Reaches file labels
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.load (.mk a3 u3 (.val (.ctype t)))
        (.mk a4 u4 (.sym s1)) .na))))) env, k, m⟩
      ⟨.value (.loaded (.specified (.integer cs[i]))), .annotations (loadAnn k (saddr + i) 1) :: k,
        {SeqReach.focusMemory ann m with lastUsed := some sid}⟩ := by
  obtain ⟨tann, rfl⟩ := isChar_inv ht
  cases u3; cases u4
  have hs' := focus_strObj hs ann
  let tags : Mem.Concrete.Tags := ⟨file.tagDefs, (SeqReach.focusMemory ann m).enumTypes⟩
  have hload := load_char tags tann hs' i hi hc
  have hacc := access_char tags tann hs' i hi
  obtain ⟨r, hr⟩ : ∃ r, request file labels
      ⟨.apply (.memory .load) [.ctype (charTy tann), .object (.pointer (.allocated sid (saddr + i)))], k,
        SeqReach.focusMemory ann m⟩ = r := ⟨_, rfl⟩
  have hr' := hr
  simp [request, requestAux, awaitsScheduling, memoryRequest, bind, Except.bind, pure,
    Except.pure] at hr'
  erw [hload, hacc] at hr'
  simp only at hr'
  have hm := Actions.memory_reaches (file := file) (labels := labels) (by intro o h; cases h)
    (hr.trans hr'.symm)
  exact (load_enter ann l u _ _ env k m).trans ((pure_value a3 _ env _ _).trans
    ((CallReach.arguments_reaches (.cons (pure_symbol a4 s1 env _ hl) .nil) (.memory .load) [] _ k _).trans
      hm))

/-! ### Frames, memories and environments -/

theorem pe_of_eval {p : PE} {env : Env} {v : Val}
    (h : ∀ tags, PureEval.Eval file tags env (.inl p) (.inl v)) : PureEval file labels p env v :=
  fun k m => PureEval.Eval.sound file _ (h (PureEval.tagsOf file m)) labels k m rfl

/-- A value over an annotation frame binds as below it. -/
theorem v_strongBind (xs : List Access) {v : Val} {pat : Pattern Sym} {b : EE} {env : Env}
    {ys : Bindings} (hm : matchPattern pat v = some ys) (k : List Frame) (m : Mem.Concrete.State) :
    ReturnConst.Reaches file labels ⟨.value v, .annotations xs :: .strongBind pat b env :: k, m⟩
      ⟨.effectExpr b (extendEnv ys env), .annotations xs :: k, m⟩ :=
  ExitCall.lift file labels (ExitCall.ra_annotations file labels (by intro _ h; cases h)
    (by intro h; cases h) (fun _ => ExitCall.ra_strongBind file labels hm _ _)) (ExitCall.plain_effectExpr _ _)

/-- A value over an annotation frame returns from a procedure. -/
theorem v_return (xs : List Access) (v : Val) (L : Labels) (k : List Frame) (m : Mem.Concrete.State) :
    ReturnConst.Reaches file labels ⟨.value v, .annotations xs :: .procedureReturn L :: k, m⟩
      ⟨.value v, .annotations xs :: k, m⟩ :=
  ExitCall.lift file labels (ExitCall.ra_annotations file labels (by intro _ h; cases h)
    (by intro h; cases h) (fun _ => by rw [requestAux.eq_def]; simp [awaitsScheduling]))
    (ExitCall.plain_value _)

/-- Two annotation frames merge. -/
theorem v_merge (xs ys : List Access) (v : Val) (k : List Frame) (m : Mem.Concrete.State) :
    ReturnConst.Reaches file labels ⟨.value v, .annotations xs :: .annotations ys :: k, m⟩
      ⟨.value v, .annotations (xs ++ ys) :: k, m⟩ :=
  SeqReach.next_reaches (by intro o; simp) (by simp [request, requestAux, awaitsScheduling])

theorem keeps_focus (ann : List Annot) (m : Mem.Concrete.State) :
    Keeps m (SeqReach.focusMemory ann m) := by
  unfold SeqReach.focusMemory
  split
  · split
    · exact Keeps.refl m
    · exact (Keeps.refl m).location _
  · exact Keeps.refl m

theorem lk_same {x y : Sym} (h : x.key = y.key) (v : Val) (env : Env) :
    (extendEnv [(y, v)] env).lookup x = some v := ExitCall.lookup_bind v h

theorem lk_other {x y : Sym} (h : x.key ≠ y.key) (v : Val) (env : Env) :
    (extendEnv [(y, v)] env).lookup x = env.lookup x := Map.lookup_insert_of_key_ne _ _ h

theorem revChars_take_succ {cs : List Int} {i : Nat} (hi : i < cs.length) :
    revChars (cs.take (i + 1)) = .object (.integer cs[i]) :: revChars (cs.take i) := by
  simp only [revChars, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    List.map_append, List.map_cons, List.map_nil, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append]

theorem string_char {cs : List Int} (hcs : StringFormat cs) {i : Nat} (hi : i + 1 < cs.length) :
    1 ≤ cs[i] ∧ cs[i] ≤ 127 := by
  have hm : cs[i] ∈ cs.dropLast := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp; omega, by simp [List.getElem_dropLast]⟩
  obtain ⟨h1, h2⟩ := hcs.2 _ hm
  exact ⟨h1, h2⟩

theorem string_last {cs : List Int} (hcs : StringFormat cs) {i : Nat} (hi : i + 1 = cs.length) :
    cs[i]'(by omega) = 0 := by
  have := hcs.1
  rw [List.getLast?_eq_getElem?, show cs.length - 1 = i by omega,
    List.getElem?_eq_getElem (by omega)] at this
  simpa using this

theorem plain_char {cs : List Int} (hcs : PlainFormat cs) {i : Nat} (hi : i + 1 < cs.length) :
    1 ≤ cs[i] ∧ cs[i] ≤ 127 := string_char hcs.stringFormat hi

theorem plain_last {cs : List Int} (hcs : PlainFormat cs) {i : Nat} (hi : i + 1 = cs.length) :
    cs[i]'(by omega) = 0 := string_last hcs.stringFormat hi

/-- **Loading a pointer** from a pointer object. -/
theorem loadPtr_reaches (ann a3 a4 : List Annot) (l : Loc) (u u3 u4 : Unit) {s1 : Sym} {env : Env}
    {t : Ctype} (ht : isCharPtr t = true) {m : Mem.Concrete.State} {fid faddr sid saddr : Int}
    (hp : PtrObj m fid faddr sid saddr)
    (hl : env.lookup s1 = some (.object (.pointer (.allocated fid faddr)))) (k : List Frame) :
    ReturnConst.Reaches file labels
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.load (.mk a3 u3 (.val (.ctype t)))
        (.mk a4 u4 (.sym s1)) .na))))) env, k, m⟩
      ⟨.value (.loaded (.specified (.pointer (.allocated sid saddr)))),
        .annotations (loadAnn k faddr 8) :: k,
        {SeqReach.focusMemory ann m with lastUsed := some fid}⟩ := by
  have ht' : ∃ tann q cann, t = .mk tann (.pointer q (charTy cann)) := by
    unfold isCharPtr at ht
    split at ht
    · exact ⟨_, _, _, rfl⟩
    · cases ht
  obtain ⟨tann, q, cann, rfl⟩ := ht'
  cases u3; cases u4
  have hp' : PtrObj (SeqReach.focusMemory ann m) fid faddr sid saddr := hp.keeps (keeps_focus ann m)
  let tags : Mem.Concrete.Tags := ⟨file.tagDefs, (SeqReach.focusMemory ann m).enumTypes⟩
  have hload := load_ptr tags tann q (charTy cann) rfl hp'
  have hacc := access_ptr tags tann q (charTy cann) hp'.slot
  obtain ⟨r, hr⟩ : ∃ r, request file labels
      ⟨.apply (.memory .load) [.ctype (.mk tann (.pointer q (charTy cann))),
        .object (.pointer (.allocated fid faddr))], k, SeqReach.focusMemory ann m⟩ = r := ⟨_, rfl⟩
  have hr' := hr
  simp [request, requestAux, awaitsScheduling, memoryRequest, bind, Except.bind, pure,
    Except.pure] at hr'
  erw [hload, hacc] at hr'
  simp only at hr'
  have hm := Actions.memory_reaches (file := file) (labels := labels) (by intro o h; cases h)
    (hr.trans hr'.symm)
  exact (load_enter ann l u _ _ env k m).trans ((pure_value a3 _ env _ _).trans
    ((CallReach.arguments_reaches (.cons (pure_symbol a4 s1 env _ hl) .nil) (.memory .load) [] _ k _).trans
      hm))

/-- Entering `proc(<builtin printf>, ps)`: the operands, under the focus. -/
theorem printf_enter (ann : List Annot) (u : Unit) (p : PE) (ps : List PE) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) :
    ReturnConst.Reaches file labels
      ⟨.effectExpr (.mk ann (.proc u (.impl (.builtinFunction "printf")) (p :: ps))) env, k, m⟩
      ⟨.pureExpr p env, .arguments (.builtin "printf") [] ps env :: k, SeqReach.focusMemory ann m⟩ := by
  apply located_next_reaches ann (by intro o; simp)
  simp only [request, requestAux, awaitsScheduling, arguments]
  change (match (if (SeqReach.focusMemory ann m).currentLocation == m.currentLocation then
    Request.next (.pureExpr p env) (.arguments (.builtin "printf") [] ps env :: k)
    else .next (.setLocation (SeqReach.focusMemory ann m).currentLocation (.pureExpr p env))
      (.arguments (.builtin "printf") [] ps env :: k)) with
    | .next (.jumping s vs env) frames => jump labels s vs env frames
    | r => r) = _
  by_cases eq : (SeqReach.focusMemory ann m).currentLocation == m.currentLocation <;> simp [eq]

/-- `m'` has the allocation state of `m`: the library calls allocate and free nothing. -/
def SameAlloc (m m' : Mem.Concrete.State) : Prop :=
  m'.lastAddress = m.lastAddress ∧ m'.nextId = m.nextId ∧ m'.dead = m.dead

@[simp] theorem focus_lastAddress (ann : List Annot) (m : Mem.Concrete.State) :
    (SeqReach.focusMemory ann m).lastAddress = m.lastAddress := by
  unfold SeqReach.focusMemory; split
  · split <;> rfl
  · rfl

@[simp] theorem focus_nextId (ann : List Annot) (m : Mem.Concrete.State) :
    (SeqReach.focusMemory ann m).nextId = m.nextId := by
  unfold SeqReach.focusMemory; split
  · split <;> rfl
  · rfl

@[simp] theorem focus_dead (ann : List Annot) (m : Mem.Concrete.State) :
    (SeqReach.focusMemory ann m).dead = m.dead := by
  unfold SeqReach.focusMemory; split
  · split <;> rfl
  · rfl

/-- Continue a run that reaches a direct call with the call's own run. -/
theorem bridge {S : State} {E : Env} {k : List Frame} {m : Mem.Concrete.State} {args : List Val}
    {v : Val} {Q : Mem.Concrete.State → Prop}
    (c : ReturnConst.Reaches file labels S ⟨.apply (.directProcedure E) args, k, m⟩)
    (h : ∃ m' zs, ReturnConst.Reaches file labels ⟨.apply (.directProcedure E) args, k, m⟩
      ⟨.value v, .annotations zs :: k, m'⟩ ∧ Q m') :
    ∃ m' zs, ReturnConst.Reaches file labels S ⟨.value v, .annotations zs :: k, m'⟩ ∧ Q m' :=
  let ⟨m', zs, r, q⟩ := h
  ⟨m', zs, c.trans r, q⟩

/-- **`rev_listFromStr_aux`** from the `i`-th character of a string object with a plain format
(`i + j + 1` characters in all): it returns the characters before the terminating 0, the first
one last. -/
theorem revAux_string_reaches {s : Std} {proxy : Sym} (hs : stdOf file proxy = some s) {cs : List Int}
    (hcs : StringFormat cs) {sid saddr : Int} (bt : BaseType) :
    ∀ (j i : Nat), i + j + 1 = cs.length → ∀ (f : Sym), f.key = s.revAux.key →
    ∀ (outer : Env) (k : List Frame) (m : Mem.Concrete.State),
    StrObj m sid saddr cs →
    ∃ m' zs, ReturnConst.Reaches file labels
      ⟨.apply (.directProcedure outer) [.loaded (.specified (.pointer (.function f))),
        .object (.pointer (.allocated sid (saddr + i))), .list bt (revChars (cs.take i))], k, m⟩
      ⟨.value (.list bt (revChars cs.dropLast)), .annotations zs :: k, m'⟩ ∧
      Keeps m m' ∧ m'.stdout = m.stdout ∧ SameAlloc m m' := by
  obtain ⟨-, -, -, hfun, -, -, -, ⟨d, hl, hb⟩, -⟩ := stdOf_spec hs
  unfold revAuxBody at hb
  split at hb
  case h_2 => cases hb
  rename_i dx loc mk ty str bstr acc bacc body
  have ord : ∀ f : Sym, f.key = s.revAux.key → libraryCall file f = none := by
    intro f hf; simp [libraryCall, ReturnLit.lookup_key (m := file.funs) hf, hfun]
  have resolved : ∀ f : Sym, f.key = s.revAux.key → ∀ P A : Val,
      procedureBody file f [P, A] = .ok (body, [(str, P), (acc, A)]) := by
    intro f hf P A
    rw [CallReach.stdlib_procedure_body (by rw [ReturnLit.lookup_key hf]; exact hl) rfl]; rfl
  obtain ⟨u, hb⟩ := Option.isSome_iff_exists.mp hb
  unfold revAuxCheck at hb
  obtain ⟨⟨sh, e1, r1⟩, q1, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨⟨str1, z⟩, q2, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨⟨c_, e2, r2⟩, q3, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨sh1, q4, hb⟩ := bind_some hb
  obtain ⟨⟨c_1, c, ife⟩, q5, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨⟨c1, yes, no⟩, q6, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨acc1, q7, hb⟩ := bind_some hb
  obtain ⟨⟨sh2, e3, r3⟩, q8, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨⟨str2, one⟩, q9, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨⟨ret, e4, r4⟩, q10, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨⟨self', sh3, c2, acc2⟩, q11, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨ret1, q12, hb⟩ := bind_some hb
  split at hb
  case isFalse => cases hb
  rename_i hc
  obtain ⟨rfl, rfl, hd, hself, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10⟩ := hc
  obtain ⟨B0, Psh, bsh, rfl⟩ := sseqOf_inv q1
  obtain ⟨A1, a1, u1, a2, u2, t1, a3, u3, rfl, ht1⟩ := shiftOf_inv q2
  obtain ⟨B5, Pc, bc, rfl⟩ := sseqOf_inv q3
  obtain ⟨A6, l7, u7, a8, u8, t2, a9, u9, rfl, ht2⟩ := loadOf_inv q4
  obtain ⟨B10, a11, u11, sa, pa, bc3, ua, up, no', rfl⟩ := specCase_inv q5
  obtain ⟨B12, a13, u13, a14, u14, a15, u15, rfl⟩ := ifZero_inv q6
  obtain ⟨B16, a17, u17, rfl⟩ := pureSym_inv q7
  obtain ⟨B18, P4, bsh2, rfl⟩ := sseqOf_inv q8
  obtain ⟨A19, a20, u20, a21, u21, t3, a22, u22, rfl, ht3⟩ := shiftOf_inv q9
  obtain ⟨B23, P5, bret, rfl⟩ := sseqOf_inv q10
  obtain ⟨A24, U24, a25, u25, a26, u26, a27, u27, a28, u28, rfl⟩ := procCons_inv q11
  obtain ⟨B29, a30, u30, rfl⟩ := pureSym_inv q12
  have nd := distinct_nodup hd
  simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.mem_nil_iff,
    or_false, not_or] at nd
  obtain ⟨⟨n_sa, n_ssh, n_sc_, n_sc, n_ssh2, n_sr⟩, ⟨n_ash, n_ac_, n_ac, n_ash2, n_ar⟩,
    ⟨n_shc_, n_shc, n_shsh2, n_shr⟩, ⟨n_c_c, n_c_sh2, n_c_r⟩, ⟨n_csh2, n_cr⟩, n_sh2r, -⟩ := nd
  intro j
  induction j with
  | zero =>
    intro i hij f hf outer k m hstr
    have hi : i < cs.length := by omega
    have c0 : cs[i] = 0 := string_last hcs (by omega)
    have hdl : cs.dropLast = cs.take i := by rw [List.dropLast_eq_take]; congr 1; omega
    let P : Val := .object (.pointer (.allocated sid (saddr + i)))
    let A : Val := .list bt (revChars (cs.take i))
    let E : Env := extendEnv [(str, P), (acc, A)] outer
    let m1 := SeqReach.focusMemory A1 m
    have hstr1 : StrObj m1 sid saddr cs := hstr.keeps (keeps_focus A1 m)
    let m2 : Mem.Concrete.State := {SeqReach.focusMemory A6 m1 with lastUsed := some sid}
    have hp : ∀ env : Env, env.lookup c1 = some (.object (.integer cs[i])) →
        PureEval file labels (.mk a13 u13 (.op .eq (.mk a14 u14 (.sym c1))
          (.mk a15 u15 (.val (.object (.integer 0)))))) env (Dynamics.boolean true) := by
      intro env hlk
      cases u13; cases u14; cases u15
      refine pe_of_eval fun tags => .op (.cons (.sym hlk) (.cons .val .nil)) ?_
      simp [primitive, integerBin, runtimeValue, runtimeObject, c0, pure, Except.pure]
    have chain := (CallReach.dispatch_reaches (labels := labels) true (ord f hf) (resolved f hf P A)
        outer k m).trans
      ((SeqReach.sseq_reaches B0 (shift_reaches A1 a1 a2 a3 u1 u2 u3 ht1 0 hstr i
        (by rw [ReturnLit.lookup_key k1]; simp [extendEnv, P]) (by omega) (by omega)
        (a' := saddr + i) (by simp) _) rfl).trans
      ((ExitCall.lift file labels (ExitCall.ra_sseq file labels _ _ _ _) (ExitCall.plain_effectExpr _ _)).trans
      ((loadChar_reaches A6 a8 a9 l7 u7 u8 u9 ht2 hstr1 i hi (by rw [c0]; omega)
        (by rw [ReturnLit.lookup_key k2]; exact lk_same rfl _ _) _).trans
      ((v_strongBind _ rfl _ _).trans
      ((SeqReach.specified_case_reaches B10 sa ua (.mk pa (.base (some c, bc3))) up
        (pure_symbol a11 c_1 _ _ (by rw [ReturnLit.lookup_key k3]; exact lk_same rfl _ _)) rfl _ m2).trans
      ((SeqReach.effect_if_reaches B12 true (hp _ (lk_same k4 _ _)) _ _).trans
      ((SeqReach.effect_pure_reaches B16 (pure_symbol a17 acc1 _ A (by
          rw [ReturnLit.lookup_key k5]
          simp only [lk_other n_ac, lk_other n_ac_, lk_other n_ash]
          simp [extendEnv, Map.lookup_insert_of_key_ne _ _ (Ne.symm n_sa)])) _ _).trans
      (v_return _ _ _ k _))))))))
    rw [hdl]
    exact ⟨_, _, chain, ((((keeps_focus A1 m).trans (keeps_focus A6 m1)).lastUsed _).trans
        (keeps_focus B10 m2)).trans ((keeps_focus B12 _).trans (keeps_focus B16 _)), by simp [m2, m1],
        by simp [SameAlloc, m2, m1]⟩
  | succ j ih =>
    intro i hij f hf outer k m hstr
    have hi : i + 1 < cs.length := by omega
    have hi' : i < cs.length := by omega
    have cpos := string_char hcs hi
    let P : Val := .object (.pointer (.allocated sid (saddr + i)))
    let A : Val := .list bt (revChars (cs.take i))
    let E : Env := extendEnv [(str, P), (acc, A)] outer
    let m1 := SeqReach.focusMemory A1 m
    have hstr1 : StrObj m1 sid saddr cs := hstr.keeps (keeps_focus A1 m)
    let m2 : Mem.Concrete.State := {SeqReach.focusMemory A6 m1 with lastUsed := some sid}
    let m4 := SeqReach.focusMemory B12 (SeqReach.focusMemory B10 m2)
    let m5 := SeqReach.focusMemory A19 m4
    have k14 : Keeps m m4 := ((((keeps_focus A1 m).trans (keeps_focus A6 m1)).lastUsed _).trans
        (keeps_focus B10 m2)).trans (keeps_focus B12 _)
    have k15 : Keeps m m5 := k14.trans (keeps_focus A19 _)
    have kc : Keeps m (SeqReach.focusMemory A24 m5) := k15.trans (keeps_focus A24 m5)
    have hp : ∀ env : Env, env.lookup c1 = some (.object (.integer cs[i])) →
        PureEval file labels (.mk a13 u13 (.op .eq (.mk a14 u14 (.sym c1))
          (.mk a15 u15 (.val (.object (.integer 0)))))) env (Dynamics.boolean false) := by
      intro env hlk
      cases u13; cases u14; cases u15
      refine pe_of_eval fun tags => .op (.cons (.sym hlk) (.cons .val .nil)) ?_
      have : (cs[i] == 0) = false := by simp; omega
      simp [primitive, integerBin, runtimeValue, runtimeObject, this, pure, Except.pure]
    have hcons : ∀ env : Env, env.lookup c2 = some (.object (.integer cs[i])) → env.lookup acc2 = some A →
        PureEval file labels (.mk a26 u26 (.ctor .cons [.mk a27 u27 (.sym c2), .mk a28 u28 (.sym acc2)])) env
          (.list bt (revChars (cs.take (i + 1)))) := by
      intro env h1 h2
      cases u26; cases u27; cases u28
      rw [revChars_take_succ hi']
      exact pe_of_eval fun tags => .ctor (.cons (.sym h1) (.cons (.sym h2) .nil)) rfl
    have c1 := (CallReach.dispatch_reaches (labels := labels) true (ord f hf) (resolved f hf P A)
        outer k m).trans
      ((SeqReach.sseq_reaches B0 (shift_reaches A1 a1 a2 a3 u1 u2 u3 ht1 0 hstr i
        (by rw [ReturnLit.lookup_key k1]; simp [extendEnv, P]) (by omega) (by omega)
        (a' := saddr + i) (by simp) _) rfl).trans
      ((ExitCall.lift file labels (ExitCall.ra_sseq file labels _ _ _ _) (ExitCall.plain_effectExpr _ _)).trans
      ((loadChar_reaches A6 a8 a9 l7 u7 u8 u9 ht2 hstr1 i hi' (by omega)
        (by rw [ReturnLit.lookup_key k2]; exact lk_same rfl _ _) _).trans
      ((v_strongBind _ rfl _ _).trans
      ((SeqReach.specified_case_reaches B10 sa ua (.mk pa (.base (some c, bc3))) up
        (pure_symbol a11 c_1 _ _ (by rw [ReturnLit.lookup_key k3]; exact lk_same rfl _ _)) rfl _ m2).trans
      ((SeqReach.effect_if_reaches B12 false (hp _ (lk_same k4 _ _)) _ _).trans
      ((SeqReach.sseq_reaches B18 (shift_reaches A19 a20 a21 a22 u20 u21 u22 ht3 1
        (hstr.keeps k14) i
        (by
          rw [ReturnLit.lookup_key k6]
          simp only [lk_other n_sc, lk_other n_sc_, lk_other n_ssh]
          simp [extendEnv, P]) (by omega) (by omega)
        (a' := saddr + ↑(i + 1)) (by push_cast; ring) _) rfl).trans
      ((ExitCall.lift file labels (ExitCall.ra_sseq file labels _ _ _ _) (ExitCall.plain_effectExpr _ _)).trans
      (proc_apply A24 U24 self'
        (.cons (pure_symbol a25 sh3 _ _ (lk_same k7 _ _))
          (.cons (hcons _ (by
              rw [ReturnLit.lookup_key k8, lk_other n_csh2]; exact lk_same rfl _ _)
            (by
              rw [ReturnLit.lookup_key k9]
              simp only [lk_other n_ash2, lk_other n_ac, lk_other n_ac_, lk_other n_ash]
              simp [extendEnv, Map.lookup_insert_of_key_ne _ _ (Ne.symm n_sa)])) .nil)) _ _)))))))))
    obtain ⟨m6, zs, r6, kp6, o6, s6⟩ := bridge c1
      (ih (i + 1) (by omega) self' hself _ _ _ (hstr.keeps kc))
    exact ⟨_, _, r6.trans ((v_strongBind zs rfl _ _).trans
      ((SeqReach.effect_pure_reaches B29 (pure_symbol a30 ret1 _ _ (lk_same k10 _ _)) _ _).trans
      ((v_merge _ _ _ _ _).trans (v_return _ _ _ k _)))),
      (kc.trans kp6).trans (keeps_focus B29 m6), by simp [o6, m4, m2, m1],
      by obtain ⟨s1, s2, s3⟩ := s6; simp [SameAlloc, s1, s2, s3, m4, m2, m1]⟩

theorem revAux_reaches {s : Std} {proxy : Sym} (hs : stdOf file proxy = some s) {cs : List Int}
    (hcs : PlainFormat cs) {sid saddr : Int} (bt : BaseType) :
    ∀ (j i : Nat), i + j + 1 = cs.length → ∀ (f : Sym), f.key = s.revAux.key →
    ∀ (outer : Env) (k : List Frame) (m : Mem.Concrete.State),
    StrObj m sid saddr cs →
    ∃ m' zs, ReturnConst.Reaches file labels
      ⟨.apply (.directProcedure outer) [.loaded (.specified (.pointer (.function f))),
        .object (.pointer (.allocated sid (saddr + i))), .list bt (revChars (cs.take i))], k, m⟩
      ⟨.value (.list bt (revChars cs.dropLast)), .annotations zs :: k, m'⟩ ∧
      Keeps m m' ∧ m'.stdout = m.stdout ∧ SameAlloc m m' := revAux_string_reaches hs hcs.stringFormat bt

theorem revChars_nil : revChars [] = [] := rfl

theorem revChars_reverse (cs : List Int) :
    (revChars cs).reverse = cs.map fun c => .object (.integer c) := by
  simp [revChars]

theorem plain_ne {cs : List Int} (hcs : PlainFormat cs) : 0 < cs.length := by
  have := hcs.1
  cases cs with
  | nil => simp at this
  | cons _ _ => simp

theorem string_ne {cs : List Int} (hcs : StringFormat cs) : 0 < cs.length := by
  have := hcs.1
  cases cs with
  | nil => simp at this
  | cons _ _ => simp

/-- `rev_listFromStr_aux` from the start of the string. -/
theorem revAux_string_start {s : Std} {proxy : Sym} (hs : stdOf file proxy = some s) {cs : List Int}
    (hcs : StringFormat cs) {sid saddr : Int} (bt : BaseType) (f : Sym) (hf : f.key = s.revAux.key)
    (outer : Env) (k : List Frame) (m : Mem.Concrete.State) (hstr : StrObj m sid saddr cs) :
    ∃ m' zs, ReturnConst.Reaches file labels
      ⟨.apply (.directProcedure outer) [.loaded (.specified (.pointer (.function f))),
        .object (.pointer (.allocated sid saddr)), .list bt []], k, m⟩
      ⟨.value (.list bt (revChars cs.dropLast)), .annotations zs :: k, m'⟩ ∧
      Keeps m m' ∧ m'.stdout = m.stdout ∧ SameAlloc m m' := by
  have h := revAux_string_reaches (labels := labels) hs hcs bt (cs.length - 1) 0
    (by have := string_ne hcs; omega) f hf outer k m hstr
  simpa only [Nat.cast_zero, add_zero, List.take_zero, revChars_nil] using h

theorem revAux_start {s : Std} {proxy : Sym} (hs : stdOf file proxy = some s) {cs : List Int}
    (hcs : PlainFormat cs) {sid saddr : Int} (bt : BaseType) (f : Sym) (hf : f.key = s.revAux.key)
    (outer : Env) (k : List Frame) (m : Mem.Concrete.State) (hstr : StrObj m sid saddr cs) :
    ∃ m' zs, ReturnConst.Reaches file labels
      ⟨.apply (.directProcedure outer) [.loaded (.specified (.pointer (.function f))),
        .object (.pointer (.allocated sid saddr)), .list bt []], k, m⟩
      ⟨.value (.list bt (revChars cs.dropLast)), .annotations zs :: k, m'⟩ ∧
      Keeps m m' ∧ m'.stdout = m.stdout ∧ SameAlloc m m' := revAux_string_start hs hcs.stringFormat bt f hf outer k m hstr

/-- **`listFromStr`** on a pointer to the start of a string object with a plain format: the
characters before the terminating 0, in order. -/
theorem lfs_string_reaches {s : Std} {proxy : Sym} (hs : stdOf file proxy = some s) {cs : List Int}
    (hcs : StringFormat cs) {sid saddr : Int} (f : Sym) (hf : f.key = s.lfs.key)
    (outer : Env) (k : List Frame) (m : Mem.Concrete.State) (hstr : StrObj m sid saddr cs) :
    ∃ m' zs, ReturnConst.Reaches file labels
      ⟨.apply (.directProcedure outer) [.loaded (.specified (.pointer (.function f))),
        .object (.pointer (.allocated sid saddr))], k, m⟩
      ⟨.value (.list s.revTy (cs.dropLast.map fun c => .object (.integer c))), .annotations zs :: k, m'⟩ ∧
      Keeps m m' ∧ m'.stdout = m.stdout ∧ SameAlloc m m' := by
  obtain ⟨-, -, hfun, -, -, ⟨d, hl, hb⟩, -, -, -⟩ := stdOf_spec hs
  unfold lfsBody at hb
  split at hb
  case h_2 => cases hb
  rename_i dx loc mk ty str bstr body
  have ord : libraryCall file f = none := by
    simp [libraryCall, ReturnLit.lookup_key (m := file.funs) hf, hfun]
  let P : Val := .object (.pointer (.allocated sid saddr))
  have resolved : procedureBody file f [P] = .ok (body, [(str, P)]) := by
    rw [CallReach.stdlib_procedure_body (by rw [ReturnLit.lookup_key hf]; exact hl) rfl]; rfl
  unfold lfsCheck at hb
  obtain ⟨⟨rx, e1, r1⟩, q1, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨⟨aux, str'⟩, q2, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨⟨rev, rx'⟩, q3, hb⟩ := bind_some hb; try dsimp only at hb
  split at hb
  case isFalse => cases hb
  rename_i hc
  cases hb
  obtain ⟨hd, k1, k2⟩ := hc
  obtain ⟨B0, P0, b0, rfl⟩ := sseqOf_inv q1
  obtain ⟨A1, U1, a2, u2, a3, u3, nbt, rfl⟩ := procNil_inv q2
  obtain ⟨B4, a5, u5, a6, u6, rfl⟩ := pureCall_inv q3
  have nd := distinct_nodup hd
  simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.mem_nil_iff,
    or_false] at nd
  obtain ⟨n_sr, -⟩ := nd
  let E : Env := extendEnv [(str, P)] outer
  have c1 := (CallReach.dispatch_reaches (labels := labels) true ord resolved outer k m).trans
    ((ExitCall.lift file labels (ExitCall.ra_sseq file labels _ _ _ _) (ExitCall.plain_effectExpr _ _)).trans
    (proc_apply A1 U1 s.revAux (env := E)
      (.cons (pure_symbol a2 str' _ P (by rw [ReturnLit.lookup_key k1]; simp [E, extendEnv]))
        (.cons (by cases u3; exact pe_of_eval fun tags => .ctor .nil rfl) .nil)) _ _))
  obtain ⟨m2, zs, r2, kp2, o2, s2⟩ := bridge c1
    (revAux_string_start hs hcs nbt s.revAux rfl _ _ _ (hstr.keeps (keeps_focus A1 m)))
  have r3 := r2.trans ((v_strongBind zs rfl _ _).trans
    ((SeqReach.effect_pure_reaches B4 (pe_of_eval fun tags => reverse_eval hs tags _ nbt _ a5 u5 a6 u6 rx'
      (lk_same k2 _ _)) _ _).trans (v_return _ _ _ k _)))
  rw [revChars_reverse] at r3
  exact ⟨_, _, r3, ((keeps_focus A1 m).trans kp2).trans (keeps_focus B4 m2), by simp [o2],
    by obtain ⟨t1, t2, t3⟩ := s2; simp [SameAlloc, t1, t2, t3]⟩

theorem lfs_reaches {s : Std} {proxy : Sym} (hs : stdOf file proxy = some s) {cs : List Int}
    (hcs : PlainFormat cs) {sid saddr : Int} (f : Sym) (hf : f.key = s.lfs.key)
    (outer : Env) (k : List Frame) (m : Mem.Concrete.State) (hstr : StrObj m sid saddr cs) :
    ∃ m' zs, ReturnConst.Reaches file labels
      ⟨.apply (.directProcedure outer) [.loaded (.specified (.pointer (.function f))),
        .object (.pointer (.allocated sid saddr))], k, m⟩
      ⟨.value (.list s.revTy (cs.dropLast.map fun c => .object (.integer c))), .annotations zs :: k, m'⟩ ∧
      Keeps m m' ∧ m'.stdout = m.stdout ∧ SameAlloc m m' := lfs_string_reaches hs hcs.stringFormat f hf outer k m hstr

/-- **`printf_proxy`** on an argument object holding a pointer to the first character of a string
object with a plain format, and no further argument: it prints the string, returns its length and
keeps every object. -/
theorem proxy_reaches {s : Std} {proxy : Sym} (hs : stdOf file proxy = some s) {cs : List Int}
    (hcs : PlainFormat cs) {m : Mem.Concrete.State} {fid faddr sid saddr : Int}
    (hp : PtrObj m fid faddr sid saddr) (hstr : StrObj m sid saddr cs) (outer : Env)
    (k : List Frame) (bt : BaseType) :
    ∃ m' zs, ReturnConst.Reaches file labels
      ⟨.apply (.procedure outer) [.loaded (.specified (.pointer (.function proxy))),
        .object (.pointer (.allocated fid faddr)), .list bt []], k, m⟩
      ⟨.value (.loaded (.specified (.integer (plainText cs).length))), .annotations zs :: k, m'⟩ ∧
      m'.stdout = m.stdout ++ plainText cs ∧ Keeps m m' ∧ SameAlloc m m' := by
  obtain ⟨rfl, hfun, -, -, ⟨d, hl, hb⟩, -, -, -, -⟩ := stdOf_spec hs
  unfold proxyBody at hb
  split at hb
  case h_2 => cases hb
  rename_i dx loc mk ty tp btp as bas body
  have ord : libraryCall file s.proxy = none := by simp [libraryCall, hfun]
  let PF : Val := .object (.pointer (.allocated fid faddr))
  let L0 : Val := .list bt []
  have resolved : procedureBody file s.proxy [PF, L0] = .ok (body, [(tp, PF), (as, L0)]) := by
    rw [CallReach.stdlib_procedure_body hl rfl]; rfl
  unfold proxyCheck at hb
  obtain ⟨⟨fp_, e1, r1⟩, q1, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨tp', q2, hb⟩ := bind_some hb
  obtain ⟨⟨fp_', fp, r2⟩, q3, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨⟨xs, e2, r3⟩, q4, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨⟨lfs, fp'⟩, q5, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨⟨ret, e3, r4⟩, q6, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨⟨xs', as'⟩, q7, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨ret', q8, hb⟩ := bind_some hb
  split at hb
  case isFalse => cases hb
  rename_i hc
  cases hb
  obtain ⟨hd, k1, k2, k3, k4, k5, k6⟩ := hc
  obtain ⟨B0, P0, b0, rfl⟩ := sseqOf_inv q1
  obtain ⟨A1, l1, U1, a2, u2, t, a3, u3, rfl, ht⟩ := loadOf_inv q2
  obtain ⟨B4, a5, u5, sa, pa, bfp, ua, up, no, rfl⟩ := specCase_inv q3
  obtain ⟨B5, P5, b5, rfl⟩ := sseqOf_inv q4
  obtain ⟨A6, U6, a7, u7, rfl⟩ := procOne_inv q5
  obtain ⟨B7, P7, b7, rfl⟩ := sseqOf_inv q6
  obtain ⟨A8, U8, a9, u9, a10, u10, rfl⟩ := procPrintf_inv q7
  obtain ⟨B11, a12, u12, rfl⟩ := pureSym_inv q8
  have nd := distinct_nodup hd
  simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.mem_nil_iff,
    or_false, not_or] at nd
  obtain ⟨⟨n_ta, -, -, -, -⟩, ⟨n_afp_, n_afp, n_axs, -⟩, -⟩ := nd
  let E : Env := extendEnv [(tp, PF), (as, L0)] outer
  let m2 : Mem.Concrete.State := {SeqReach.focusMemory A1 m with lastUsed := some fid}
  let mc := SeqReach.focusMemory A6 (SeqReach.focusMemory B4 m2)
  have kc : Keeps m mc := ((keeps_focus A1 m).lastUsed _).trans
    ((keeps_focus B4 m2).trans (keeps_focus A6 _))
  have c1 := (CallReach.dispatch_reaches (labels := labels) false ord resolved outer k m).trans
    ((ExitCall.lift file labels (ExitCall.ra_sseq file labels _ _ _ _) (ExitCall.plain_effectExpr _ _)).trans
    ((loadPtr_reaches A1 a2 a3 l1 U1 u2 u3 ht hp
      (by rw [ReturnLit.lookup_key k1]; simp [extendEnv, PF]) _).trans
    ((v_strongBind _ rfl _ _).trans
    ((SeqReach.specified_case_reaches B4 sa ua (.mk pa (.base (some fp, bfp))) up
      (pure_symbol a5 fp_' _ _ (by rw [ReturnLit.lookup_key k2]; exact lk_same rfl _ _)) rfl _ m2).trans
    ((ExitCall.lift file labels (ExitCall.ra_sseq file labels _ _ _ _) (ExitCall.plain_effectExpr _ _)).trans
    (proc_apply A6 U6 s.lfs (.cons (pure_symbol a7 fp' _ _ (lk_same k3 _ _)) .nil) _ _))))))
  obtain ⟨m4, zs, r4, kp4, o4, s4⟩ := bridge c1 (lfs_reaches hs hcs s.lfs rfl _ _ _ (hstr.keeps kc))
  have hasl : ∀ v w : Val, (extendEnv [(xs, v)] (extendEnv [(fp, w)]
      (extendEnv [(fp_, .loaded (.specified (.pointer (.allocated sid saddr))))] E))).lookup as' = some L0 := by
    intro v w
    rw [ReturnLit.lookup_key k5, lk_other n_axs, lk_other n_afp, lk_other n_afp_]
    simp [E, extendEnv, Map.lookup_insert_of_key_ne _ _ (Ne.symm n_ta), L0]
  let m5 := SeqReach.focusMemory A8 m4
  have r5 := r4.trans ((v_strongBind zs rfl _ _).trans
    ((ExitCall.lift file labels (ExitCall.ra_sseq file labels _ _ _ _) (ExitCall.plain_effectExpr _ _)).trans
    ((printf_enter A8 U8 _ _ _ _ m4).trans
    ((pure_symbol a9 xs' _ _ (lk_same k4 _ _) _ _).trans
    ((CallReach.arguments_reaches (.cons (pure_symbol a10 as' _ L0 (hasl _ _)) .nil)
      (.builtin "printf") [] _ _ _).trans
    ((builtin_printf_plain hcs s.revTy bt _ m5).trans
    ((SeqReach.strong_bind_reaches rfl _ _).trans
    ((SeqReach.effect_pure_reaches B11 (pure_symbol a12 ret' _ _ (lk_same k6 _ _)) _ _).trans
    ((v_merge _ _ _ _ _).trans (v_return _ _ _ k _))))))))))
  obtain ⟨t1, t2, t3⟩ := s4
  refine ⟨_, _, r5, by simp [m5, o4, m2], ?_, by simp [SameAlloc, m5, t1, t2, t3, m2]⟩
  exact (kc.trans kp4).trans (((keeps_focus A8 m4).stdout _).trans (keeps_focus B11 _))


end Runs

end Silmaril.Compile.Core.Verified.PrintfStd
