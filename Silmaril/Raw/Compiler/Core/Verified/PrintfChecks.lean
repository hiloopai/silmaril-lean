module

public import Silmaril.Compiler.Core.Verified.PrintfArg.Defs
public import Silmaril.Compiler.Core.Verified.PrintExprLink.Defs
/-! # Concrete checks of the formatted-output proof boundaries

The format permits conversions while the old plain-format recognizer rejects
them. The argument helper has satisfiable hypotheses, preserves caller output,
and rejects aliased parameter keys. Decimal capacity covers zero, negative
values and both signed-int bounds. Runtime expression checks use the two
bitwise expressions in ci/0067-band1 and ci/0068-bor1.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PrintfChecks

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open PrintfArg

example : PrintfStd.StringFormat [68, 69, 66, 85, 71, 62, 32, 37, 100, 10, 0] := by unfold PrintfStd.StringFormat; decide
example : ¬ PrintfStd.PlainFormat [68, 69, 66, 85, 71, 62, 32, 37, 100, 10, 0] := by decide
example : ¬ PrintfStd.StringFormat [37, 0, 100, 0] := by unfold PrintfStd.StringFormat; decide
example : ¬ PrintfStd.StringFormat [37, 100] := by unfold PrintfStd.StringFormat; decide

def ty : Sym := ⟨⟨[]⟩, 0, .id "ty"⟩
def value : Sym := ⟨⟨[]⟩, 1, .id "x"⟩
def ptr : Sym := ⟨⟨[]⟩, 2, .id "p"⟩

/-- The exact statement structure of std.core's helper. -/
def argBody (ty value ptr : Sym) : EExp :=
  .mk [] (.wseq (.mk [] (.base (some ptr, .object .pointer)))
    (.mk [] (.action (.mk .pos (.mk .unknown () (.create
      (.mk [] () (.ctor .ivAlignof [.mk [] () (.sym ty)]))
      (.mk [] () (.sym ty)) (.other "Core"))))))
    (.mk [] (.wseq (.mk [] (.base (none, .unit)))
      (.mk [] (.action (.mk .pos (.mk .unknown () (.store false
        (.mk [] () (.sym ty)) (.mk [] () (.sym ptr)) (.mk [] () (.sym value)) .na)))))
      (.mk [] (.pure (.mk [] () (.sym ptr)))))))

example : createStoreBody ty value (argBody ty value ptr) = some () := by decide
example : createStoreBody ty value (argBody ty value ty) = none := by decide
example : createStoreBody ty ty (argBody ty ty ptr) = none := by decide

/-- A fresh argument object can actually be produced, over an arbitrary program
and continuation, with prior caller output intact. -/
theorem arg_body_runs (file : Program) (labels : Labels) (k : List Frame) (out : String)
    (n : Int) (range : Mem.Concrete.IntRange n) :
    let m : Mem.Concrete.State := {nextId := 3, lastAddress := 4096, stdout := out}
    let env : Env := (∅ : Env).insert value (.loaded (.specified (.integer n)))
      |>.insert ty (.ctype (Mem.Concrete.intType []))
    ∃ m' zs, ReturnConst.Reaches file labels ⟨.effectExpr (argBody ty value ptr) env, k, m⟩
      ⟨.value (.object (.pointer (.allocated 3 4092))), .annotations zs :: k, m'⟩ ∧
      Locals.Slot m' 3 4092 n ∧ StrMem.Keeps m m' ∧ m'.stdout = out ∧
      m'.nextId = 4 ∧ m'.lastAddress = 4092 ∧ m'.dead = [] := by
  intro m env
  exact body_reaches (file := file) (labels := labels) (ty := ty) (v := value) (by decide) []
    (by simp [env]) (by
      dsimp only [env]
      rw [Map.lookup_insert_of_key_ne _ _ (show MapKey.key value ≠ MapKey.key ty by decide)]
      exact Map.lookup_insert _ _ _)
    range k m (by dsimp [m, Mem.Concrete.nextIntAddress]; omega) (by simp [m])

example : PrintLink.Fits [.int 0] := PrintfDecimal.decimal_fits (by norm_num [Mem.Concrete.IntRange])
example : PrintLink.Fits [.int (-23)] := PrintfDecimal.decimal_fits (by norm_num [Mem.Concrete.IntRange])
example : PrintLink.Fits [.int (-2147483648)] := PrintfDecimal.decimal_fits (by norm_num [Mem.Concrete.IntRange])
example : PrintLink.Fits [.int 2147483647] := PrintfDecimal.decimal_fits (by norm_num [Mem.Concrete.IntRange])

def band : IntExpr.Term := .bit .and (.lit 10) (.lit 136)
def bor : IntExpr.Term := .bit .or (.lit 10) (.lit 136)

example : band.Ok 0 ∧ band.val 0 = 8 := by
  norm_num [band, IntExpr.Term.Ok, ConvInt.IsInt, IntExpr.Term.val, Bitwise.Op.apply]; decide
example : bor.Ok 0 ∧ bor.val 0 = 138 := by
  norm_num [bor, IntExpr.Term.Ok, ConvInt.IsInt, IntExpr.Term.val, Bitwise.Op.apply]; decide

/-- The actual emitted operations evaluate the bitwise expression and append
its digits; this statement holds for any earlier output and following code. -/
theorem band_exec {size : Nat} {fr : Silmaril.Machine.Lir.Frame Mir.Reg}
    {m : Silmaril.Machine.Lir.Memory} {out : List UInt8}
    (inv : PrintLink.Inv size fr m out) (room : PrintLink.outBase + out.length + 11 ≤ size)
    (hs : size < 2 ^ 64) (rest : List PrintLink.Op) :
    ∃ fr' m', Silmaril.Machine.Lir.execOps (PrintExpr.closedDecimalOps band ++ rest) fr m =
      Silmaril.Machine.Lir.execOps rest fr' m' ∧ PrintLink.Inv size fr' m' (out ++ PrintLink.Item.render (.int 8)) := by
  have ok : band.Ok 0 := by norm_num [band, IntExpr.Term.Ok, ConvInt.IsInt]
  have val : band.val 0 = 8 := by change Int.land 10 136 = 8; decide
  have range : ConvInt.IsInt (band.val 0) := by rw [val]; norm_num [ConvInt.IsInt]
  simpa only [val] using PrintExpr.closedDecimal_exec inv room hs ok range rest

example : PrintExprLink.Fits [68, 69, 66, 85, 71, 62, 32] [10] := by decide

end Silmaril.Compile.Core.Verified.PrintfChecks
