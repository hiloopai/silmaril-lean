module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Import

/-!
# Errata for the meta-theory IL script

`specs/spectec/meta-theory-3a10283c5b/meta-il.ast` is the `--ast` output of SpecTec's own
semantics of its internal language (`Wasm-DSL/spectec@3a10283c5b`, branch `meta-theory`,
`spectec/doc/semantics/il/*.spectec`). It is imported here as `Specs.metail` and patched with
the same mechanism as the WebAssembly errata (`Silmaril/Raw/Wasm/SpecTec/SpecTec/Errata.lean`): each
`spectec_erratum` edits one definition's flat `--ast` rendering, the edit must occur exactly
once and must change something, and the edited text is decoded back into an `IL.Def`.

The numbers are local (`M1`, `M2`), not issue numbers; `docs/projects/wasm-extras.md` has the
witnesses and the draft upstream texts. Both errata are needed for the agreement theorems of
`Silmaril.Wasm.SpecTec.Meta.Thms`; the original script is kept, and its disagreements are stated as
theorems there too.

* **M1, `Step_exp`** (`5-reduction.spectec`, rules `BIN-ctx2` … `CMP-NE-false`).
  `BIN-ctx2` and `CMP-ctx2` write `e_1'` for `e_1` and `e_2` for `e_2'` in the conclusion, so the
  right operand never steps and the left one is replaced by an arbitrary expression.
  `CMP-EQ-true` and `CMP-NE-false` compare arbitrary expressions syntactically, and the rules
  for unequal operands (`CMP-EQ-false`, `CMP-NE-true`) are missing. The patch fixes the two
  conclusions, restricts the four comparison rules to values (`val`, as `MEM-*-false` already
  do and as the Rocq development `se_cmp_*` does), and adds the two missing rules.
* **M2, `$numbin`** (`3-primitives.spectec`, clauses `DIV` and `MOD` on `int`, `DIV` on `rat`, `MOD`
  on `nat`). `MOD` is written with `/`, so it divides; `DIV` on `int` converts the quotient to
  `nat`; the guards `i_2 =/= 0`, `$(i_1 \ i_2) = 0` and `q_2 =/= 0` are elaborated by
  *narrowing the variable to `nat`* (`cvt int nat (var "i_2")`), so they are undefined on
  negative operands. The patch writes each of these clauses as `Num.bin` reads it.

  `POW` on `int` and `rat` is left alone. It elaborates to `pow` at `rat` with an `int`
  exponent, which `il/valid.ml` types (`Xl.Num.typ_binop`) and `Xl.Num.bin` (eval.ml, and our
  `Num.bin`) does not evaluate; and `pow` at `int`, which `Xl.Num.bin` evaluates, is ill-typed
  for `il/valid.ml`, so `spectec_revalidate` rejects it. No IL expression is both, which is a
  finding about SpecTec's toolchain (`docs/projects/wasm-extras.md`, F6), not about this
  specification.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod

set_option maxRecDepth 100000

namespace Specs

spectec_import metail from "specs/spectec/meta-theory-3a10283c5b/meta-il.ast"

end Specs

spectec_erratum 1 in Specs.metail on "Step_exp"
  because "5-reduction.spectec: BIN-ctx2/CMP-ctx2 step e_2 but rewrite e_1; CMP-EQ-true and "
          "CMP-NE-false compare non-values; CMP-EQ-false and CMP-NE-true are missing"
  replacing "(exp \"e_1'\" (var \"exp\")) (exp \"e_2'\" (var \"exp\")) \"%|-%~>%\" (tup (var \""
            "S\") (case \"BIN\" (tup (var \"op\") (var \"e_1\") (var \"e_2\"))) (case \"BIN\" ("
            "tup (var \"op\") (var \"e_1'\") (var \"e_2\")))) (rule \"Step_exp\" \"%|-%~>%\" (t"
            "up (var \"S\") (var \"e_2\") (var \"e_2'\")))) (rule \"BIN-BOOL\" (exp \"S\" (var "
            "\"S\")) (exp \"boolbinop\" (var \"boolbinop\")) (exp \"b_1\" bool) (exp \"b_2\" bo"
            "ol) \"%|-%~>%\" (tup (var \"S\") (case \"BIN\" (tup (sub (var \"boolbinop\") (var "
            "\"binop\") (var \"boolbinop\")) (case \"BOOL\" (tup (var \"b_1\"))) (case \"BOOL\""
            " (tup (var \"b_2\"))))) (case \"BOOL\" (tup (call \"boolbin\" (exp (var \"boolbino"
            "p\")) (exp (var \"b_1\")) (exp (var \"b_2\"))))))) (rule \"BIN-NUM\" (exp \"S\" (v"
            "ar \"S\")) (exp \"numbinop\" (var \"numbinop\")) (exp \"num_1\" (var \"num\")) (ex"
            "p \"num_2\" (var \"num\")) \"%|-%~>%\" (tup (var \"S\") (case \"BIN\" (tup (sub (v"
            "ar \"numbinop\") (var \"binop\") (var \"numbinop\")) (sub (var \"num\") (var \"exp"
            "\") (var \"num_1\")) (sub (var \"num\") (var \"exp\") (var \"num_2\")))) (sub (var"
            " \"num\") (var \"exp\") (call \"numbin\" (exp (var \"numbinop\")) (exp (var \"num_"
            "1\")) (exp (var \"num_2\")))))) (rule \"CMP-ctx1\" (exp \"S\" (var \"S\")) (exp \""
            "op\" (var \"cmpop\")) (exp \"e_1\" (var \"exp\")) (exp \"e_2\" (var \"exp\")) (exp"
            " \"e_1'\" (var \"exp\")) \"%|-%~>%\" (tup (var \"S\") (case \"CMP\" (tup (var \"op"
            "\") (var \"e_1\") (var \"e_2\"))) (case \"CMP\" (tup (var \"op\") (var \"e_1'\") ("
            "var \"e_2\")))) (rule \"Step_exp\" \"%|-%~>%\" (tup (var \"S\") (var \"e_1\") (var"
            " \"e_1'\")))) (rule \"CMP-ctx2\" (exp \"S\" (var \"S\")) (exp \"op\" (var \"cmpop"
            "\")) (exp \"e_1\" (var \"exp\")) (exp \"e_2\" (var \"exp\")) (exp \"e_1'\" (var \""
            "exp\")) (exp \"e_2'\" (var \"exp\")) \"%|-%~>%\" (tup (var \"S\") (case \"CMP\" (t"
            "up (var \"op\") (var \"e_1\") (var \"e_2\"))) (case \"CMP\" (tup (var \"op\") (var"
            " \"e_1'\") (var \"e_2\")))) (rule \"Step_exp\" \"%|-%~>%\" (tup (var \"S\") (var "
            "\"e_2\") (var \"e_2'\")))) (rule \"CMP-EQ-true\" (exp \"S\" (var \"S\")) (exp \"e_"
            "1\" (var \"exp\")) (exp \"e_2\" (var \"exp\")) \"%|-%~>%\" (tup (var \"S\") (case "
            "\"CMP\" (tup (case \"EQ\" (tup)) (var \"e_1\") (var \"e_2\"))) (case \"BOOL\" (tup"
            " (bool true)))) (if (cmp eq bool (var \"e_1\") (var \"e_2\")))) (rule \"CMP-NE-fal"
            "se\" (exp \"S\" (var \"S\")) (exp \"e_1\" (var \"exp\")) (exp \"e_2\" (var \"exp\""
            ")) \"%|-%~>%\" (tup (var \"S\") (case \"CMP\" (tup (case \"NE\" (tup)) (var \"e_1"
            "\") (var \"e_2\"))) (case \"BOOL\" (tup (bool false)))) (if (cmp eq bool (var \"e_"
            "1\") (var \"e_2\"))))"
  with      "(exp \"e_2'\" (var \"exp\")) \"%|-%~>%\" (tup (var \"S\") (case \"BIN\" (tup (var "
            "\"op\") (var \"e_1\") (var \"e_2\"))) (case \"BIN\" (tup (var \"op\") (var \"e_1\""
            ") (var \"e_2'\")))) (rule \"Step_exp\" \"%|-%~>%\" (tup (var \"S\") (var \"e_2\") "
            "(var \"e_2'\")))) (rule \"BIN-BOOL\" (exp \"S\" (var \"S\")) (exp \"boolbinop\" (v"
            "ar \"boolbinop\")) (exp \"b_1\" bool) (exp \"b_2\" bool) \"%|-%~>%\" (tup (var \"S"
            "\") (case \"BIN\" (tup (sub (var \"boolbinop\") (var \"binop\") (var \"boolbinop\""
            ")) (case \"BOOL\" (tup (var \"b_1\"))) (case \"BOOL\" (tup (var \"b_2\"))))) (case"
            " \"BOOL\" (tup (call \"boolbin\" (exp (var \"boolbinop\")) (exp (var \"b_1\")) (ex"
            "p (var \"b_2\"))))))) (rule \"BIN-NUM\" (exp \"S\" (var \"S\")) (exp \"numbinop\" "
            "(var \"numbinop\")) (exp \"num_1\" (var \"num\")) (exp \"num_2\" (var \"num\")) \""
            "%|-%~>%\" (tup (var \"S\") (case \"BIN\" (tup (sub (var \"numbinop\") (var \"binop"
            "\") (var \"numbinop\")) (sub (var \"num\") (var \"exp\") (var \"num_1\")) (sub (va"
            "r \"num\") (var \"exp\") (var \"num_2\")))) (sub (var \"num\") (var \"exp\") (call"
            " \"numbin\" (exp (var \"numbinop\")) (exp (var \"num_1\")) (exp (var \"num_2\"))))"
            ")) (rule \"CMP-ctx1\" (exp \"S\" (var \"S\")) (exp \"op\" (var \"cmpop\")) (exp \""
            "e_1\" (var \"exp\")) (exp \"e_2\" (var \"exp\")) (exp \"e_1'\" (var \"exp\")) \"%|"
            "-%~>%\" (tup (var \"S\") (case \"CMP\" (tup (var \"op\") (var \"e_1\") (var \"e_2"
            "\"))) (case \"CMP\" (tup (var \"op\") (var \"e_1'\") (var \"e_2\")))) (rule \"Step"
            "_exp\" \"%|-%~>%\" (tup (var \"S\") (var \"e_1\") (var \"e_1'\")))) (rule \"CMP-ct"
            "x2\" (exp \"S\" (var \"S\")) (exp \"op\" (var \"cmpop\")) (exp \"e_1\" (var \"exp"
            "\")) (exp \"e_2\" (var \"exp\")) (exp \"e_2'\" (var \"exp\")) \"%|-%~>%\" (tup (va"
            "r \"S\") (case \"CMP\" (tup (var \"op\") (var \"e_1\") (var \"e_2\"))) (case \"CMP"
            "\" (tup (var \"op\") (var \"e_1\") (var \"e_2'\")))) (rule \"Step_exp\" \"%|-%~>%"
            "\" (tup (var \"S\") (var \"e_2\") (var \"e_2'\")))) (rule \"CMP-EQ-true\" (exp \"S"
            "\" (var \"S\")) (exp \"val_1\" (var \"val\")) (exp \"val_2\" (var \"val\")) \"%|-%"
            "~>%\" (tup (var \"S\") (case \"CMP\" (tup (case \"EQ\" (tup)) (sub (var \"val\") ("
            "var \"exp\") (var \"val_1\")) (sub (var \"val\") (var \"exp\") (var \"val_2\")))) "
            "(case \"BOOL\" (tup (bool true)))) (if (cmp eq bool (var \"val_1\") (var \"val_2\""
            ")))) (rule \"CMP-EQ-false\" (exp \"S\" (var \"S\")) (exp \"val_1\" (var \"val\")) "
            "(exp \"val_2\" (var \"val\")) \"%|-%~>%\" (tup (var \"S\") (case \"CMP\" (tup (cas"
            "e \"EQ\" (tup)) (sub (var \"val\") (var \"exp\") (var \"val_1\")) (sub (var \"val"
            "\") (var \"exp\") (var \"val_2\")))) (case \"BOOL\" (tup (bool false)))) (if (cmp "
            "ne bool (var \"val_1\") (var \"val_2\")))) (rule \"CMP-NE-false\" (exp \"S\" (var "
            "\"S\")) (exp \"val_1\" (var \"val\")) (exp \"val_2\" (var \"val\")) \"%|-%~>%\" (t"
            "up (var \"S\") (case \"CMP\" (tup (case \"NE\" (tup)) (sub (var \"val\") (var \"ex"
            "p\") (var \"val_1\")) (sub (var \"val\") (var \"exp\") (var \"val_2\")))) (case \""
            "BOOL\" (tup (bool false)))) (if (cmp eq bool (var \"val_1\") (var \"val_2\")))) (r"
            "ule \"CMP-NE-true\" (exp \"S\" (var \"S\")) (exp \"val_1\" (var \"val\")) (exp \"v"
            "al_2\" (var \"val\")) \"%|-%~>%\" (tup (var \"S\") (case \"CMP\" (tup (case \"NE\""
            " (tup)) (sub (var \"val\") (var \"exp\") (var \"val_1\")) (sub (var \"val\") (var "
            "\"exp\") (var \"val_2\")))) (case \"BOOL\" (tup (bool true)))) (if (cmp ne bool (v"
            "ar \"val_1\") (var \"val_2\"))))"

spectec_erratum 2 in Specs.metail on "numbin"
  because "3-primitives.spectec: MOD divides, DIV on int goes through nat, and the int/rat "
          "guards narrow the divisor to nat"
  replacing "(clause (exp \"i_1\" int) (exp \"i_2\" int) (exp (case \"DIV\" (tup))) (exp (case "
            "\"INT\" (tup (var \"i_1\")))) (exp (case \"INT\" (tup (var \"i_2\")))) (case \"INT"
            "\" (tup (cvt nat int (cvt rat nat (bin div rat (cvt int rat (var \"i_1\")) (cvt in"
            "t rat (var \"i_2\"))))))) (if (bin and bool (cmp ne bool (cvt int nat (var \"i_2\""
            ")) (num (nat 0))) (cmp eq bool (cvt int nat (bin mod int (var \"i_1\") (var \"i_2"
            "\"))) (num (nat 0)))))) (clause (exp \"q_1\" rat) (exp \"q_2\" rat) (exp (case \"D"
            "IV\" (tup))) (exp (case \"RAT\" (tup (var \"q_1\")))) (exp (case \"RAT\" (tup (var"
            " \"q_2\")))) (case \"RAT\" (tup (bin div rat (var \"q_1\") (var \"q_2\")))) (if (c"
            "mp ne bool (cvt rat nat (var \"q_2\")) (num (nat 0))))) (clause (exp \"r_1\" real)"
            " (exp \"r_2\" real) (exp (case \"DIV\" (tup))) (exp (case \"REAL\" (tup (var \"r_1"
            "\")))) (exp (case \"REAL\" (tup (var \"r_2\")))) (case \"REAL\" (tup (bin div real"
            " (var \"r_1\") (var \"r_2\")))) (if (cmp ne bool (cvt real nat (var \"r_2\")) (num"
            " (nat 0))))) (clause (exp \"n_1\" nat) (exp \"n_2\" nat) (exp (case \"MOD\" (tup))"
            ") (exp (case \"NAT\" (tup (var \"n_1\")))) (exp (case \"NAT\" (tup (var \"n_2\")))"
            ") (case \"NAT\" (tup (cvt rat nat (bin div rat (cvt nat rat (var \"n_1\")) (cvt na"
            "t rat (var \"n_2\")))))) (if (cmp ne bool (var \"n_2\") (num (nat 0))))) (clause ("
            "exp \"i_1\" int) (exp \"i_2\" int) (exp (case \"MOD\" (tup))) (exp (case \"INT\" ("
            "tup (var \"i_1\")))) (exp (case \"INT\" (tup (var \"i_2\")))) (case \"INT\" (tup ("
            "cvt rat int (bin div rat (cvt int rat (var \"i_1\")) (cvt int rat (var \"i_2\"))))"
            ")) (if (cmp ne bool (cvt int nat (var \"i_2\")) (num (nat 0)))))"
  with      "(clause (exp \"i_1\" int) (exp \"i_2\" int) (exp (case \"DIV\" (tup))) (exp (case "
            "\"INT\" (tup (var \"i_1\")))) (exp (case \"INT\" (tup (var \"i_2\")))) (case \"INT"
            "\" (tup (cvt rat int (bin div rat (cvt int rat (var \"i_1\")) (cvt int rat (var \""
            "i_2\")))))) (if (bin and bool (cmp ne bool (var \"i_2\") (cvt nat int (num (nat 0)"
            "))) (cmp eq bool (bin mod int (var \"i_1\") (var \"i_2\")) (cvt nat int (num (nat "
            "0))))))) (clause (exp \"q_1\" rat) (exp \"q_2\" rat) (exp (case \"DIV\" (tup))) (e"
            "xp (case \"RAT\" (tup (var \"q_1\")))) (exp (case \"RAT\" (tup (var \"q_2\")))) (c"
            "ase \"RAT\" (tup (bin div rat (var \"q_1\") (var \"q_2\")))) (if (cmp ne bool (var"
            " \"q_2\") (cvt nat rat (num (nat 0)))))) (clause (exp \"r_1\" real) (exp \"r_2\" r"
            "eal) (exp (case \"DIV\" (tup))) (exp (case \"REAL\" (tup (var \"r_1\")))) (exp (ca"
            "se \"REAL\" (tup (var \"r_2\")))) (case \"REAL\" (tup (bin div real (var \"r_1\") "
            "(var \"r_2\")))) (if (cmp ne bool (cvt real nat (var \"r_2\")) (num (nat 0))))) (c"
            "lause (exp \"n_1\" nat) (exp \"n_2\" nat) (exp (case \"MOD\" (tup))) (exp (case \""
            "NAT\" (tup (var \"n_1\")))) (exp (case \"NAT\" (tup (var \"n_2\")))) (case \"NAT\""
            " (tup (bin mod nat (var \"n_1\") (var \"n_2\")))) (if (cmp ne bool (var \"n_2\") ("
            "num (nat 0))))) (clause (exp \"i_1\" int) (exp \"i_2\" int) (exp (case \"MOD\" (tu"
            "p))) (exp (case \"INT\" (tup (var \"i_1\")))) (exp (case \"INT\" (tup (var \"i_2\""
            ")))) (case \"INT\" (tup (bin mod int (var \"i_1\") (var \"i_2\")))) (if (cmp ne bo"
            "ol (var \"i_2\") (cvt nat int (num (nat 0))))))"

/-- The two meta-theory errata, in order. -/
noncomputable def metailErrata : List Erratum := [metail.erratum1, metail.erratum2]

/-- `Specs.metail` with both errata applied. -/
noncomputable def metailCorrected : Script :=
  replaceDefs metail.erratum2.corrected (replaceDefs metail.erratum1.corrected Specs.metail)

/-- Both patches apply, and `metailCorrected` is their result. -/
theorem applyErrata_metailErrata :
    applyErrata metailErrata Specs.metail = some metailCorrected := by
  rfl

end Silmaril.Wasm.SpecTec.Meta
