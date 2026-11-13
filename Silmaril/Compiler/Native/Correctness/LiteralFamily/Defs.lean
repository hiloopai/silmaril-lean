module

public import Silmaril.Compiler.Native.Correctness.LiteralEmission.Defs
public import Silmaril.Compiler.Native.Correctness.LiteralTotal.Defs
public import Silmaril.Compiler.Native.Correctness.Literal42.Defs
public import Silmaril.Compiler.Native.TargetCoherence.Defs
public import Silmaril.Compiler.Native.Correctness.LiteralText.Defs
public import Silmaril.Compiler.Native.Correctness.LiteralLoader.Defs
/-! Independently selected canonical signed32 literal inputs. The source syntax,
constructed conversion runtime, primitive LP64 target, freshness, options and
argv are fixed before compilation or behavior. The partial target profile is
not a complete Cerberus Linux implementation. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.LiteralFamily

/-- Reuse the checked constructed runtime; this is not a full upstream runtime. -/
abbrev runtime := Literal42.runtime

def source (number : Int) : Source where
  program := (LiteralEmission.literal number).program
  elaboration := {
    config := Silmaril.Compiler.Native.TargetCoherence.linuxLP64
    runtime := runtime
    freshness := ⟨⟨[]⟩, 100, 1000⟩ }
  options := { opt := some .O0 }
  tag := "literal-linkage"
  commit := "formal-literal-signed32-family"
  implementation := "constructed-conversion-runtime; explicit-linux-lp64-primitive-profile; closed-main-model"
  enumBindings := []
  arguments := ["a.out"]

/-- Membership inspects bounded integer syntax and exact source inputs only. -/
def domain (candidate : Source) : Prop :=
  ∃ number, LiteralEmission.IsInt32 number ∧ candidate = source number

def target (number : Int) : Target :=
  ⟨LiteralEmission.assembly (BitVec.ofInt 64 number), ["a.out"]⟩

/-- Independently derived grammar, local labels and actual encoded layout feed
an explicit deterministic loader. No text-template equality or machine result
is used to admit a load. -/
def Loads (text : String) (arguments : List String) (image : Image) : Prop :=
  ∃ value code,
    Literal42.Text.MainSyntax text (LiteralText.statements value) ∧
    Silmaril.Compiler.Native.Assembly.Local (LiteralText.statements value) ∧
    Silmaril.Compiler.Native.Assembly.Assembles LiteralText.labels 0
      (LiteralText.statements value) code 83 ∧
    arguments = ["a.out"] ∧ image = LiteralLoader.image code

end Silmaril.Compiler.Native.Correctness.LiteralFamily
