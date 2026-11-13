module

public import Silmaril.Cerberus.Core.Compatibility.Defs

/-! Kernel checks for the qualifier, tag, array and function rules. -/

@[expose] public section
namespace Silmaril.Cerberus.Core

private def intTy : Ctype := .mk [] (.basic (.integer (.signed .int)))
private def longTy : Ctype := .mk [] (.basic (.integer (.signed .long)))
private def ptr (q : Qualifiers) (t : Ctype) : Ctype := .mk [] (.pointer q t)
private def arr (n : Option Int) : Ctype := .mk [] (.array intTy n)
private def fn (ps : List Ctype) (v := false) : Ctype :=
  .mk [] (.function (noQualifiers, intTy) (ps.map (noQualifiers, ·, false)) v)
private def check (a b : Ctype) := (compatible 256 noQualifiers a noQualifiers b).toOption

/-- Tag descriptions do not participate in Lem key equality. -/
theorem compatible_tag_description (fuel n : Nat) (d : Digest)
    (a b : SymbolDescription) :
    compatible (fuel+1) noQualifiers (.mk [] (.struct (.mk d n a)))
      noQualifiers (.mk [] (.struct (.mk d n b))) = .ok true := by
  simp [compatible, compatibleWith, noQualifiers, Mem.Concrete.symbolEq, Sym.key]
  rfl

private theorem compatibility_check_0 : check (ptr noQualifiers intTy) (ptr noQualifiers intTy) = some true := by decide +kernel

private theorem compatibility_check_1 : check (ptr ⟨true,false,false⟩ intTy) (ptr noQualifiers intTy) = some false := by decide +kernel

private theorem compatibility_check_2 : check (ptr noQualifiers intTy) (ptr noQualifiers longTy) = some false := by decide +kernel

private theorem compatibility_check_3 : check (arr none) (arr (some 3)) = some true := by decide +kernel

private theorem compatibility_check_4 : check (arr (some 2)) (arr (some 3)) = some false := by decide +kernel

private theorem compatibility_check_5 : check (fn [intTy]) (fn [intTy,intTy]) = some false := by decide +kernel

private theorem compatibility_check_6 : check (fn [intTy]) (fn [intTy] true) = some false := by decide +kernel

private theorem compatibility_check_7 : check (fn [intTy]) (.mk [] (.functionNoParams (noQualifiers,intTy))) = some true := by decide +kernel

private theorem compatibility_check_8 : check (fn [intTy] true) (.mk [] (.functionNoParams (noQualifiers,intTy))) = some false := by decide +kernel

private theorem compatibility_check_9 : check (fn [intTy]) (.mk [] (.function (noQualifiers,intTy) [(⟨true,false,false⟩,intTy,true)] false)) = some true := by decide +kernel

private theorem compatibility_check_10 : check (.mk [] (.union (.mk ⟨[100]⟩ 1 .none)))
  (.mk [] (.union (.mk ⟨[100]⟩ 1 (.id "other")))) = some true := by decide +kernel

private theorem compatibility_check_11 : check (.mk [] (.struct (.mk ⟨[100]⟩ 1 .none)))
  (.mk [] (.struct (.mk ⟨[100]⟩ 2 .none))) = some false := by decide +kernel

private theorem compatibility_check_12 : check (.mk [] (.atomic intTy)) (.mk [] (.atomic intTy)) = some true := by decide +kernel

private theorem compatibility_check_13 : check (.mk [] (.basic (.integer .size)))
  (.mk [] (.basic (.integer (.unsigned .long)))) = some true := by decide +kernel

private theorem compatibility_check_14 : check longTy (.mk [] (.basic (.integer (.signed .longLong)))) = some false := by decide +kernel

private theorem compatibility_check_15 : check (.mk [] (.basic (.integer .char)))
  (.mk [] (.basic (.integer (.signed .ichar)))) = some false := by decide +kernel

private theorem compatibility_check_16 : (compatible 0 noQualifiers intTy noQualifiers intTy).toOption = none := by decide +kernel

end Silmaril.Cerberus.Core
