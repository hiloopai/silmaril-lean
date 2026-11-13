module

public import Silmaril.Cerberus.Names.Defs
public import Silmaril.Cerberus.Ail.Syntax.Defs

/-! # Ail and typed-Ail names in Silmaril

The Lem names of `Silmaril.Cerberus.Ail.Syntax`, in the format of
`Silmaril.Cerberus.Names.types`: each Lem type as `Module.name`, the Silmaril declaration
that ports it, and every constructor or record field whose Silmaril name differs from its Lem
name. The Lem names are the wire tags that `Silmaril.Cerberus.Ail.Codec` prints and reads.

Lem aliases map to the `abbrev`s that port them and print as their bodies
(`ail_identifier` is `Sym`; `sigma_function_definition` is the pair of a symbol and a
`FunctionDefinition`). The aliases with no Silmaril declaration of their own
(`sigma_declaration`, `sigma_object_definition`, `sigma_static_assertion`,
`sigma_tag_definition`, `sigma_extern_id`, `sigma_cn_*`, `reg`) are products, `Nat` or CN
instances, written out in the fields of `Sigma` and the constructors that use them. The types
shared with Core (`AilSyntax.arithmeticOperator`, `unaryOperator`, `binaryOperator`, the
`Ctype`, `Annot` and `Symbol` types) are in `Silmaril.Cerberus.Names.types`, and the CN types
in `Silmaril.Cerberus.Cabs.Names.types`.
-/

@[expose] public section

namespace Silmaril.Cerberus.Ail.Names

open Silmaril.Cerberus

/-- Every Lem type of the Ail and typed-Ail levels (`export2/schema.json`, levels `ail` and
`tail`) that `Silmaril.Cerberus.Ail.Syntax` ports. -/
def types : List Silmaril.Cerberus.Names.TypeName := [
  ⟨"AilSyntax.ail_identifier", ``Sym, []⟩,
  ⟨"AilSyntax.integerSuffix", ``Ail.IntegerSuffix, [("U", "u"), ("UL", "ul"), ("ULL", "ull"), ("L", "l"), ("LL", "ll")]⟩,
  ⟨"AilSyntax.basis", ``Ail.Basis, [("Octal", "octal"), ("Decimal", "decimal"), ("Hexadecimal", "hexadecimal"), ("Binary", "binary")]⟩,
  ⟨"AilSyntax.integerConstant", ``Ail.IntegerConstant, [("IConstant", "iconstant"), ("IConstantMax", "max"), ("IConstantMin", "min")]⟩,
  ⟨"AilSyntax.floatingSuffix", ``Ail.FloatingSuffix, [("Fsuf_F", "f"), ("Fsuf_L", "l")]⟩,
  ⟨"AilSyntax.floatingConstant", ``Ail.FloatingConstant, []⟩,
  ⟨"AilSyntax.characterPrefix", ``Ail.CharacterPrefix, [("Pref_L", "wide"), ("Pref_u", "utf16"), ("Pref_U", "utf32")]⟩,
  ⟨"AilSyntax.characterConstant", ``Ail.CharacterConstant, []⟩,
  ⟨"AilSyntax.predefinedConstant", ``Ail.PredefinedConstant, [("PConstantFalse", "false_"), ("PConstantTrue", "true_")]⟩,
  ⟨"AilSyntax.encodingPrefix", ``Ail.EncodingPrefix, [("Enc_u8", "utf8"), ("Enc_u", "utf16"), ("Enc_U", "utf32"), ("Enc_L", "wide")]⟩,
  ⟨"AilSyntax.stringLiteral", ``Ail.StringLiteral, []⟩,
  ⟨"AilSyntax.constant", ``Ail.Constant, [("ConstantIndeterminate", "indeterminate"), ("ConstantNull", "null"), ("ConstantInteger", "integer"), ("ConstantFloating", "floating"), ("ConstantCharacter", "character"), ("ConstantArray", "array"), ("ConstantStruct", "struct"), ("ConstantUnion", "union"), ("ConstantPredefined", "predefined")]⟩,
  ⟨"AilSyntax.ail_builtin_atomic", ``Ail.BuiltinAtomic, [("AilBAthread_fence", "threadFence"), ("AilBAstore", "store"), ("AilBAload", "load"), ("AilBAexchange", "exchange"), ("AilBAcompare_exchange_strong", "compareExchangeStrong"), ("AilBAcompare_exchange_weak", "compareExchangeWeak"), ("AilBAfetch_key", "fetchKey")]⟩,
  ⟨"AilSyntax.ail_builtin_linux", ``Ail.BuiltinLinux, [("AilBLfence", "fence"), ("AilBLread", "read"), ("AilBLwrite", "write"), ("AilBLrmw", "rmw")]⟩,
  ⟨"AilSyntax.ail_builtin", ``Ail.Builtin, [("AilBatomic", "atomic"), ("AilBlinux", "linux"), ("AilBcopy_alloc_id", "copyAllocId"), ("AilBCHERI", "cheri")]⟩,
  ⟨"AilSyntax.storageDuration", ``Ail.StorageDuration, [("Static", "static"), ("Thread", "thread"), ("Automatic", "automatic")]⟩,
  ⟨"AilSyntax.bindings", ``Ail.Bindings, []⟩,
  ⟨"AilSyntax.desug_case", ``Ail.DesugCase, [("Desug_forloop", "forloop"), ("Desug_continue", "continue_")]⟩,
  ⟨"AilSyntax.desug_info", ``Ail.DesugInfo, [("is_forloop_body", "isForloopBody"), ("desug_case", "desugCase")]⟩,
  ⟨"AilSyntax.ail_invalid_reason", ``Ail.InvalidReason, [("AilInvalid_desugaring_init_failed", "desugaringInitFailed"), ("AilInvalid_other", "other")]⟩,
  ⟨"GenTypes.genIntegerType", ``Ail.GenIntegerType, [("Concrete", "concrete"), ("SizeT", "sizeT"), ("PtrdiffT", "ptrdiffT"), ("PtraddrT", "ptraddrT"), ("Unknown", "unknown"), ("Promote", "promote"), ("Usual", "usual")]⟩,
  ⟨"GenTypes.genBasicType", ``Ail.GenBasicType, [("GenInteger", "integer"), ("GenFloating", "floating")]⟩,
  ⟨"GenTypes.genType", ``Ail.GenType, [("GenVoid", "void"), ("GenBasic", "basic"), ("GenArray", "array"), ("GenFunction", "function"), ("GenFunctionNoParams", "functionNoParams"), ("GenPointer", "pointer"), ("GenStruct", "struct"), ("GenUnion", "union"), ("GenAtomic", "atomic"), ("GenByte", "byte")]⟩,
  ⟨"GenTypes.genTypeCategory", ``Ail.GenTypeCategory, [("GenLValueType", "lvalue"), ("GenRValueType", "rvalue")]⟩,
  ⟨"AilSyntax.expression_", ``Ail.ExpressionNode, [("AilEunary", "unary"), ("AilEbinary", "binary"), ("AilEassign", "assign"), ("AilEcompoundAssign", "compoundAssign"), ("AilEcond", "cond"), ("AilEcast", "cast"), ("AilEcall", "call"), ("AilEassert", "assert"), ("AilEoffsetof", "offsetof"), ("AilEgeneric", "generic"), ("AilEarray", "array"), ("AilEstruct", "struct"), ("AilEunion", "union"), ("AilEcompound", "compound"), ("AilEmemberof", "memberof"), ("AilEmemberofptr", "memberofptr"), ("AilEbuiltin", "builtin"), ("AilEstr", "str"), ("AilEconst", "const"), ("AilEident", "ident"), ("AilEsizeof", "sizeof"), ("AilEsizeof_expr", "sizeofExpr"), ("AilEalignof", "alignof"), ("AilEannot", "annot"), ("AilEva_start", "vaStart"), ("AilEva_arg", "vaArg"), ("AilEva_copy", "vaCopy"), ("AilEva_end", "vaEnd"), ("AilEprint_type", "printType"), ("AilEbmc_assume", "bmcAssume"), ("AilEreg_load", "regLoad"), ("AilErvalue", "rvalue"), ("AilEarray_decay", "arrayDecay"), ("AilEfunction_decay", "functionDecay"), ("AilEatomic", "atomic"), ("AilElabel_addressGNU", "labelAddressGnu"), ("AilEgcc_statement", "gccStatement"), ("AilEinvalid", "invalid")]⟩,
  ⟨"AilSyntax.generic_association", ``Ail.GenericAssociation, [("AilGAtype", "type_"), ("AilGAdefault", "default")]⟩,
  ⟨"AilSyntax.expression", ``Ail.Expression, [("AnnotatedExpression", "mk")]⟩,
  ⟨"AilSyntax.statement_", ``Ail.StatementNode, [("AilSskip", "skip"), ("AilSexpr", "expr"), ("AilSblock", "block"), ("AilSif", "if_"), ("AilSwhile", "while_"), ("AilSdo", "do_"), ("AilSbreak", "break_"), ("AilScontinue", "continue_"), ("AilSreturnVoid", "returnVoid"), ("AilSreturn", "return_"), ("AilSswitch", "switch"), ("AilScase", "case_"), ("AilScase_rangeGNU", "caseRangeGnu"), ("AilSdefault", "default"), ("AilSlabel", "label"), ("AilSgoto", "goto"), ("AilSdeclaration", "declaration"), ("AilSpar", "par"), ("AilSreg_store", "regStore"), ("AilSmarker", "marker")]⟩,
  ⟨"AilSyntax.statement", ``Ail.Statement, [("desug_info", "desugInfo")]⟩,
  ⟨"AilSyntax.declaration", ``Ail.Declaration, [("Decl_object", "object"), ("Decl_function", "function")]⟩,
  ⟨"AilSyntax.id_kind", ``Ail.IdKind, [("IK_declaration", "declaration"), ("IK_tentative", "tentative"), ("IK_definition", "definition")]⟩,
  ⟨"Cn.cn_namespace", ``Ail.CnNamespace, [("CN_predicate", "predicate"), ("CN_function", "function"), ("CN_lemma", "lemma"), ("CN_fun_spec", "funSpec"), ("CN_datatype_nm", "datatype"), ("CN_constructor", "constructor"), ("CN_vars", "vars"), ("CN_oarg", "oarg"), ("CN_type_nm", "typeName")]⟩,
  ⟨"AilSyntax.sigma_function_definition", ``Ail.FunctionDefinition, []⟩,
  ⟨"AilSyntax.sigma", ``Ail.Sigma, [("object_definitions", "objectDefinitions"), ("function_definitions", "functionDefinitions"), ("static_assertions", "staticAssertions"), ("tag_definitions", "tagDefinitions"), ("extern_idmap", "externIdmap"), ("typedef_attributes", "typedefAttributes"), ("loop_attributes", "loopAttributes"), ("cn_functions", "cnFunctions"), ("cn_lemmata", "cnLemmata"), ("cn_predicates", "cnPredicates"), ("cn_datatypes", "cnDatatypes"), ("cn_decl_specs", "cnDeclSpecs"), ("cn_idents", "cnIdents")]⟩,
  ⟨"AilSyntax.ail_program", ``Ail.Program, []⟩]

theorem types_length : types.length = 35 := by decide

end Silmaril.Cerberus.Ail.Names
