module

public import Silmaril.Cerberus.Names.Defs
public import Silmaril.Cerberus.Cabs.Syntax.Defs

/-! # Cabs and CN names in Silmaril

The Lem names of `Silmaril.Cerberus.Cabs.Syntax`, in the format of
`Silmaril.Cerberus.Names.types`: each Lem type as `Module.name`, the Silmaril
declaration that ports it, and every constructor or record field whose Silmaril name
differs from its Lem name. The Lem names are the wire tags that
`Silmaril.Cerberus.Cabs.Codec` prints and reads. The four Lem aliases
(`cabs_integer_constant`, `cabs_floating_constant`, `cabs_character_constant`,
`cabs_string_literal`) map to `abbrev`s and print as their bodies.
-/

@[expose] public section

namespace Silmaril.Cerberus.Cabs.Names

open Silmaril.Cerberus

/-- Every Lem type of the Cabs level (`export2/schema.json`, level `cabs`), CN first. -/
def types : List Silmaril.Cerberus.Names.TypeName := [
  ⟨"Cabs.cabs_integer_suffix", ``Cabs.IntegerSuffix, [("CabsSuffix_U", "u"), ("CabsSuffix_UL", "ul"), ("CabsSuffix_ULL", "ull"), ("CabsSuffix_L", "l"), ("CabsSuffix_LL", "ll")]⟩,
  ⟨"Cabs.cabs_integer_constant", ``Cabs.IntegerConstant, []⟩,
  ⟨"Cabs.cabs_floating_suffix", ``Cabs.FloatingSuffix, [("CabsFloatingSuffix_F", "f"), ("CabsFloatingSuffix_L", "l")]⟩,
  ⟨"Cabs.cabs_floating_constant", ``Cabs.FloatingConstant, []⟩,
  ⟨"Cabs.cabs_character_prefix", ``Cabs.CharacterPrefix, [("CabsPrefix_L", "wide"), ("CabsPrefix_u", "utf16"), ("CabsPrefix_U", "utf32")]⟩,
  ⟨"Cabs.cabs_character_constant", ``Cabs.CharacterConstant, []⟩,
  ⟨"Cabs.cabs_constant", ``Cabs.Constant, [("CabsInteger_const", "integer"), ("CabsFloating_const", "floating"), ("CabsCharacter_const", "character")]⟩,
  ⟨"Cabs.cabs_encoding_prefix", ``Cabs.EncodingPrefix, [("CabsEncPrefix_u8", "utf8"), ("CabsEncPrefix_u", "utf16"), ("CabsEncPrefix_U", "utf32"), ("CabsEncPrefix_L", "wide")]⟩,
  ⟨"Cabs.cabs_string_literal", ``Cabs.StringLiteral, []⟩,
  ⟨"Cabs.cabs_expression_", ``Cabs.ExpressionNode, [("CabsEident", "ident"), ("CabsEconst", "const"), ("CabsEstring", "string"), ("CabsEgeneric", "generic"), ("CabsEsubscript", "subscript"), ("CabsEcall", "call"), ("CabsEmemberof", "memberof"), ("CabsEmemberofptr", "memberofptr"), ("CabsEpostincr", "postincr"), ("CabsEpostdecr", "postdecr"), ("CabsEcompound", "compound"), ("CabsEpreincr", "preincr"), ("CabsEpredecr", "predecr"), ("CabsEunary", "unary"), ("CabsEsizeof_expr", "sizeofExpr"), ("CabsEsizeof_type", "sizeofType"), ("CabsEalignof", "alignof"), ("CabsEcast", "cast"), ("CabsEbinary", "binary"), ("CabsEcond", "cond"), ("CabsEassign", "assign"), ("CabsEcomma", "comma"), ("CabsEassert", "assert"), ("CabsEoffsetof", "offsetof"), ("CabsEva_start", "vaStart"), ("CabsEva_copy", "vaCopy"), ("CabsEva_arg", "vaArg"), ("CabsEva_end", "vaEnd"), ("CabsEprint_type", "printType"), ("CabsEbmc_assume", "bmcAssume"), ("CabsElabel_addressGNU", "labelAddressGnu"), ("CabsEgcc_statement", "gccStatement"), ("CabsEcondGNU", "condGnu"), ("CabsEbuiltinGNU", "builtinGnu")]⟩,
  ⟨"Cabs.gnu_builtin_function", ``Cabs.GnuBuiltinFunction, [("GNUbuiltin_types_compatible_p", "typesCompatibleP"), ("GNUbuiltin_choose_expr", "chooseExpr")]⟩,
  ⟨"Cabs.cabs_expression", ``Cabs.Expression, [("CabsExpression", "mk")]⟩,
  ⟨"Cabs.cabs_generic_association", ``Cabs.GenericAssociation, [("GA_type", "type_"), ("GA_default", "default")]⟩,
  ⟨"Cabs.cabs_unary_operator", ``Cabs.UnaryOperator, [("CabsAddress", "address"), ("CabsIndirection", "indirection"), ("CabsPlus", "plus"), ("CabsMinus", "minus"), ("CabsBnot", "bnot"), ("CabsNot", "not")]⟩,
  ⟨"Cabs.cabs_binary_operator", ``Cabs.BinaryOperator, [("CabsMul", "mul"), ("CabsDiv", "div"), ("CabsMod", "mod"), ("CabsAdd", "add"), ("CabsSub", "sub"), ("CabsShl", "shl"), ("CabsShr", "shr"), ("CabsLt", "lt"), ("CabsGt", "gt"), ("CabsLe", "le"), ("CabsGe", "ge"), ("CabsEq", "eq"), ("CabsNe", "ne"), ("CabsBand", "band"), ("CabsBxor", "bxor"), ("CabsBor", "bor"), ("CabsAnd", "and"), ("CabsOr", "or")]⟩,
  ⟨"Cabs.cabs_assignment_operator", ``Cabs.AssignmentOperator, [("Assign", "assign"), ("Assign_Mul", "mul"), ("Assign_Div", "div"), ("Assign_Mod", "mod"), ("Assign_Add", "add"), ("Assign_Sub", "sub"), ("Assign_Shl", "shl"), ("Assign_Shr", "shr"), ("Assign_Band", "band"), ("Assign_Bxor", "bxor"), ("Assign_Bor", "bor")]⟩,
  ⟨"Cabs.cabs_declaration", ``Cabs.Declaration, [("Declaration_base", "base"), ("Declaration_static_assert", "staticAssert")]⟩,
  ⟨"Cabs.specifiers", ``Cabs.Specifiers, [("storage_classes", "storageClasses"), ("type_specifiers", "typeSpecifiers"), ("type_qualifiers", "typeQualifiers"), ("function_specifiers", "functionSpecifiers"), ("alignment_specifiers", "alignmentSpecifiers")]⟩,
  ⟨"Cabs.init_declarator", ``Cabs.InitDeclarator, [("InitDecl", "mk")]⟩,
  ⟨"Cabs.storage_class_specifier", ``Cabs.StorageClassSpecifier, [("SC_typedef", "typedef"), ("SC_extern", "extern"), ("SC_static", "static"), ("SC_Thread_local", "threadLocal"), ("SC_auto", "auto"), ("SC_register", "register")]⟩,
  ⟨"Cabs.cabs_type_specifier_", ``Cabs.TypeSpecifierNode, [("TSpec_void", "void"), ("TSpec_char", "char"), ("TSpec_short", "short"), ("TSpec_int", "int"), ("TSpec_long", "long"), ("TSpec_float", "float"), ("TSpec_double", "double"), ("TSpec_signed", "signed"), ("TSpec_unsigned", "unsigned"), ("TSpec_Bool", "bool"), ("TSpec_Complex", "complex"), ("TSpec_Atomic", "atomic"), ("TSpec_struct", "struct"), ("TSpec_union", "union"), ("TSpec_enum", "enum"), ("TSpec_name", "name"), ("TSpec_typeof_expr", "typeofExpr"), ("TSpec_typeof_type", "typeofType")]⟩,
  ⟨"Cabs.cabs_type_specifier", ``Cabs.TypeSpecifier, [("TSpec", "mk")]⟩,
  ⟨"Cabs.struct_declaration", ``Cabs.StructDeclaration, [("Struct_declaration", "member"), ("Struct_assert", "staticAssert")]⟩,
  ⟨"Cabs.struct_declarator", ``Cabs.StructDeclarator, [("SDecl_simple", "simple"), ("SDecl_bitfield", "bitfield")]⟩,
  ⟨"Cabs.cabs_type_qualifier", ``Cabs.TypeQualifier, [("Q_const", "const"), ("Q_restrict", "restrict"), ("Q_volatile", "volatile"), ("Q_Atomic", "atomic")]⟩,
  ⟨"Cabs.function_specifier", ``Cabs.FunctionSpecifier, [("FS_inline", "inline"), ("FS_Noreturn", "noreturn")]⟩,
  ⟨"Cabs.alignment_specifier", ``Cabs.AlignmentSpecifier, [("AS_type", "type_"), ("AS_expr", "expr")]⟩,
  ⟨"Cabs.declarator", ``Cabs.Declarator, [("Declarator", "mk")]⟩,
  ⟨"Cabs.direct_declarator", ``Cabs.DirectDeclarator, [("DDecl_identifier", "identifier"), ("DDecl_declarator", "declarator"), ("DDecl_array", "array"), ("DDecl_function", "function")]⟩,
  ⟨"Cabs.array_declarator", ``Cabs.ArrayDeclarator, [("ADecl", "mk")]⟩,
  ⟨"Cabs.array_declarator_size", ``Cabs.ArrayDeclaratorSize, [("ADeclSize_expression", "expression"), ("ADeclSize_asterisk", "asterisk")]⟩,
  ⟨"Cabs.pointer_declarator", ``Cabs.PointerDeclarator, [("PDecl", "mk")]⟩,
  ⟨"Cabs.parameter_type_list", ``Cabs.ParameterTypeList, [("Params", "mk")]⟩,
  ⟨"Cabs.parameter_declaration", ``Cabs.ParameterDeclaration, [("PDeclaration_decl", "declarator"), ("PDeclaration_abs_decl", "abstract")]⟩,
  ⟨"Cabs.type_name", ``Cabs.TypeName, [("Type_name", "mk")]⟩,
  ⟨"Cabs.abstract_declarator", ``Cabs.AbstractDeclarator, [("AbsDecl_pointer", "pointer"), ("AbsDecl_direct", "direct")]⟩,
  ⟨"Cabs.direct_abstract_declarator", ``Cabs.DirectAbstractDeclarator, [("DAbs_abs_declarator", "abstract"), ("DAbs_array", "array"), ("DAbs_function", "function")]⟩,
  ⟨"Cabs.initializer_", ``Cabs.Initializer, [("Init_expr", "expr"), ("Init_list", "list")]⟩,
  ⟨"Cabs.designator", ``Cabs.Designator, [("Desig_array", "array"), ("Desig_member", "member")]⟩,
  ⟨"Cabs.static_assert_declaration", ``Cabs.StaticAssertDeclaration, [("Static_assert", "mk")]⟩,
  ⟨"Cabs.cabs_statement_", ``Cabs.StatementNode, [("CabsSlabel", "label"), ("CabsScase", "case_"), ("CabsSdefault", "default"), ("CabsSblock", "block"), ("CabsSdecl", "decl"), ("CabsSnull", "null"), ("CabsSexpr", "expr"), ("CabsSif", "if_"), ("CabsSswitch", "switch"), ("CabsSwhile", "while_"), ("CabsSdo", "do_"), ("CabsSfor", "for_"), ("CabsSgoto", "goto"), ("CabsScontinue", "continue_"), ("CabsSbreak", "break_"), ("CabsSreturn", "return_"), ("CabsSpar", "par"), ("CabsSasm", "asm"), ("CabsScaseGNU", "caseRangeGnu"), ("CabsSmarker", "marker")]⟩,
  ⟨"Cabs.cabs_statement", ``Cabs.Statement, [("CabsStatement", "mk")]⟩,
  ⟨"Cabs.for_clause", ``Cabs.ForClause, [("FC_expr", "expr"), ("FC_decl", "decl")]⟩,
  ⟨"Cabs.translation_unit", ``Cabs.TranslationUnit, [("TUnit", "mk")]⟩,
  ⟨"Cabs.external_declaration", ``Cabs.ExternalDeclaration, [("EDecl_func", "func"), ("EDecl_decl", "decl"), ("EDecl_magic", "magic"), ("EDecl_funcCN", "funcCn"), ("EDecl_lemmaCN", "lemmaCn"), ("EDecl_predCN", "predCn"), ("EDecl_datatypeCN", "datatypeCn"), ("EDecl_type_synCN", "typeSynCn"), ("EDecl_fun_specCN", "funSpecCn")]⟩,
  ⟨"Cabs.function_definition", ``Cabs.FunctionDefinition, [("FunDef", "mk")]⟩,
  ⟨"Cn.sign", ``Cn.Sign, [("CN_unsigned", "unsigned"), ("CN_signed", "signed")]⟩,
  ⟨"Cn.cn_base_type", ``Cn.BaseType, [("CN_unit", "unit"), ("CN_bool", "bool"), ("CN_integer", "integer"), ("CN_bits", "bits"), ("CN_real", "real"), ("CN_loc", "loc"), ("CN_alloc_id", "allocId"), ("CN_struct", "struct"), ("CN_record", "record"), ("CN_datatype", "datatype"), ("CN_map", "map"), ("CN_list", "list"), ("CN_tuple", "tuple"), ("CN_set", "set"), ("CN_user_type_name", "userTypeName"), ("CN_c_typedef_name", "cTypedefName")]⟩,
  ⟨"Cn.cn_binop", ``Cn.Binop, [("CN_add", "add"), ("CN_sub", "sub"), ("CN_mul", "mul"), ("CN_div", "div"), ("CN_mod", "mod"), ("CN_equal", "equal"), ("CN_inequal", "inequal"), ("CN_lt", "lt"), ("CN_le", "le"), ("CN_gt", "gt"), ("CN_ge", "ge"), ("CN_or", "or"), ("CN_and", "and"), ("CN_implies", "implies"), ("CN_map_get", "mapGet"), ("CN_band", "band"), ("CN_bor", "bor"), ("CN_bxor", "bxor")]⟩,
  ⟨"Cn.cn_c_kind", ``Cn.CKind, [("C_kind_var", "var"), ("C_kind_enum", "enum")]⟩,
  ⟨"Cn.cn_const", ``Cn.Const, [("CNConst_NULL", "null"), ("CNConst_integer", "integer"), ("CNConst_bits", "bits"), ("CNConst_bool", "bool"), ("CNConst_unit", "unit")]⟩,
  ⟨"Cn.cn_pat_", ``Cn.PatNode, [("CNPat_sym", "sym"), ("CNPat_wild", "wild"), ("CNPat_constructor", "constructor")]⟩,
  ⟨"Cn.cn_pat", ``Cn.Pat, [("CNPat", "mk")]⟩,
  ⟨"Cn.cn_expr_", ``Cn.ExprNode, [("CNExpr_const", "const"), ("CNExpr_var", "var"), ("CNExpr_list", "list"), ("CNExpr_memberof", "memberof"), ("CNExpr_arrow", "arrow"), ("CNExpr_record", "record"), ("CNExpr_struct", "struct"), ("CNExpr_memberupdates", "memberUpdates"), ("CNExpr_arrayindexupdates", "arrayIndexUpdates"), ("CNExpr_binop", "binop"), ("CNExpr_sizeof", "sizeof"), ("CNExpr_offsetof", "offsetof"), ("CNExpr_membershift", "memberShift"), ("CNExpr_addr", "addr"), ("CNExpr_cast", "cast"), ("CNExpr_array_shift", "arrayShift"), ("CNExpr_call", "call"), ("CNExpr_cons", "cons"), ("CNExpr_each", "each"), ("CNExpr_let", "let_"), ("CNExpr_match", "match_"), ("CNExpr_ite", "ite"), ("CNExpr_good", "good"), ("CNExpr_deref", "deref"), ("CNExpr_value_of_c_atom", "valueOfCAtom"), ("CNExpr_unchanged", "unchanged"), ("CNExpr_at_env", "atEnv"), ("CNExpr_not", "not"), ("CNExpr_negate", "negate"), ("CNExpr_default", "default"), ("CNExpr_bnot", "bnot")]⟩,
  ⟨"Cn.cn_expr", ``Cn.Expr, [("CNExpr", "mk")]⟩,
  ⟨"Cn.cn_pred", ``Cn.Pred, [("CN_owned", "owned"), ("CN_block", "block"), ("CN_named", "named")]⟩,
  ⟨"Cn.cn_resource", ``Cn.Resource, [("CN_pred", "pred"), ("CN_each", "each")]⟩,
  ⟨"Cn.cn_assertion", ``Cn.Assertion, [("CN_assert_exp", "expr"), ("CN_assert_qexp", "quantified")]⟩,
  ⟨"Cn.cn_condition", ``Cn.Condition, [("CN_cletResource", "letResource"), ("CN_cletExpr", "letExpr"), ("CN_cconstr", "constraint")]⟩,
  ⟨"Cn.cn_clause", ``Cn.Clause, [("CN_letResource", "letResource"), ("CN_letExpr", "letExpr"), ("CN_assert", "assert"), ("CN_return", "return_")]⟩,
  ⟨"Cn.cn_clauses", ``Cn.Clauses, [("CN_clause", "clause"), ("CN_if", "if_")]⟩,
  ⟨"Cn.cn_acc_func", ``Cn.AccFunc, [("CN_accesses", "accesses"), ("CN_mk_function", "mkFunction")]⟩,
  ⟨"Cn.cn_func_spec", ``Cn.FuncSpec, [("cn_func_trusted", "trusted"), ("cn_func_acc_func", "accFunc"), ("cn_func_requires", "requires"), ("cn_func_ensures", "ensures")]⟩,
  ⟨"Cn.cn_decl_spec", ``Cn.DeclSpec, [("cn_decl_loc", "loc"), ("cn_decl_name", "name"), ("cn_decl_args", "args"), ("cn_func_spec", "funcSpec")]⟩,
  ⟨"Cn.cn_function", ``Cn.Function, [("cn_func_magic_loc", "magicLoc"), ("cn_func_loc", "loc"), ("cn_func_name", "name"), ("cn_func_attrs", "attrs"), ("cn_func_args", "args"), ("cn_func_body", "body"), ("cn_func_return_bty", "returnType")]⟩,
  ⟨"Cn.cn_lemma", ``Cn.Lemma, [("cn_lemma_magic_loc", "magicLoc"), ("cn_lemma_loc", "loc"), ("cn_lemma_name", "name"), ("cn_lemma_args", "args"), ("cn_lemma_requires", "requires"), ("cn_lemma_ensures", "ensures")]⟩,
  ⟨"Cn.cn_predicate", ``Cn.Predicate, [("cn_pred_magic_loc", "magicLoc"), ("cn_pred_loc", "loc"), ("cn_pred_name", "name"), ("cn_pred_attrs", "attrs"), ("cn_pred_output", "output"), ("cn_pred_iargs", "iargs"), ("cn_pred_clauses", "clauses")]⟩,
  ⟨"Cn.cn_datatype", ``Cn.Datatype, [("cn_dt_magic_loc", "magicLoc"), ("cn_dt_loc", "loc"), ("cn_dt_name", "name"), ("cn_dt_cases", "cases")]⟩,
  ⟨"Cn.cn_type_synonym", ``Cn.TypeSynonym, [("cn_tysyn_magic_loc", "magicLoc"), ("cn_tysyn_loc", "loc"), ("cn_tysyn_name", "name"), ("cn_tysyn_rhs", "rhs")]⟩]

theorem types_length : types.length = 69 := by decide

end Silmaril.Cerberus.Cabs.Names
