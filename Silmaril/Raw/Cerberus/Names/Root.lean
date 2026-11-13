module

public import Silmaril.Cerberus.Core.Syntax.Defs

/-! # Cerberus names in Silmaril

The one map from Cerberus's names to the Silmaril names of the port. The port uses
Silmaril's conventions: types are `UpperCamelCase` in the `Silmaril.Cerberus`
namespace (Core's own types in `Silmaril.Cerberus.Core`), constructors and fields
are `lowerCamelCase`, a Lean keyword gets a trailing `_`, a single-constructor type
has the constructor `mk`, and Lem's unannotated `generic_x_` shapes are `XNode`.
The undefined-behaviour catalogue keeps its Cerberus names.

Each entry names a Lem type as `sil cerberus` resolves it (`Module.name`), the
Silmaril declaration that ports it, and every constructor or record field whose
Silmaril name differs from its Lem name. Names not listed are unchanged. A Lem
abbreviation maps to the declaration it abbreviates, and a type that Lem leaves
abstract maps to the declaration that stands for it. The Lem names are also the
constructor tags of the wire format, so a decoder reads tags through this map.
-/

@[expose] public section

namespace Silmaril.Cerberus.Names

/-- A Lem type and the Silmaril declaration that ports it. -/
structure TypeName where
  /-- The Lem type, as `Module.name`. -/
  cerberus : String
  /-- The Silmaril declaration. -/
  silmaril : Lean.Name
  /-- Constructors or record fields renamed from their Lem name, as `(Lem, Silmaril)`. -/
  renames : List (String × String)

/-- Every Lem type the port covers, in the source order of `sil cerberus`. -/
def types : List TypeName := [
  ⟨"Loc.t", ``Loc, []⟩,
  ⟨"Symbol.identifier", ``Identifier, [
      ("Identifier", "mk")]⟩,
  ⟨"Symbol.digest", ``Digest, []⟩,
  ⟨"Symbol.symbol_description", ``SymbolDescription, [
      ("SD_None", "none"), ("SD_unnamed_tag", "unnamedTag"), ("SD_Id", "id"),
      ("SD_CN_Id", "cnId"), ("SD_ObjectAddress", "objectAddress"), ("SD_Return", "return_"),
      ("SD_FunArgValue", "funArgValue"), ("SD_FunArg", "funArg")]⟩,
  ⟨"Symbol.sym", ``Sym, [
      ("Symbol", "mk")]⟩,
  ⟨"Symbol.prefix", ``Prefix, [
      ("PrefSource", "source"), ("PrefFunArg", "funArg"),
      ("PrefStringLiteral", "stringLiteral"), ("PrefCompoundLiteral", "compoundLiteral"),
      ("PrefMalloc", "malloc"), ("PrefTemporaryLifetime", "temporaryLifetime"),
      ("PrefOther", "other")]⟩,
  ⟨"IntegerType.integerBaseType", ``IntegerBaseType, [
      ("Ichar", "ichar"), ("Short", "short"), ("Int_", "int"), ("Long", "long"),
      ("LongLong", "longLong"), ("IntN_t", "intN"), ("Int_leastN_t", "intLeastN"),
      ("Int_fastN_t", "intFastN"), ("Intmax_t", "intmax"), ("Intptr_t", "intptr")]⟩,
  ⟨"IntegerType.integerType", ``IntegerType, [
      ("Char", "char"), ("Bool", "bool"), ("Signed", "signed"), ("Unsigned", "unsigned"),
      ("Enum", "enum"), ("Wchar_t", "wchar"), ("Wint_t", "wint"), ("Size_t", "size"),
      ("Ptrdiff_t", "ptrdiff"), ("Ptraddr_t", "ptraddr")]⟩,
  ⟨"Annot.bmc_annot", ``BmcAnnot, [
      ("Abmc_id", "id")]⟩,
  ⟨"Annot.attribute", ``Attribute, [
      ("attr_ns", "ns"), ("attr_id", "id"), ("attr_args", "args")]⟩,
  ⟨"Annot.attributes", ``Attributes, [
      ("Attrs", "mk")]⟩,
  ⟨"Annot.loop_id", ``LoopId, []⟩,
  ⟨"Annot.label_annot", ``LabelAnnot, [
      ("LAloop", "loop"), ("LAloop_continue", "loopContinue"), ("LAloop_break", "loopBreak"),
      ("LAreturn", "return_"), ("LAswitch", "switch"), ("LAcase", "case_"),
      ("LAdefault", "default"), ("LAactual_label", "actualLabel")]⟩,
  ⟨"Annot.cerb_attribute", ``CerbAttribute, [
      ("ACerb_with_address", "withAddress"), ("ACerb_hidden", "hidden")]⟩,
  ⟨"Annot.value_annot", ``ValueAnnot, [
      ("Ainteger", "integer")]⟩,
  ⟨"Annot.annot", ``Annot, [
      ("Astd", "std"), ("Aloc", "loc"), ("Auid", "uid"), ("Amarker", "marker"),
      ("Amarker_object_types", "markerObjectTypes"), ("Abmc", "bmc"), ("Aattrs", "attrs"),
      ("Atypedef", "typedef"), ("Alabel", "label"), ("Acerb", "cerb"), ("Avalue", "value"),
      ("Ainlined_label", "inlinedLabel"), ("Astmt", "stmt"), ("Aexpr", "expr")]⟩,
  ⟨"Annot.loop_attribute", ``LoopAttribute, [
      ("marker_id", "markerId"), ("loc_condition", "conditionLoc"), ("loc_loop", "loopLoc")]⟩,
  ⟨"Annot.loop_attributes", ``LoopAttributes, []⟩,
  ⟨"Ctype.realFloatingType", ``RealFloatingType, [
      ("Float", "float"), ("Double", "double"), ("LongDouble", "longDouble")]⟩,
  ⟨"Ctype.floatingType", ``FloatingType, [
      ("RealFloating", "realFloating")]⟩,
  ⟨"Ctype.basicType", ``BasicType, [
      ("Integer", "integer"), ("Floating", "floating")]⟩,
  ⟨"Ctype.qualifiers", ``Qualifiers, []⟩,
  ⟨"Ctype.ctype_", ``CtypeNode, [
      ("Void", "void"), ("Basic", "basic"), ("Array", "array"), ("Function", "function"),
      ("FunctionNoParams", "functionNoParams"), ("Pointer", "pointer"), ("Atomic", "atomic"),
      ("Struct", "struct"), ("Union", "union"), ("Byte", "byte")]⟩,
  ⟨"Ctype.ctype", ``Ctype, [
      ("Ctype", "mk")]⟩,
  ⟨"Ctype.flexible_array_member", ``FlexibleArrayMember, [
      ("FlexibleArrayMember", "mk")]⟩,
  ⟨"Ctype.alignment", ``Alignment, [
      ("AlignInteger", "integer"), ("AlignType", "ctype")]⟩,
  ⟨"Ctype.tag_definition", ``TagDefinition, [
      ("StructDef", "struct"), ("UnionDef", "union")]⟩,
  ⟨"AilSyntax.arithmeticOperator", ``ArithmeticOperator, [
      ("Mul", "mul"), ("Div", "div"), ("Mod", "mod"), ("Add", "add"), ("Sub", "sub"),
      ("Shl", "shl"), ("Shr", "shr"), ("Band", "band"), ("Bxor", "bxor"), ("Bor", "bor")]⟩,
  ⟨"AilSyntax.unaryOperator", ``UnaryOperator, [
      ("Plus", "plus"), ("Minus", "minus"), ("Bnot", "bnot"), ("Address", "address"),
      ("Indirection", "indirection"), ("PostfixIncr", "postfixIncr"),
      ("PostfixDecr", "postfixDecr")]⟩,
  ⟨"AilSyntax.binaryOperator", ``BinaryOperator, [
      ("Arithmetic", "arithmetic"), ("Comma", "comma"), ("And", "and"), ("Or", "or"),
      ("Lt", "lt"), ("Gt", "gt"), ("Le", "le"), ("Ge", "ge"), ("Eq", "eq"), ("Ne", "ne")]⟩,
  ⟨"Cmm_csem.memory_order", ``MemoryOrder, [
      ("NA", "na"), ("Seq_cst", "seqCst"), ("Relaxed", "relaxed"), ("Release", "release"),
      ("Acquire", "acquire"), ("Consume", "consume"), ("Acq_rel", "acqRel")]⟩,
  ⟨"Linux.linux_memory_order", ``LinuxMemoryOrder, [
      ("Once", "once"), ("LAcquire", "acquire"), ("LRelease", "release"), ("Rmb", "rmb"),
      ("Wmb", "wmb"), ("Mb", "mb"), ("RbDep", "rbDep"), ("RcuLock", "rcuLock"),
      ("RcuUnlock", "rcuUnlock"), ("SyncRcu", "syncRcu")]⟩,
  ⟨"Undefined.unspecified_ub_context", ``UnspecifiedUbContext, []⟩,
  ⟨"Undefined.undefined_by_omission", ``UndefinedByOmission, []⟩,
  ⟨"Undefined.undefined_behaviour", ``UndefinedBehaviour, []⟩,
  ⟨"Mem_common.thread_id", ``ThreadId, []⟩,
  ⟨"Mem_common.derivecap_op", ``DeriveCapOp, [
      ("DCunary", "unary"), ("DCbinary", "binary")]⟩,
  ⟨"Mem_common.pure_memop", ``PureMemOp, [
      ("DeriveCap", "deriveCap"), ("CapAssignValue", "capAssignValue"),
      ("Ptr_tIntValue", "ptrTIntValue"), ("ByteFromInt", "byteFromInt"),
      ("IntFromByte", "intFromByte")]⟩,
  ⟨"Mem_common.generic_memop", ``MemOp, [
      ("PtrEq", "ptrEq"), ("PtrNe", "ptrNe"), ("PtrLt", "ptrLt"), ("PtrGt", "ptrGt"),
      ("PtrLe", "ptrLe"), ("PtrGe", "ptrGe"), ("Ptrdiff", "ptrdiff"),
      ("IntFromPtr", "intFromPtr"), ("PtrFromInt", "ptrFromInt"),
      ("PtrValidForDeref", "ptrValidForDeref"), ("PtrWellAligned", "ptrWellAligned"),
      ("PtrArrayShift", "ptrArrayShift"), ("PtrMemberShift", "ptrMemberShift"),
      ("Memcpy", "memcpy"), ("Memcmp", "memcmp"), ("Realloc", "realloc"),
      ("Va_start", "vaStart"), ("Va_copy", "vaCopy"), ("Va_arg", "vaArg"), ("Va_end", "vaEnd"),
      ("Copy_alloc_id", "copyAllocId"), ("CHERI_intrinsic", "cheriIntrinsic")]⟩,
  ⟨"Mem_common.mem_constraint", ``MemConstraint, [
      ("MC_empty", "empty"), ("MC_eq", "eq"), ("MC_le", "le"), ("MC_lt", "lt"),
      ("MC_in_device", "inDevice"), ("MC_or", "or"), ("MC_conj", "conj"), ("MC_not", "not")]⟩,
  ⟨"Mem.pointer_value", ``MemoryModel.PointerValue, []⟩,
  ⟨"Mem.integer_value", ``MemoryModel.IntegerValue, []⟩,
  ⟨"Mem.floating_value", ``MemoryModel.FloatingValue, []⟩,
  ⟨"Mem.mem_value", ``MemoryModel.MemValue, []⟩,
  ⟨"Mem.mem_iv_constraint", ``IvConstraint, []⟩,
  ⟨"Mem.footprint", ``MemoryModel.Footprint, []⟩,
  ⟨"Implementation.implementation_constant", ``ImplementationConstant, [
      ("Environment__startup_name", "environmentStartupName"),
      ("Environment__startup_type", "environmentStartupType"),
      ("Characters__bits_in_byte", "charactersBitsInByte"),
      ("Characters__execution_character_set_values", "charactersExecutionCharacterSetValues"),
      ("Characters__TODO1", "charactersTodo1"), ("Characters__TODO2", "charactersTodo2"),
      ("Characters__plain_char_is_signed", "charactersPlainCharIsSigned"),
      ("Characters__TODO3", "charactersTodo3"), ("Characters__TODO4", "charactersTodo4"),
      ("Characters__TODO5", "charactersTodo5"), ("Characters__TODO6", "charactersTodo6"),
      ("Characters__TODO7", "charactersTodo7"), ("Characters__TODO8", "charactersTodo8"),
      ("Characters__TODO9", "charactersTodo9"), ("Characters__TODO10", "charactersTodo10"),
      ("Integer__encode", "integerEncode"), ("Integer__decode", "integerDecode"),
      ("Integer__conv_nonrepresentable_signed_integer", "integerConvNonrepresentableSignedInteger"),
      ("Sizeof", "sizeof"), ("Alignof", "alignof"),
      ("SHR_signed_negative", "shrSignedNegative"),
      ("Bitwise_complement", "bitwiseComplement"),
      ("Plain_bitfield_sign", "plainBitfieldSign"),
      ("Bitfield_other_types", "bitfieldOtherTypes"),
      ("Atomic_bitfield_permitted", "atomicBitfieldPermitted"), ("Ctype_min", "ctypeMin"),
      ("Ctype_max", "ctypeMax"), ("BuiltinFunction", "builtinFunction")]⟩,
  ⟨"Core.core_object_type", ``Core.ObjectType, [
      ("OTy_integer", "integer"), ("OTy_floating", "floating"), ("OTy_pointer", "pointer"),
      ("OTy_array", "array"), ("OTy_struct", "struct"), ("OTy_union", "union")]⟩,
  ⟨"Core.core_base_type", ``Core.BaseType, [
      ("BTy_unit", "unit"), ("BTy_boolean", "boolean"), ("BTy_ctype", "ctype"),
      ("BTy_list", "list"), ("BTy_tuple", "tuple"), ("BTy_object", "object"),
      ("BTy_loaded", "loaded"), ("BTy_storable", "storable")]⟩,
  ⟨"Core.binop", ``Core.BinOp, [
      ("OpAdd", "add"), ("OpSub", "sub"), ("OpMul", "mul"), ("OpDiv", "div"),
      ("OpRem_t", "remT"), ("OpRem_f", "remF"), ("OpExp", "exp"), ("OpEq", "eq"),
      ("OpGt", "gt"), ("OpLt", "lt"), ("OpGe", "ge"), ("OpLe", "le"), ("OpAnd", "and"),
      ("OpOr", "or")]⟩,
  ⟨"Core.iop", ``Core.IntOp, [
      ("IOpAdd", "add"), ("IOpSub", "sub"), ("IOpMul", "mul"), ("IOpShl", "shl"),
      ("IOpShr", "shr"), ("IOpDiv", "div"), ("IOpRem_t", "remT")]⟩,
  ⟨"Core.polarity", ``Core.Polarity, [
      ("Pos", "pos"), ("Neg", "neg")]⟩,
  ⟨"Core.generic_name", ``Core.Name, [
      ("Sym", "sym"), ("Impl", "impl")]⟩,
  ⟨"Core.object_value", ``Core.ObjectValue, [
      ("OVinteger", "integer"), ("OVfloating", "floating"), ("OVpointer", "pointer"),
      ("OVarray", "array"), ("OVstruct", "struct"), ("OVunion", "union")]⟩,
  ⟨"Core.loaded_value", ``Core.LoadedValue, [
      ("LVspecified", "specified"), ("LVunspecified", "unspecified")]⟩,
  ⟨"Core.value", ``Core.Value, [
      ("Vobject", "object"), ("Vloaded", "loaded"), ("Vunit", "unit"), ("Vtrue", "true"),
      ("Vfalse", "false"), ("Vctype", "ctype"), ("Vlist", "list"), ("Vtuple", "tuple")]⟩,
  ⟨"Core.ctor", ``Core.Ctor, [
      ("Cnil", "nil"), ("Ccons", "cons"), ("Ctuple", "tuple"), ("Carray", "array"),
      ("Civmax", "ivMax"), ("Civmin", "ivMin"), ("Civsizeof", "ivSizeof"),
      ("Civalignof", "ivAlignof"), ("CivCOMPL", "ivCompl"), ("CivAND", "ivAnd"),
      ("CivOR", "ivOr"), ("CivXOR", "ivXor"), ("Cspecified", "specified"),
      ("Cunspecified", "unspecified"), ("Cfvfromint", "fvFromInt"),
      ("Civfromfloat", "ivFromFloat"), ("CivNULLcap", "ivNullCap")]⟩,
  ⟨"Core.generic_pattern_", ``Core.PatternNode, [
      ("CaseBase", "base"), ("CaseCtor", "ctor")]⟩,
  ⟨"Core.generic_pattern", ``Core.Pattern, [
      ("Pattern", "mk")]⟩,
  ⟨"Core.generic_pexpr_", ``Core.PexprNode, [
      ("PEsym", "sym"), ("PEimpl", "impl"), ("PEval", "val"), ("PEconstrained", "constrained"),
      ("PEundef", "undef"), ("PEerror", "error"), ("PEctor", "ctor"), ("PEcase", "case_"),
      ("PEarray_shift", "arrayShift"), ("PEmember_shift", "memberShift"), ("PEmemop", "memop"),
      ("PEnot", "not"), ("PEop", "op"), ("PEconv_int", "convInt"), ("PEwrapI", "wrapI"),
      ("PEcatch_exceptional_condition", "catchExceptionalCondition"), ("PEstruct", "struct"),
      ("PEunion", "union"), ("PEcfunction", "cfunction"), ("PEmemberof", "memberof"),
      ("PEcall", "call"), ("PElet", "let_"), ("PEif", "if_"), ("PEis_scalar", "isScalar"),
      ("PEis_integer", "isInteger"), ("PEis_signed", "isSigned"),
      ("PEis_unsigned", "isUnsigned"), ("PEbmc_assume", "bmcAssume"),
      ("PEare_compatible", "areCompatible")]⟩,
  ⟨"Core.generic_pexpr", ``Core.Pexpr, [
      ("Pexpr", "mk")]⟩,
  ⟨"Core.kill_kind", ``Core.KillKind, [
      ("Dynamic", "dynamic"), ("Static", "static")]⟩,
  ⟨"Core.generic_action_", ``Core.ActionNode, [
      ("Create", "create"), ("CreateReadOnly", "createReadOnly"), ("Alloc", "alloc"),
      ("Kill", "kill"), ("Store", "store"), ("Load", "load"), ("SeqRMW", "seqRmw"),
      ("RMW", "rmw"), ("Fence", "fence"), ("CompareExchangeStrong", "compareExchangeStrong"),
      ("CompareExchangeWeak", "compareExchangeWeak"), ("LinuxFence", "linuxFence"),
      ("LinuxLoad", "linuxLoad"), ("LinuxStore", "linuxStore"), ("LinuxRMW", "linuxRmw")]⟩,
  ⟨"Core.generic_action", ``Core.Action, [
      ("Action", "mk")]⟩,
  ⟨"Core.generic_paction", ``Core.PolarizedAction, [
      ("Paction", "mk")]⟩,
  ⟨"Core.dyn_annotation", ``Core.DynAnnotation, [
      ("DA_neg", "neg"), ("DA_pos", "pos")]⟩,
  ⟨"Core.pass_by_value_or_pointer", ``Core.PassBy, [
      ("By_pointer", "pointer"), ("By_value", "value")]⟩,
  ⟨"Core.generic_expr_", ``Core.ExprNode, [
      ("Epure", "pure"), ("Ememop", "memop"), ("Eaction", "action"), ("Ecase", "case_"),
      ("Elet", "let_"), ("Eif", "if_"), ("Eccall", "ccall"), ("Eproc", "proc"),
      ("Eunseq", "unseq"), ("Ewseq", "wseq"), ("Esseq", "sseq"), ("Ebound", "bound"),
      ("End", "nd"), ("Esave", "save"), ("Erun", "run"), ("Epar", "par"), ("Ewait", "wait"),
      ("Eannot", "annot"), ("Eexcluded", "excluded")]⟩,
  ⟨"Core.generic_expr", ``Core.Expr, [
      ("Expr", "mk")]⟩,
  ⟨"Core.generic_impl_decl", ``Core.ImplDecl, [
      ("Def", "constant"), ("IFun", "function")]⟩,
  ⟨"Core.generic_impl", ``Core.Impl, []⟩,
  ⟨"Core.generic_fun_map_decl", ``Core.FunDecl, [
      ("Fun", "function"), ("Proc", "procedure"), ("ProcDecl", "procedureDecl"),
      ("BuiltinDecl", "builtinDecl")]⟩,
  ⟨"Core.generic_fun_map", ``Core.FunMap, []⟩,
  ⟨"Core.linking_kind", ``Core.LinkingKind, [
      ("LK_none", "none"), ("LK_tentative", "tentative"), ("LK_normal", "normal")]⟩,
  ⟨"Core.extern_map", ``Core.ExternMap, []⟩,
  ⟨"Core.generic_globs", ``Core.Global, [
      ("GlobalDef", "definition"), ("GlobalDecl", "declaration")]⟩,
  ⟨"Core.core_tag_definitions", ``Core.TagDefinitions, []⟩,
  ⟨"Core.visible_objects_env", ``Core.VisibleObjects, []⟩,
  ⟨"Core.calling_convention", ``Core.CallingConvention, [
      ("Normal_callconv", "normal"), ("Inner_arg_callconv", "innerArg")]⟩,
  ⟨"Core.generic_file", ``Core.File, [
      ("calling_convention", "callingConvention"), ("funinfo", "funInfo"),
      ("loop_attributes", "loopAttributes"), ("visible_objects_env", "visibleObjects")]⟩,
  ⟨"Core.file", ``Core.File, []⟩

]

/-- The Silmaril name of a constructor or field of `type`. -/
def TypeName.rename (type : TypeName) (name : String) : String :=
  (type.renames.lookup name).getD name

end Silmaril.Cerberus.Names
