module

public import Silmaril.Data.Layout.Header.Defs
public import Silmaril.Data.Layout.Bitfield.Defs

/-! # The header subset reader: sanity theorems

Each is one kernel evaluation of `read` (`decide +kernel`): what is read, and what is refused
rather than skipped. The last section lays out structs read from a header text under System V
x86-64 and Microsoft x64 (`tagLayout`; `Silmaril.Data.Layout.Bitfield` for bit-fields). -/

@[expose] public section

namespace Silmaril.Data.Layout.Header

/-- Whether `text`, read alone as `h.h`, is refused. -/
def refuses (text : String) : Bool := (read [("h.h", text)] "h.h").toOption.isNone

/-- The prototypes `text` declares. -/
def protos (text : String) : Option (List (String × CProto)) :=
  (read [("h.h", text)] "h.h").toOption.map (·.protos)

theorem reads_typedefs :
    protos "typedef unsigned int u32; typedef u32 *u32p; u32 f(u32p a, const char *s);" =
      some [("f", ⟨.typedef "u32" (.int .int .unsigned),
        [.typedef "u32p" (.ptr (.typedef "u32" (.int .int .unsigned))), .ptr (.int .char .plain)],
        false⟩)] := by decide +kernel

theorem reads_void_varargs_arrays :
    protos "int g(void); int printf(const char *fmt, ...); void h(int a[4], int b[]);" =
      some [("g", ⟨.int .int .signed, [], false⟩),
        ("printf", ⟨.int .int .signed, [.ptr (.int .char .plain)], true⟩),
        ("h", ⟨.void, [.ptr (.int .int .signed), .ptr (.int .int .signed)], false⟩)] := by
  decide +kernel

theorem reads_specifier_order :
    protos "unsigned long long a(void); long unsigned int b(void); signed char c(void);" =
      some [("a", ⟨.int .longLong .unsigned, [], false⟩), ("b", ⟨.int .long .unsigned, [], false⟩),
        ("c", ⟨.int .char .signed, [], false⟩)] := by decide +kernel

theorem reads_include_guard_and_macros :
    protos "#ifndef H\n#define H\n#define ZEXPORT\n#define ZEXTERN extern\nZEXTERN int ZEXPORT z(int);\n#endif\n" =
      some [("z", ⟨.int .int .signed, [.int .int .signed], false⟩)] := by decide +kernel

theorem reads_incomplete_struct_pointer :
    protos "struct s *mk(void); void use(struct s *p);" =
      some [("mk", ⟨.ptr (.struct "s"), [], false⟩), ("use", ⟨.void, [.ptr (.struct "s")], false⟩)] := by
  decide +kernel

theorem refuses_outside_subset :
    refuses "#if X\nint f(void);\n#endif\n" = true ∧
    refuses "typedef struct { int a; } T;" = true ∧
    refuses "int f();" = true ∧
    refuses "void f(int (*cb)(int));" = true ∧
    refuses "int f(int x) { return x; }" = true ∧
    refuses "static int f(int);" = true ∧
    refuses "uLong f(uLong);" = true ∧
    refuses "#define F(x) x\n" = true ∧
    refuses "#include <stdio.h>\n" = true ∧
    refuses "int f(void)" = true ∧
    refuses "struct s;" = true ∧
    refuses "int f(int); long f(long);" = true ∧
    refuses "typedef int t; typedef long t;" = true := by decide +kernel

theorem reads_identical_redeclaration :
    protos "int f(int); int f(int x); typedef int t; typedef int t; t g(void);" =
      some [("f", ⟨.int .int .signed, [.int .int .signed], false⟩),
        ("g", ⟨.typedef "t" (.int .int .signed), [], false⟩)] := by decide +kernel

/-- The qualifiers `text` writes for `f`. -/
def quals (text f : String) : Option ProtoQuals :=
  (read [("h.h", text)] "h.h").toOption.bind (·.quals? f)

/-- Qualifiers are kept by level: `const char *` is `[["const"], []]` (a non-`const` pointer to
`const char`), `char *const` is `[[], ["const"]]`; an array parameter gets the level of the
pointer it is adjusted to; `__restrict` is `restrict`. -/
theorem reads_qualifiers :
    quals "int printf(const char *fmt, ...);" "printf" =
      some ⟨[[]], [[["const"], []]]⟩ ∧
    quals "const volatile int *g(char *const p, const int a[], int *__restrict q);" "g" =
      some ⟨[["const", "volatile"], []], [[[], ["const"]], [["const"], []], [[], ["restrict"]]]⟩ := by
  decide +kernel

/-- A redeclaration must agree on pointee qualifiers; parameters' top-level qualifiers do not
matter (C17 6.7.6.3p15). -/
theorem qualifier_redeclaration :
    refuses "int f(const char *); int f(char *);" = true ∧
    refuses "const char *f(void); char *f(void);" = true ∧
    refuses "int f(const int); int f(int);" = false ∧
    refuses "int f(char *const); int f(char *);" = false := by decide +kernel

/-! ## Struct, union and enum definitions -/

/-- The header `text` reads to, read alone as `h.h`. -/
def header? (text : String) : Option Header := (read [("h.h", text)] "h.h").toOption

/-- The message `text` is refused with. -/
def error? (text : String) : Option String :=
  match read [("h.h", text)] "h.h" with
  | .error e => some e
  | .ok _ => none

/-- Definitions are read in the order they are completed: a definition nested in a member comes
first (its tag has file scope, C17 6.2.1p4). Members keep `_Alignas`, array sizes (row-major:
`buf[3][2]` is 3 arrays of 2) and bit-field widths; `: 0` is an unnamed bit-field. -/
theorem reads_struct_union_definitions :
    (header? ("struct outer { struct inner { short s; char t; } in; " ++
      "_Alignas(16) char buf[3][2]; union u { int i; double d; } uu; " ++
      "unsigned f : 4, : 0, g : 2; };")).map (·.decls) =
      some [⟨.struct, "inner", [⟨"s", .int .short .signed, none, none⟩,
          ⟨"t", .int .char .plain, none, none⟩]⟩,
        ⟨.union, "u", [⟨"i", .int .int .signed, none, none⟩,
          ⟨"d", .float .double, none, none⟩]⟩,
        ⟨.struct, "outer", [⟨"in", .struct "inner", none, none⟩,
          ⟨"buf", .array (.array (.int .char .plain) 2) 3, some 16, none⟩,
          ⟨"uu", .union "u", none, none⟩,
          ⟨"f", .int .int .unsigned, none, some 4⟩, ⟨"", .int .int .unsigned, none, some 0⟩,
          ⟨"g", .int .int .unsigned, none, some 2⟩]⟩] := by decide +kernel

/-- Enumerators get their implicit (previous plus one, from 0) or explicit values, decimal,
hexadecimal or negated; a trailing `,` is allowed. A member of enum type is laid out as the
data model's `enumRepr`. -/
theorem reads_enum_definitions :
    (header? "enum color { RED, GREEN = 5, BLUE, NEG = -2, AFTER, HEX = 0x10, }; struct p { enum color c; };").map
        (fun h => (h.enums, h.decls)) =
      some ([("color", [("RED", 0), ("GREEN", 5), ("BLUE", 6), ("NEG", -2), ("AFTER", -1),
          ("HEX", 16)])],
        [⟨.struct, "p", [⟨"c", .enum "color" none, none, none⟩]⟩]) := by decide +kernel

/-- `typedef struct T {…} T;` defines the tag and the typedef; a self-referential member is a
pointer to the tag. -/
theorem reads_typedef_struct :
    (header? "typedef struct node { struct node *next; int v; } node; node *push(node *l, int v);").map
        (fun h => (h.decls, h.typedefs, h.protos)) =
      some ([⟨.struct, "node", [⟨"next", .ptr (.struct "node"), none, none⟩,
          ⟨"v", .int .int .signed, none, none⟩]⟩],
        [("node", .struct "node")],
        [("push", ⟨.ptr (.typedef "node" (.struct "node")),
          [.ptr (.typedef "node" (.struct "node")), .int .int .signed], false⟩)]) := by decide +kernel

/-- A struct defined in the header and used by pointer in prototypes: the prototypes read as
before the definition was supported. -/
theorem reads_defined_struct_pointer :
    protos "struct rec { int a; }; int use(const struct rec *r); struct rec *mk(void);" =
      some [("use", ⟨.int .int .signed, [.ptr (.struct "rec")], false⟩),
        ("mk", ⟨.ptr (.struct "rec"), [], false⟩)] := by decide +kernel

/-- An identical redefinition of a struct, union or enum is accepted (as C23 allows; C17
refuses any redefinition in one scope) and recorded once. -/
theorem reads_identical_definition :
    (header? ("struct s { int a; char b : 3; }; struct s { int a; char b : 3; }; " ++
      "enum e { A, B }; enum e { A, B }; struct s *f(void);")).map (fun h => (h.decls, h.enums)) =
      some ([⟨.struct, "s", [⟨"a", .int .int .signed, none, none⟩,
          ⟨"b", .int .char .plain, none, some 3⟩]⟩], [("e", [("A", 0), ("B", 1)])]) := by
  decide +kernel

/-- A redefinition with different members (or enumerators), or of a tag as another kind, is
refused, with its reason. -/
theorem refuses_conflicting_definition :
    error? "struct s { int a; }; struct s { long a; };" =
      some "struct s redefined with different members" ∧
    error? "struct s { int a; }; struct s { int a : 4; };" =
      some "struct s redefined with different members" ∧
    error? "struct s { int a; }; union s { int a; };" =
      some "tag s is already defined as another kind" ∧
    error? "enum e { A }; struct e { int a; };" =
      some "tag e is already defined as another kind" ∧
    error? "enum e { A }; enum e { A = 1 };" =
      some "enum e redefined with different enumerators" ∧
    error? "enum e { A }; enum f { A };" = some "enumerator A redeclares an identifier" ∧
    error? "enum e { A }; int A(void);" = some "A redeclares an enumerator" ∧
    error? "struct s { int a; int a; };" = some "struct s: a member declared twice" := by
  decide +kernel

/-- What stays outside the subset is refused, not skipped: definitions without a tag
(`typedef struct {…} T;`, anonymous members, an untagged struct type of a named member),
flexible and zero-length arrays, array sizes that are not literals, function-pointer members,
members of incomplete type (also the struct itself), bit-fields of other types, with `_Alignas`
or named with width 0, `_Alignas(type)`, enums with a fixed underlying type, enumerators
with non-literal values or outside `int`, definitions inside a parameter, object declarations,
forward declarations, and `#pragma pack` (any `#pragma` but `once`). -/
theorem refuses_unsupported_aggregates :
    refuses "typedef struct { int a; } T;" = true ∧
    refuses "struct s { struct t { int a; }; int b; };" = true ∧
    refuses "struct s { union { int a; float b; }; };" = true ∧
    refuses "struct s { struct { int a; } x; };" = true ∧
    refuses "enum { A, B };" = true ∧
    refuses "struct s { int n; int a[]; };" = true ∧
    refuses "struct s { int a[0]; };" = true ∧
    refuses "struct s { int a[N]; };" = true ∧
    refuses "struct s { int (*cb)(int); };" = true ∧
    refuses "struct s { struct t x; };" = true ∧
    refuses "struct s { struct s x; };" = true ∧
    refuses "struct s { void v; };" = true ∧
    refuses "struct s { double d : 3; };" = true ∧
    refuses "struct s { int *p : 3; };" = true ∧
    refuses "struct s { _Alignas(8) int a : 3; };" = true ∧
    refuses "struct s { int a : 0; };" = true ∧
    refuses "struct s { _Alignas(double) int a; };" = true ∧
    refuses "struct s { };" = true ∧
    refuses "enum e : unsigned char { A };" = true ∧
    refuses "enum e { A = B };" = true ∧
    refuses "enum e { A = 2147483647, B };" = true ∧
    refuses "void f(struct s { int a; } x);" = true ∧
    refuses "struct s { int a; } x;" = true ∧
    refuses "struct s { int a; } struct t { int b; };" = true ∧
    refuses "#pragma pack(1)\nstruct s { char c; int i; };" = true ∧
    refuses "struct s { int a; " = true := by decide +kernel

/-! ## Layouts of a parsed header

The definitions a header reads are an `Env` (`Header.env`), laid out by the layout API under a
data model: `tagLayout` for aggregates without bit-fields (it refuses bit-fields), and
`Bitfield`'s `bitLayout` and queries under a bit-field policy. System V x86-64 (`sysvX86_64`,
policy `sysv`) and Microsoft x64 (`msX64`, policy `ms`: clang's MSVC-compatible record layout,
a data model and not the Win64 calling convention) differ on `long` (8 bytes against 4) and on
bit-field storage units. -/

/-- A struct with `char`, `unsigned` bit-fields, `long`, `int` and `double` members. -/
def recH : String :=
  "struct rec { char c; unsigned flags : 3; unsigned mode : 5; long n; int x; double d; };"

/-- Its definitions. -/
def recEnv : Env := ((header? recH).map Header.env).getD []

theorem recEnv_eq :
    recEnv = [⟨.struct, "rec", [⟨"c", .int .char .plain, none, none⟩,
      ⟨"flags", .int .int .unsigned, none, some 3⟩, ⟨"mode", .int .int .unsigned, none, some 5⟩,
      ⟨"n", .int .long .signed, none, none⟩, ⟨"x", .int .int .signed, none, none⟩,
      ⟨"d", .float .double, none, none⟩]⟩] := by decide +kernel

/-- The bit-level layout of `rec` under a policy and data model: slots and shape. -/
def recLayout (pol : BitPolicy) (dm : DataModel) : Option (List BitSlot × Shape) :=
  match recEnv.find? .struct "rec" with
  | some d => (bitLayout pol dm recEnv d).toOption
  | none => none

/-- **System V x86-64**: the bit-fields share `c`'s `unsigned` storage unit (bits 8 and 11), `n`
is 8 bytes at 8; `sizeof` 32, `_Alignof` 8; 10 padding bytes (80 padding bits). C's `offsetof`
refuses the bit-field `flags`; `bitOffsetOf` gives its placement. -/
theorem rec_layout_sysv :
    recLayout .sysv sysvX86_64 = some ([⟨"c", 0, 8⟩, ⟨"flags", 8, 3⟩, ⟨"mode", 11, 5⟩,
      ⟨"n", 64, 64⟩, ⟨"x", 128, 32⟩, ⟨"d", 192, 64⟩], ⟨32, 8⟩) ∧
    (bitShapeOf .sysv sysvX86_64 recEnv .struct "rec").toOption = some ⟨32, 8⟩ ∧
    (offsetOf .sysv sysvX86_64 recEnv .struct "rec" "n").toOption = some 8 ∧
    (offsetOf .sysv sysvX86_64 recEnv .struct "rec" "x").toOption = some 16 ∧
    (offsetOf .sysv sysvX86_64 recEnv .struct "rec" "d").toOption = some 24 ∧
    (offsetOf .sysv sysvX86_64 recEnv .struct "rec" "flags").toOption = none ∧
    (bitOffsetOf .sysv sysvX86_64 recEnv .struct "rec" "mode").toOption = some (11, 5) ∧
    (recLayout .sysv sysvX86_64).map (fun (ss, sh) => (paddingBytes ss sh, paddingBits ss sh)) =
      some (10, 80) := by decide +kernel

/-- **Microsoft x64** (clang's MSVC emulation): the bit-fields open a new `unsigned` unit at
byte 4 (bits 32 and 35), `n` is a 4-byte `long` at 8, so `x` is at 12 and `d` at 16;
`sizeof` 24, `_Alignof` 8; 6 padding bytes (48 padding bits). -/
theorem rec_layout_ms :
    recLayout .ms msX64 = some ([⟨"c", 0, 8⟩, ⟨"flags", 32, 3⟩, ⟨"mode", 35, 5⟩,
      ⟨"n", 64, 32⟩, ⟨"x", 96, 32⟩, ⟨"d", 128, 64⟩], ⟨24, 8⟩) ∧
    (bitShapeOf .ms msX64 recEnv .struct "rec").toOption = some ⟨24, 8⟩ ∧
    (offsetOf .ms msX64 recEnv .struct "rec" "n").toOption = some 8 ∧
    (offsetOf .ms msX64 recEnv .struct "rec" "x").toOption = some 12 ∧
    (offsetOf .ms msX64 recEnv .struct "rec" "d").toOption = some 16 ∧
    (bitOffsetOf .ms msX64 recEnv .struct "rec" "flags").toOption = some (32, 3) ∧
    (recLayout .ms msX64).map (fun (ss, sh) => (paddingBytes ss sh, paddingBits ss sh)) =
      some (6, 48) := by decide +kernel

/-- `tagLayout` (no bit-field policy) refuses `rec` because of its bit-fields. -/
theorem rec_tagLayout_refused :
    (tagLayout sysvX86_64 recEnv .struct "rec").toOption = none := by decide +kernel

/-- A typedef'd struct without bit-fields, with a nested union, used by pointer in a prototype. -/
def ptH : String :=
  "typedef struct pt { char tag; long v; short s[3]; union num { int i; double d; } u; } pt; " ++
  "long norm(const pt *p);"

def ptEnv : Env := ((header? ptH).map Header.env).getD []

/-- `pt` by `tagLayout` under System V x86-64: `(member, offset, size)` rows, shape and padding
bytes. `v` is an 8-byte `long` at 8; `sizeof` 32, `_Alignof` 8, padding bytes 1–7 and 22–23. -/
theorem pt_layout_sysv :
    (tagLayout sysvX86_64 ptEnv .struct "pt").toOption.map (fun L => (L.table, L.shape, L.padding)) =
      some ([("tag", 0, 1), ("v", 8, 8), ("s", 16, 6), ("u", 24, 8)], ⟨32, 8⟩,
        [1, 2, 3, 4, 5, 6, 7, 22, 23]) := by decide +kernel

/-- `pt` under Microsoft x64: `v` is a 4-byte `long` at 4; `sizeof` 24, `_Alignof` 8, padding
bytes 1–3 and 14–15. -/
theorem pt_layout_ms :
    (tagLayout msX64 ptEnv .struct "pt").toOption.map (fun L => (L.table, L.shape, L.padding)) =
      some ([("tag", 0, 1), ("v", 4, 4), ("s", 8, 6), ("u", 16, 8)], ⟨24, 8⟩,
        [1, 2, 3, 14, 15]) := by decide +kernel

/-- The prototype after the definition reads. -/
theorem reads_pt_prototype :
    protos ptH = some [("norm", ⟨.int .long .signed, [.ptr (.typedef "pt" (.struct "pt"))], false⟩)] := by
  decide +kernel

/-- `_Alignas(16)` on a member: `x` moves to 16 and the struct is 32 bytes, 16-aligned. -/
theorem alignas_layout :
    ((header? "struct a { char c; _Alignas(16) int x; };").bind fun h =>
      (tagLayout sysvX86_64 h.env .struct "a").toOption.map fun L => (L.table, L.shape)) =
      some ([("c", 0, 1), ("x", 16, 4)], ⟨32, 16⟩) := by decide +kernel

end Silmaril.Data.Layout.Header

end
