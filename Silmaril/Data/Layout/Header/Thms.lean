module

public import Silmaril.Data.Layout.Header.Defs

/-! # The header subset reader: sanity theorems

Each is one kernel evaluation of `read` (`decide +kernel`): what is read, and what is refused
rather than skipped. -/

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
    refuses "struct s { int a; };" = true ∧
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

end Silmaril.Data.Layout.Header

end
