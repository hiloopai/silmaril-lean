module

public import Silmaril.Data.Layout.Command.Defs

/-!
# Regression tests: what the C record-layout slice rejects, and how

The parser's messages are checked in the kernel (`decide +kernel` on `parse`); the commands'
messages with `#guard_msgs`. `clang/tampered.x86_64.json` is a hand-edited copy of the
x86-64 fixture with one member moved, so the import must fail.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Examples.Rejections

open Silmaril.Data.Layout Silmaril.Data.Layout.Source Silmaril.Data.Layout.Record

/-- `parse src` fails with exactly `msg`. -/
def rejectsWith (src msg : String) : Bool :=
  match parse src with
  | .error e => e == msg
  | .ok _ => false

example : rejectsWith "struct A { int x : 3; };" "unsupported C feature: bit-fields" := by
  decide +kernel
example : rejectsWith "struct A { _Alignas(8) int x; };"
    "unsupported C feature: alignment specifiers (`_Alignas`)" := by decide +kernel
example : rejectsWith "struct A { int x; } __attribute__((packed));"
    "unsupported C feature: attributes (`__attribute__`)" := by decide +kernel
example : rejectsWith "#pragma pack(1)\nstruct A { int x; };"
    "unsupported C feature: preprocessor directives (`#`)" := by decide +kernel
example : rejectsWith "struct A { const int x; };"
    "unsupported C feature: type qualifiers (`const`)" := by decide +kernel
example : rejectsWith "typedef int T;"
    "unsupported C feature: typedef declarations (`typedef`)" := by decide +kernel
example : rejectsWith "struct A { enum E e; };" "unsupported C feature: enumerations (`enum`)" := by
  decide +kernel
example : rejectsWith "struct A { int n; char data[]; };"
    "unsupported C feature: flexible array members" := by decide +kernel
example : rejectsWith "struct A { char data[0]; };"
    "unsupported C feature: zero-length arrays" := by decide +kernel
example : rejectsWith "struct A { int (*f)(int); };"
    "unsupported C feature: function pointers and parenthesized declarators" := by decide +kernel
example : rejectsWith "struct A { struct { int y; } b; };"
    "unsupported C feature: anonymous structs and unions" := by decide +kernel
example : rejectsWith "struct A { struct B { int y; } b; };"
    "unsupported C feature: record definitions inside a member \
      (define the record at top level)" := by decide +kernel
example : rejectsWith "struct A;" "unsupported C feature: forward declarations (`A`)" := by
  decide +kernel
example : rejectsWith "struct A {};" "`A` has no members (empty records are a GNU extension)" := by
  decide +kernel
example : rejectsWith "struct A { char c[0x10]; };"
    "unsupported literal `0x10`: only decimal array lengths" := by decide +kernel
example : rejectsWith "struct A { int x; } a;"
    "expected `;` after the definition of `A` (declaring objects is not supported)" := by
  decide +kernel
example : rejectsWith "struct A { struct B b; }; struct B { int y; };"
    "member `b` of `A` has an incomplete or void type \
      (records must be defined before they are used by value)" := by decide +kernel
example : rejectsWith "struct A { struct A self; };"
    "member `self` of `A` has an incomplete or void type \
      (records must be defined before they are used by value)" := by decide +kernel
example : rejectsWith "struct A { void v; };"
    "member `v` of `A` has an incomplete or void type \
      (records must be defined before they are used by value)" := by decide +kernel
example : rejectsWith "struct A { int x; int x; };" "`A` has two members with the same name" := by
  decide +kernel
example : rejectsWith "struct A { int x; }; union A { int y; };" "tag `A` is defined twice" := by
  decide +kernel
example : rejectsWith "struct A { int int; };" "`int` cannot be a member name" := by decide +kernel

/-- Pointers may name records that are incomplete, including the record itself. -/
example : (parse "struct L { struct L *next; struct M *other; void *p; };").toOption.isSome := by
  decide +kernel

/-! ## The commands -/

/-- error: c_layout: unsupported C feature: bit-fields -/
#guard_msgs in
c_layout Bad for Target.x86_64 := "struct A { unsigned flag : 1; };"

c_layout Small for Target.x86_64 := include_str "clang/message.c"

/--
error: c_layout_import: clang/tampered.x86_64.json disagrees with the model: `Header.length`: predicted offset 32 bits, observed `length` at 64
-/
#guard_msgs in
c_layout_import Small.x86_64 from "clang/tampered.x86_64.json"

/--
error: c_layout_import: clang/message.i386.json disagrees with the model: the report is for `i386-unknown-linux-gnu`, the target `x86_64` is `x86_64-unknown-linux-gnu`
-/
#guard_msgs in
c_layout_import Small.x86_64 from "clang/message.i386.json"

end Silmaril.Data.Layout.Examples.Rejections
