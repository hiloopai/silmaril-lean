/* Aggregate layout cases for Silmaril.Data.Layout (bit-fields under System V and Microsoft x64).
   Each case is measured by measure.sh with gcc (x86-64 System V) and clang (x86_64-pc-windows-msvc). */
enum e3 { E3A, E3B, E3C };
struct c01 { unsigned int a : 3; unsigned int b : 30; };
struct c02 { char a; int b : 4; };
struct c03 { char a : 4; int b : 4; };
struct c04 { int a : 4; int : 0; int b : 4; char c; };
struct c05 { char a; long long : 3; };
struct c06 { short a : 9; short b : 9; };
struct c07 { int a : 20; int b : 20; };
struct c08 { char a : 3; short b : 3; int c : 3; long long d : 3; };
struct c09 { long long a : 40; int b : 30; };
struct c10 { unsigned char a : 1; unsigned char b : 7; unsigned char c : 1; };
struct c11 { _Bool a : 1; _Bool b : 1; int c; };
struct c12 { enum e3 a : 2; enum e3 b : 2; };
struct c13 { int a; char b : 2; char c; };
struct c14 { char a; char : 0; char b; };
struct c15 { int : 3; char a; };
struct c16 { long a; int b : 5; };
struct c17 { long double a; char b; };
struct c18 { void *p; unsigned int f : 1; };
struct c19 { char a[3]; int b : 9; };
struct c20 { short a; _Alignas(16) char b; int c : 3; };
union u01 { int a : 3; char b; };
union u02 { char a; long long b : 33; };
union u03 { int : 7; char a; };
struct c21 { unsigned int a : 31; unsigned int b : 2; unsigned int c : 31; };
struct c22 { char a; int b : 24; char c; };
