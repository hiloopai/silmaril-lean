module

public import Silmaril.Wasm.Perf.WatRead.Defs
public import Silmaril.Wasm.Wit.Tool.Defs
public import Silmaril.Wasm.Perf.EncodeB.Thms

/-!
# The tail-recursive WAT reader is the reader

`lexT_eq : lexT cs acc = (lex cs).map (acc.reverse ++ ·)`, `readF_eq : readF = Sexp.read`
(registered with `@[csimp]`), `parseWatF_eq : parseWatF = Wit.Tool.parseWat`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.WatRead

open Silmaril.Wasm.Component.Wat (Sexp Tok)
open Silmaril.Wasm.Component.Wat.Sexp (lex parseTop)

theorem lexT_eq (cs : List Char) : ∀ acc : List Tok, lexT cs acc = (lex cs).map (acc.reverse ++ ·) := by
  fun_induction lex cs <;> intro acc <;> simp_all [lexT, Function.comp_def] <;> split <;>
    simp_all

theorem readF_eq : readF = Sexp.read := by
  funext s
  simp only [readF, Sexp.read, lexT_eq, List.reverse_nil, List.nil_append]
  cases lex s.toList <;> rfl

/-- `readF_eq` for the compiler. -/
@[csimp] theorem read_eq_readF : @Sexp.read = @readF := readF_eq.symm

theorem readWatF_eq : readWatF = Silmaril.Wasm.Component.Wat.read := by
  funext s
  simp only [readWatF, Silmaril.Wasm.Component.Wat.read, readF_eq]
  rfl

theorem parseWatF_eq : parseWatF = Silmaril.Wasm.Wit.Tool.parseWat := by
  funext t
  simp only [parseWatF, Silmaril.Wasm.Wit.Tool.parseWat, readWatF_eq,
    ← Silmaril.Wasm.Perf.EncodeB.encode_eq_encodeF]
  rfl

end Silmaril.Wasm.Perf.WatRead
