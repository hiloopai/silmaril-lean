module

public import Silmaril.Wasm.Tools.Cli.Defs

/-!
# Laws of the command-line grammar

Equational laws of `Silmaril.Wasm.Tools.Cli.go` that reduce spellings to a normal form:

* `go_dd`: after `--`, every argument is a positional (`go_ddArg`: `--` itself switches).
* `go_dash`: `-` alone is a positional.
* `go_long_eq`: `--NAME=V` is `--NAME V` for an option that takes a value (when `V` is
  non-empty and does not look like an option).
* `go_long_flag_eq`: `--NAME=V` for a switch or counter is the `unexpectedValue` error.
* `parse_help`: `--help` asks for the long help when no option is called `help`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Cli

theorem splitEq_of_not_mem {n : Arg} (h : '=' ∉ n) : splitEq n = (n, none) := by
  induction n with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ '=' := fun e => h (e ▸ List.mem_cons_self)
    have hcs : '=' ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitEq, ih hcs]

theorem splitEq_append {n v : Arg} (h : '=' ∉ n) : splitEq (n ++ '=' :: v) = (n, some v) := by
  induction n with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ '=' := fun e => h (e ▸ List.mem_cons_self)
    have hcs : '=' ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitEq, ih hcs]

theorem go_dd {s : Spec} {st : St} {a : Arg} {rest : List Arg} (h : st.dd = true) :
    go s st (a :: rest) = positional s st a rest := by
  rw [go.eq_def]; simp [h]

theorem go_ddArg {s : Spec} {st : St} {rest : List Arg} (h : st.dd = false) :
    go s st (['-', '-'] :: rest) = go s { st with dd := true } rest := by
  rw [go.eq_def]; simp [h]

theorem go_dash {s : Spec} {st : St} {rest : List Arg} (h : st.dd = false) :
    go s st (['-'] :: rest) = positional s st ['-'] rest := by
  rw [go.eq_def]; simp [h]

theorem go_long_eq {s : Spec} {st : St} {c : Char} {l v : Arg} {o : Opt} {rest : List Arg}
    (hst : st.dd = false) (hl : '=' ∉ c :: l) (ho : s.findLong (c :: l) = some o)
    (hv : o.takesValue = true) (hv0 : v ≠ []) (hopt : optionLike v = false) :
    go s st (('-' :: '-' :: (c :: l ++ '=' :: v)) :: rest) =
      go s st (('-' :: '-' :: c :: l) :: v :: rest) := by
  have hne : l ++ '=' :: v ≠ ['e', 'l', 'p'] := by
    intro e
    have : '=' ∈ ['e', 'l', 'p'] := e ▸ List.mem_append_right _ List.mem_cons_self
    simp at this
  have hsplit := splitEq_append (v := v) hl
  have hsplit' := splitEq_of_not_mem hl
  have hv' : v.isEmpty = false := List.isEmpty_eq_false_iff.mpr hv0
  rw [go.eq_def, go.eq_def]
  simp only [hst, Bool.false_eq_true, ↓reduceIte, List.cons_append]
  simp only [List.cons_append] at hsplit
  cases v with
  | nil => exact absurd rfl hv0
  | cons _ _ => simp [hne, hsplit, hsplit', ho, hv, hv', hopt]

theorem go_long_flag_eq {s : Spec} {st : St} {c : Char} {l v : Arg} {o : Opt}
    {rest : List Arg} (hst : st.dd = false) (hl : '=' ∉ c :: l)
    (ho : s.findLong (c :: l) = some o) (hv : o.takesValue = false) :
    go s st (('-' :: '-' :: (c :: l ++ '=' :: v)) :: rest) =
      .err (.unexpectedValue o (String.ofList v)) := by
  have hne : l ++ '=' :: v ≠ ['e', 'l', 'p'] := by
    intro e
    have : '=' ∈ ['e', 'l', 'p'] := e ▸ List.mem_append_right _ List.mem_cons_self
    simp at this
  have hsplit := splitEq_append (v := v) hl
  rw [go.eq_def]
  simp only [hst, Bool.false_eq_true, ↓reduceIte, List.cons_append]
  simp only [List.cons_append] at hsplit
  simp [hne, hsplit, ho, hv]

theorem parse_help {s : Spec} {rest : List String} (h : s.findLong "help".toList = none) :
    parse s ("--help" :: rest) = .help true := by
  have h' : s.findLong ['h', 'e', 'l', 'p'] = none := h
  unfold parse
  rw [List.map_cons, go.eq_def]
  simp [h']

end Silmaril.Wasm.Tools.Cli
