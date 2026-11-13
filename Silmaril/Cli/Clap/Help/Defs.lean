module

public import Silmaril.Cli.Clap.Defs

/-!
# clap's help layout, exactly

The `-h` and `--help` texts of a tool in the clap dialect, byte for byte as clap 4 prints them
at a given width (clap's: `COLUMNS` when set, at most 100; 100 when unknown, `widthOf`), as
functions of the grammar (`Tool.grammar`) and its presentation data (`Tool.after`,
`Tool.long`). `Silmaril.Cli.Surface.Command.help` is the reference layout without wrapping; this
module adds what clap's `HelpTemplate` does on top of it:

* **wrapping** (`wrap`): clap's `LineWrapper` over the words of `find_words_ascii_space`
  (a word is a run of non-spaces with the spaces after it; leading spaces are a word of their
  own). A word moves to the next line when it would end past the width, except the first word
  of a line; the spaces before the break are dropped and the line's indentation is repeated.
  Every input line is wrapped on its own; the about, the argument helps and the texts after the
  options are wrapped;
* **two-column rows** (`row`): the left column padded to the widest entry plus two spaces, the
  help wrapped to the columns left and indented by the same amount; or, when one row of the
  section would not fit (`nextLine`: the left column takes more than 40% of the width and some
  help text does not fit beside it), every help on its own lines, indented by 10;
* **long help** (`--help`, when the command has long texts, `Long.exists`): the long about,
  every argument on its own lines with its long help (paragraphs indented by 10, blank lines
  between arguments, the `[default: …]` and `[possible values: …]` notes as a paragraph of
  their own), and the long text after the options.

The help ends with exactly one newline (clap trims trailing white space). `help NAME…` and
`NAME --help` print the long help; `-h` the short one.

A Silmaril addition (the layout follows `clap_builder` 4.5's `output/help_template.rs` and
`output/textwrap`); the test is `tools/cli-spec/tests/wasm-tools-surface.sh`, which compares
both texts of every command path of `wasm-tools` with the pinned binary byte for byte.
-/

@[expose] public section

namespace Silmaril.Cli.Clap.Help

open Silmaril.Cli

/-- clap's terminal width when it is unknown, and its maximum (`max_term_width`). -/
def width : Nat := 100

/-- clap's width from the environment: `COLUMNS` when set to a number, at most 100 (no
terminal is consulted: the output of these tools is compared in pipes). -/
def widthOf (columns : Option String) : Nat :=
  match columns.bind String.toNat? with
  | some n => if n == 0 then width else min n width
  | none => width

/-- The indentation of a help text on its own lines (`TAB` and `NEXT_LINE_INDENT`). -/
def nextIndent : Nat := 10

/-! ## Wrapping -/

/-- The words of one line (clap's `find_words_ascii_space`): runs of non-spaces with the
spaces after them; leading spaces are a word of their own. -/
def wordsAux : List Char → List Char → Bool → List (List Char)
  | [], cur, _ => if cur.isEmpty then [] else [cur.reverse]
  | c :: cs, cur, inWs =>
    if inWs && c != ' ' then cur.reverse :: wordsAux cs [c] false
    else wordsAux cs (c :: cur) (c == ' ')

/-- The words of one line. -/
def words (l : List Char) : List (List Char) := wordsAux l [] false

/-- Rust's `trim_end` for the characters clap meets here. -/
def trimEnd (w : List Char) : List Char :=
  (w.reverse.dropWhile fun c => c == ' ' || c == '\n' || c == '\t' || c == '\r').reverse

/-- clap's `LineWrapper::wrap` (clap 4.6) on the words of one line, from line width `lw`: the
first word of positive width never moves (`first`); before a later word that would end past
`hard`, the previous word loses its trailing spaces, a newline starts a new line and the line's
indentation `ind` (its first word when that is only spaces) is repeated. The words are returned
in reverse. -/
def wrapWords (hard : Nat) (ind : List Char) : Nat → Bool → List (List Char) →
    List (List Char) → List (List Char)
  | _, _, acc, [] => acc
  | lw, first, acc, w :: ws =>
    let t := trimEnd w
    let delta := w.length - t.length
    if first && 0 < t.length then wrapWords hard ind (lw + t.length + delta) false (w :: acc) ws
    else if hard < lw + t.length then
      let acc := match acc with
        | p :: ps => trimEnd p :: ps
        | [] => []
      wrapWords hard ind (ind.length + t.length + delta) first (w :: ind :: ['\n'] :: acc) ws
    else wrapWords hard ind (lw + t.length + delta) first (w :: acc) ws

/-- The indentation of a line: its first word when that is white space only. -/
def indentOf (ws : List (List Char)) : List Char :=
  match ws with
  | w :: _ => if (trimEnd w).isEmpty then w else []
  | [] => []

/-- Split after every newline (Rust's `split_inclusive('\n')`). -/
def linesIncl : List Char → List Char → List (List Char)
  | [], cur => if cur.isEmpty then [] else [cur.reverse]
  | '\n' :: cs, cur => ('\n' :: cur).reverse :: linesIncl cs []
  | c :: cs, cur => linesIncl cs (c :: cur)

/-- **clap's wrapping** of a text to `hard` columns: every line is wrapped on its own, keeping
its indentation; trailing white space is dropped (`StyledStr::wrap`). -/
def wrap (hard : Nat) (s : String) : String :=
  String.ofList (trimEnd ((linesIncl s.toList []).flatMap fun l =>
    let ws := words l
    (wrapWords hard (indentOf ws) 0 true [] ws).reverse.flatten))

/-- Indent every line after the first by `n` spaces (clap's `indent("", trailing)`: blank
lines get the spaces too). -/
def indentAfter (n : Nat) (s : String) : String :=
  String.ofList (s.toList.flatMap fun c =>
    if c == '\n' then '\n' :: List.replicate n ' ' else [c])

/-- `n` spaces. -/
def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-! ## Rows -/

/-- One row of a section: the left column, the help, the default value and the possible
values (rendered as notes) and the long help (`none`: the help). -/
structure Row where
  left : String
  help : String
  default : Option String := none
  choices : List String := []
  long : Option String := none
  deriving Inhabited

/-- The notes of an argument: `[default: …]` then `[possible values: …]`, joined by `sep` (a
space in short help, a newline in long help). -/
def notes (sep : String) (default : Option String) (choices : List String) : String :=
  sep.intercalate ((match default with | some d => ["[default: " ++ d ++ "]"] | none => []) ++
    (if choices.isEmpty then [] else ["[possible values: " ++ ", ".intercalate choices ++ "]"]))

/-- The notes of a row (`notes`). -/
def Row.notes (r : Row) (sep : String) : String := Help.notes sep r.default r.choices

/-- The help and notes of a row in short help (joined by a space). -/
def Row.short (r : Row) : String :=
  let n := r.notes " "
  if n.isEmpty then r.help else if r.help.isEmpty then n else r.help ++ " " ++ n

/-- clap's `arg_next_line_help` in short help: the left column (`longest + 4`) takes more
than 40% of the width and the help with its notes does not fit beside it. -/
def Row.wraps (width longest : Nat) (r : Row) : Bool :=
  let taken := longest + 4
  decide (taken ≤ width) && decide (taken * 10 > width * 4) &&
    decide (r.help.length + (r.notes " ").length > width - taken)

/-- One row in short help; `next`: help on its own lines. -/
def Row.render (width longest : Nat) (next : Bool) (r : Row) : String :=
  let sp := if next then nextIndent else longest + 4
  let body := indentAfter sp (wrap (width - sp) r.short)
  if next then "  " ++ r.left ++ "\n" ++ spaces nextIndent ++ body
  else "  " ++ r.left ++ spaces (longest + 2 - r.left.length) ++ body

/-- One row in long help: the long help (else the help), the notes as a paragraph of their
own, all on their own lines. -/
def Row.renderLong (width : Nat) (r : Row) : String :=
  let h := r.long.getD r.help
  let n := r.notes "\n"
  let text := if n.isEmpty then h else if h.isEmpty then n else h ++ "\n\n" ++ n
  "  " ++ r.left ++ "\n" ++ spaces nextIndent ++
    indentAfter nextIndent (wrap (width - nextIndent) text)

/-- A section of rows (`Arguments:`, `Options:`); `opts` counts clap's four columns for the
short name in the widest entry. -/
def block (width : Nat) (title : String) (long : Bool) (rows : List Row) : String :=
  let longest := rows.foldl (fun n r => max n r.left.length) 2
  if long then title ++ "\n" ++ "\n\n".intercalate (rows.map (Row.renderLong width))
  else
    let next := rows.any (Row.wraps width longest)
    title ++ "\n" ++ "\n".intercalate (rows.map (Row.render width longest next))

end Silmaril.Cli.Clap.Help

namespace Silmaril.Cli.Clap

open Silmaril.Cli Silmaril.Cli.Clap.Help

/-! ## The help texts -/

/-- The long texts of the command at `path` (below the root). -/
def Tool.longAt (t : Tool) (path : List String) : Long := (t.long.lookup path).getD {}

/-- The row of a positional. -/
def helpPosRow (lg : Long) (p : Pos) : Row :=
  let s := surfacePos p
  { left := s.spec, help := s.help, default := s.default, choices := s.choices,
    long := lg.args.lookup p.id }

/-- The row of an option; `extra`: possible values the tool lists for it (`Tool.choices`). -/
def helpOptRow (lg : Long) (extra : String → List String) (o : Opt) : Row :=
  let s := surfaceOpt o
  { left := s.spec, help := s.help, default := s.default,
    choices := if s.choices.isEmpty then extra o.id else s.choices,
    long := lg.args.lookup o.id }

/-- The `Commands:` section of a group. -/
def helpCommands (width : Nat) (helpSub : Bool) (c : Command) : String :=
  block width "Commands:" false (c.subs.map (fun s => { left := s.name, help := s.about }) ++
    (if helpSub then [{ left := Surface.helpRow.1, help := Surface.helpRow.2 }] else []))

/-- Trim trailing white space and end with one newline (clap's last step). -/
def helpFinish (s : String) : String := String.ofList (trimEnd s.toList) ++ "\n"

/-- **The help of the command `c` at `path`** (below the root): the short help (`-h`), or the
long help (`--help`) when `long` and the command has long texts. -/
def Tool.clapHelpOf (t : Tool) (c : Command) (path : List String) (long : Bool)
    (width : Nat := Help.width) : String :=
  let lg := t.longAt path
  let useLong := long && lg.exists
  let about := if useLong then lg.about.getD c.about else c.about
  let sc := surfaceCmd t path c
  let sections : List String :=
    (if c.subs.isEmpty then [] else [helpCommands width t.helpSub c]) ++
    (if c.pos.isEmpty then [] else [block width "Arguments:" useLong (c.pos.map (helpPosRow lg))]) ++
    (if c.opts.isEmpty then [] else [block width "Options:" useLong (c.opts.map (helpOptRow lg fun id =>
      (t.choices.find? fun (q, i, _) => q == path && i == id).map (·.2.2) |>.getD []))])
  let after := wrap width (if useLong then lg.after.getD sc.after else sc.after)
  helpFinish ((if about.isEmpty then "" else wrap width about ++ "\n\n") ++
    sc.usage (t.grammar.name :: path) ++ "\n\n" ++ "\n\n".intercalate sections ++
    (if after.isEmpty then "" else "\n\n" ++ after))

/-- clap's implicit `help` subcommand of a group. -/
def implicitHelp : Command where
  name := "help"
  about := Surface.helpRow.2
  pos := [{ id := "command", arity := .many, metavar := "COMMAND",
            help := "Print help for the subcommand(s)" }]

/-- The command at `path` (below the root) as help shows it: a subcommand, or clap's implicit
`help` subcommand of a group. -/
def Tool.helpCmd? (t : Tool) (path : List String) : Option Command :=
  match t.grammar.walk path with
  | some c => some c
  | none =>
    if path.getLast? == some "help" then
      (t.grammar.walk path.dropLast).bind fun g =>
        if g.subs.isEmpty || !t.helpSub then none else some implicitHelp
    else none

/-- The help of the command at `path` (below the root; the root's if the path leads nowhere). -/
def Tool.clapHelp (t : Tool) (path : List String) (long : Bool) (width : Nat := Help.width) :
    String :=
  match t.helpCmd? path with
  | some c => t.clapHelpOf c path long width
  | none => t.clapHelpOf t.grammar [] long width

end Silmaril.Cli.Clap
