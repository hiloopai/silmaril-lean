module

public import Silmaril.Cli.Getopt.Defs
public import Silmaril.Cli.Args.Thms
import Silmaril.Proofs.Cli.Getopt.Permute
import Silmaril.Proofs.Cli.Getopt.Agree

/-!
# The getopt dialect: theorems (header)

PROVED (standard axioms; proofs in `Silmaril.Proofs.Cli.Getopt.*`):

* **Long names** (`Permute`): `resolveLong_exact` (an exact name wins), `resolveLong_ok` (a
  resolved name is an entry of the table: the exact one, or one of which the name is a prefix,
  when no entry has the exact name and every entry with that prefix means the same option),
  `resolveLong_unique` (a prefix of entries that all mean one option resolves to that option);
* **Permutation** (`Permute`): **`parse_permuted`**: the GNU reading (`permute`) of an argument
  vector is the POSIX reading (`requireOrder`) of its permuted vector `Parsed.permuted` (option
  tokens first, then `--` if one was given, then the operands); `Tool.parse_permuted` for tools;
* **Agreement with the args front end** (`Agree`): for a grammar getopt can express (`Fits`:
  no subcommands, no exact or negatable options, one-letter single-dash names) and an argument
  vector the pre-pass passes (`t.pre env argv = none`), in either ordering:
  `parse_scan` (getopt and the args scanner `scanAux` read the same frame, or both fail) and
  **`read_agrees`** (`Agrees (t.read env argv) (interpret t.grammar env argv)`: the same run,
  help or version, or usage errors on both sides). The proof goes token by token:
  `readTok_readOpt` (an option token: the derived table finds the option the args lookups find,
  `find_longsOf`, `find_shortsOf`; clusters letter by letter);
* **The environment** (here): `order_posixly` (a set `POSIXLY_CORRECT` stops at the first
  operand), `order_plus`, `order_posix`, `order_gnu` (otherwise GNU getopt permutes).

TASK-CONDITIONAL: `read_render_of` (on `Task.pre_render`, frozen in `Silmaril.Cli.Getopt.Defs`):
the getopt reading of the args normal form of a valid invocation agrees with the checks of the
args front end on that invocation.

Where the pre-pass stops the readings may differ, by design: getopt_long accepts abbreviated
long names and `-W name`; `-t=` gives getopt the argument `=` (the args dialect reads an
attached `=x` as `x`); in POSIX order an option after the first operand is an operand.
-/

@[expose] public section

namespace Silmaril.Cli.Getopt

open Silmaril.Cli

/-! ## Long names -/

theorem resolveLong_exact {ls : List Long} {n : String} {l : Long}
    (h : ls.find? (·.name == n) = some l) : resolveLong ls n = .ok l :=
  Proofs.Cli.Getopt.resolveLong_exact h

theorem resolveLong_ok {ls : List Long} {n : String} {l : Long} (h : resolveLong ls n = .ok l) :
    l ∈ ls ∧ (l.name = n ∨ (prefixOf n l.name = true ∧ (∀ l' ∈ ls, l'.name ≠ n) ∧
      ∀ l' ∈ ls, prefixOf n l'.name = true → l'.target = l.target)) :=
  Proofs.Cli.Getopt.resolveLong_ok h

theorem resolveLong_unique {ls : List Long} {n : String} {l : Long} (hl : l ∈ ls)
    (hp : prefixOf n l.name = true)
    (hu : ∀ l' ∈ ls, prefixOf n l'.name = true → l'.target = l.target) :
    ∃ l', resolveLong ls n = .ok l' ∧ l'.target = l.target :=
  Proofs.Cli.Getopt.resolveLong_unique hl hp hu

/-! ## Permutation -/

/-- **The GNU reading is the POSIX reading of the permuted argument vector.** -/
theorem parse_permuted {t : Table} {argv : List String} {p : Parsed}
    (h : parse t .permute argv = .ok p) : parse t .requireOrder p.permuted = .ok p :=
  Proofs.Cli.Getopt.parse_permuted h

/-- A permuting tool's reading is its POSIX reading of the permuted vector. -/
theorem Tool.parse_permuted {t : Tool} {env : String → Option String} {argv : List String}
    {p : Parsed} (ho : t.order env = .permute) (h : t.parse env argv = .ok p) :
    Getopt.parse t.table .requireOrder p.permuted = .ok p := by
  unfold Tool.parse at h; rw [ho] at h; exact Getopt.parse_permuted h

/-! ## The environment -/

theorem order_posixly (t : Tool) {env : String → Option String}
    (h : (env "POSIXLY_CORRECT").isSome) : t.order env = .requireOrder := by
  simp [Tool.order, h]

theorem order_plus {t : Tool} (h : t.plus = true) (env : String → Option String) :
    t.order env = .requireOrder := by
  simp [Tool.order, h]

theorem order_posix {t : Tool} (h : t.gnu = false) (env : String → Option String) :
    t.order env = .requireOrder := by
  simp [Tool.order, h]

theorem order_gnu {t : Tool} (hg : t.gnu = true) (hp : t.plus = false)
    {env : String → Option String} (he : env "POSIXLY_CORRECT" = none) :
    t.order env = .permute := by
  simp [Tool.order, hg, hp, he]

/-! ## Agreement with the args front end -/

/-- One option token the pre-pass passes reads alike (or fails on both sides). -/
theorem readTok_readOpt {c : Command} (hf : Fits c) {plus w : Bool} {tok : String}
    {next : Option String} (hd : tokDiverge (Table.ofCommand c plus w) tok = none) :
    (readTok (Table.ofCommand c plus w) tok next).toOption = (readOpt c.opts tok next).toOption :=
  Proofs.Cli.Getopt.readTok_readOpt hf hd

/-- A command line the pre-pass passes: getopt and the args scanner read the same frame. -/
theorem parse_scan {c : Command} (hf : Fits c) {plus w : Bool} {ord : Order} {argv : List String}
    (hp : pre (Table.ofCommand c plus w) ord argv = none) :
    (parse (Table.ofCommand c plus w) ord argv).toOption.map
        (fun p => (({ cmd := c.name, opts := p.opts, args := p.operands } : Frame),
          ([] : Invocation))) =
      (scanAux c argv).toOption :=
  Proofs.Cli.Getopt.parse_scanAux hf argv hp

/-- **The getopt reading agrees with `interpret`** on every argument vector the pre-pass passes,
in every environment (so in both orderings). -/
theorem read_agrees (t : Tool) (env : String → Option String) (argv : List String)
    (hf : Fits t.grammar) (hp : t.pre env argv = none) :
    Agrees (t.read env argv) (interpret t.grammar env argv) :=
  Proofs.Cli.Getopt.read_agrees t env argv hf hp

/-- Conditional on `Task.pre_render`: the getopt reading of the normal form of a valid
invocation agrees with the args checks on that invocation. -/
theorem read_render_of (h : Task.pre_render) (t : Tool) (hw : t.wLong = false)
    (env : String → Option String) {fs : Invocation} (hf : Fits t.grammar) (hwf : t.grammar.WF)
    (hv : Valid t.grammar fs) :
    Agrees (t.read env (render t.grammar fs)) (afterScan t.grammar env fs) := by
  have hp : t.pre env (render t.grammar fs) = none := by
    unfold Tool.pre Tool.table; rw [hw]; exact h _ _ _ _ hf hwf hv
  have ha := read_agrees t env _ hf hp
  rw [Proofs.Cli.Getopt.interpret_afterScan, scan_render hwf hv] at ha
  exact ha

end Silmaril.Cli.Getopt
