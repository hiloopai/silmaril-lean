module

/-!
# Tables and numbers of `wasm-tools metadata show`

* `renderTable`: comfy-table 8.0.0 as `metadata show` uses it (`UTF8_FULL` with rounded corners,
  `ContentArrangement::Dynamic`, width 80, padding one space each side, no colours): the
  dynamic column arrangement (`find_columns_that_fit_into_average`,
  `optimize_space_after_split`, `distribute_remaining_space`) and its line splitting
  (`split_line`, `split_long_word`), ported.
* `displayWidth`: unicode-width's `width`, exact for ASCII; for other characters an
  approximation (East Asian wide and fullwidth ranges count 2, combining marks and zero-width
  characters 0, others 1). Graphemes are approximated by characters when a long non-ASCII word
  is split.
* `f64Of`, `fmtFixed1`, `roundAway`: the IEEE double nearest a rational (round half to even),
  Rust's `{:.1}` of a double (exact decimal value, half to even) and `f64::round` (half away
  from zero), for the `SIZE` and `SIZE%` columns.
* `siShort`: bytesize 2.7.0's `display().si_short()`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta.Table

/-! ## Widths -/

/-- The display width of a character (see the module note). -/
def charWidth (c : Char) : Nat :=
  let n := c.toNat
  -- control characters count 1 in a string's width (unicode-width 0.2's `str_width`)
  if n < 0xa0 then 1
  else if (0x300 ≤ n ∧ n < 0x370) ∨ (0x200b ≤ n ∧ n < 0x2010) ∨ n == 0xfeff ∨
      (0xfe00 ≤ n ∧ n < 0xfe10) then 0
  else if (0x1100 ≤ n ∧ n < 0x1160) ∨ (0x2e80 ≤ n ∧ n < 0xa4d0 ∧ n != 0x303f) ∨
      (0xac00 ≤ n ∧ n < 0xd7a4) ∨ (0xf900 ≤ n ∧ n < 0xfb00) ∨ (0xfe30 ≤ n ∧ n < 0xfe50) ∨
      (0xff00 ≤ n ∧ n < 0xff61) ∨ (0xffe0 ≤ n ∧ n < 0xffe7) ∨ (0x1f300 ≤ n ∧ n < 0x1f650) ∨
      (0x1f900 ≤ n ∧ n < 0x1fa00) ∨ (0x20000 ≤ n ∧ n < 0x3fffe) then 2
  else 1

/-- The display width of a string. -/
def displayWidth (s : String) : Nat := s.toList.foldl (fun w c => w + charWidth c) 0

/-! ## `split_line` -/

/-- `split_long_word`: the longest prefix fitting in `allowed`, and the rest. -/
def splitLongWord (allowed : Nat) (word : String) : String × String :=
  if word.toList.all (fun c => 0x20 ≤ c.toNat ∧ c.toNat < 0x7f) then
    (String.ofList (word.toList.take allowed), String.ofList (word.toList.drop allowed))
  else
    let rec go : List Char → Nat → List Char → List Char × List Char
      | [], _, acc => (acc.reverse, [])
      | c :: cs, w, acc =>
        if w + charWidth c > allowed then (acc.reverse, c :: cs) else go cs (w + charWidth c) (c :: acc)
    let (h, t) := go word.toList 0 []
    (String.ofList h, String.ofList t)

/-- The splitting state: finished lines, the current line and its width. -/
structure SplitSt where
  lines : Array String := #[]
  cur : String := ""
  len : Nat := 0

/-- `check_if_full`. -/
def checkFull (cw : Nat) (st : SplitSt) : SplitSt :=
  if st.len > cw - 2 then { st with lines := st.lines.push st.cur, cur := "", len := 0 } else st

/-- The loop of `split_line` over the remaining elements; `fuel` bounds its steps. -/
def splitGo (cw : Nat) : Nat → List String → SplitSt → SplitSt
  | 0, _, st => st
  | _ + 1, [], st => st
  | f + 1, next :: els, st =>
    let nl := displayWidth next
    let added := nl + st.len + (if st.cur.isEmpty then 0 else 1)
    let rem0 := cw - st.len
    let rem := if st.cur.isEmpty then rem0 else rem0 - 1
    if added ≤ cw then
      let st := if st.cur.isEmpty then st else { st with cur := st.cur.push ' ', len := st.len + 1 }
      let st := { st with cur := st.cur ++ next, len := st.len + nl }
      splitGo cw f els (checkFull cw st)
    else if !st.cur.isEmpty && rem ≤ 2 then
      splitGo cw f (next :: els) { lines := st.lines.push st.cur, cur := "", len := 0 }
    else if nl > cw then
      let newLine := st.cur.isEmpty
      let cur := if newLine then st.cur else st.cur.push ' '
      let (head, tail) := splitLongWord rem next
      if newLine && head.isEmpty then
        match tail.toList with
        | c :: cs =>
          splitGo cw f (String.ofList cs :: els) { lines := st.lines.push (cur.push c), cur := "", len := 0 }
        | [] => splitGo cw f els { lines := st.lines.push cur, cur := "", len := 0 }
      else
        splitGo cw f (tail :: els) { lines := st.lines.push (cur ++ head), cur := "", len := 0 }
    else
      splitGo cw f els (checkFull cw { lines := st.lines.push st.cur, cur := next, len := nl })

/-- `split_line` with the delimiter `' '`. -/
def splitLine (cw : Nat) (line : String) : List String :=
  let els := line.splitOn " "
  let st := splitGo cw (4 * line.length + els.length + 4) els {}
  let st := if st.cur.isEmpty then st else { st with lines := st.lines.push st.cur }
  st.lines.toList

/-! ## Arrangement -/

/-- The cells of a column (header first), each split into its `\n` lines. -/
abbrev Column := List (List String)

/-- `longest_line_after_split`. -/
def longestAfterSplit (avg : Nat) (col : Column) : Nat :=
  col.foldl (fun m cell => cell.foldl (fun m line =>
    if displayWidth line > avg then (splitLine avg line).foldl (fun m p => max m (displayWidth p)) m
    else max m (displayWidth line)) m) 0

/-- The arrangement state: decided content widths, remaining width and columns. -/
structure ArrSt where
  widths : Array (Option Nat)
  remW : Nat
  remC : Nat

def ArrSt.avg (st : ArrSt) : Nat := if st.remC == 0 then 0 else st.remW / st.remC

/-- `fix_column`: decide column `i`; whether columns remain. -/
def ArrSt.fix (st : ArrSt) (i w : Nat) : ArrSt × Bool :=
  let st := { widths := st.widths.set! i (some w), remW := st.remW - w, remC := st.remC - 1 }
  (st, st.remC > 0)

/-- One pass of `find_columns_that_fit_into_average` over the columns from `i`. -/
def fitPass (maxw : Array Nat) : List Nat → ArrSt → Bool → ArrSt × Bool
  | [], st, found => (st, found)
  | i :: is, st, found =>
    if (st.widths[i]?.getD none).isSome then fitPass maxw is st found else
    if maxw[i]!  ≤ st.avg then
      let (st, more) := st.fix i maxw[i]!
      if !more then (st, found) else fitPass maxw is st true
    else fitPass maxw is st found

def fitLoop (maxw : Array Nat) (idx : List Nat) : Nat → ArrSt → ArrSt
  | 0, st => st
  | f + 1, st =>
    if st.remC == 0 || st.avg == 0 then st else
    let (st, found) := fitPass maxw idx st false
    if found then fitLoop maxw idx f st else st

/-- One pass of `optimize_space_after_split`. -/
def optPass (cols : Array Column) : List Nat → ArrSt → Bool → ArrSt × Bool
  | [], st, found => (st, found)
  | i :: is, st, found =>
    if (st.widths[i]?.getD none).isSome then optPass cols is st found else
    let avg := st.avg
    let longest := longestAfterSplit avg cols[i]!
    if avg - longest ≥ 3 then
      let (st, more) := st.fix i longest
      if !more then (st, found) else optPass cols is st true
    else optPass cols is st found

def optLoop (cols : Array Column) (idx : List Nat) : Nat → ArrSt → ArrSt
  | 0, st => st
  | f + 1, st =>
    let (st, found) := optPass cols idx st false
    if found then optLoop cols idx f st else st

/-- The content widths of the columns (`dynamic::arrange`, no constraints, width `tw`). -/
def arrange (tw : Nat) (cols : Array Column) : Array Nat :=
  let n := cols.size
  let maxw := cols.map fun c => max 1 (c.foldl (fun m cell => cell.foldl (fun m l => max m (displayWidth l)) m) 0)
  let idx := List.range n
  let st : ArrSt := { widths := Array.replicate n none, remW := tw - (n + 1) - 2 * n, remC := n }
  let st := fitLoop maxw idx (n + 1) st
  let st := if st.remC > 0 then optLoop cols idx (n + 1) st else st
  if st.remC == 0 then st.widths.map (·.getD 1) else
  let remW := max st.remW st.remC
  let avg := remW / st.remC
  let excess := remW - avg * st.remC
  let (ws, _) := idx.foldl (fun (ws, k) i =>
    if (ws[i]?.getD none).isSome then (ws, k)
    else (ws.set! i (some (if k < excess then avg + 1 else avg)), k + 1)) (st.widths, 0)
  ws.map (·.getD 1)

/-! ## Rendering -/

/-- Cell alignment. -/
inductive Align where
  | left
  | right
  deriving DecidableEq, Inhabited

/-- `align_line` with padding one each side. -/
def alignLine (cw : Nat) (a : Align) (line : String) : String :=
  let r := cw - displayWidth line
  match a with
  | .left => " " ++ line ++ "".pushn ' ' (r + 1)
  | .right => "".pushn ' ' (r + 1) ++ line ++ " "

/-- The lines of one row: each cell split to its width, aligned, and padded to the row's
height. -/
def rowLines (ws : Array Nat) (aligns : List Align) (row : List String) : List String :=
  let cells : List (List String) := (row.zip (aligns.zip ws.toList)).map fun (c, a, w) =>
    (c.splitOn "\n").flatMap (fun l => if displayWidth l > w then splitLine w l else [l]) |>.map (alignLine w a)
  let h := cells.foldl (fun m c => max m c.length) 0
  (List.range h).map fun k =>
    "│" ++ "┆".intercalate ((cells.zip ws.toList).map fun (c, w) => c[k]?.getD ("".pushn ' ' (w + 2))) ++ "│"

/-- A horizontal line. -/
def hline (ws : Array Nat) (l f j r : Char) : String :=
  String.singleton l ++ (String.singleton j).intercalate (ws.toList.map fun w => "".pushn f (w + 2)) ++
    String.singleton r

/-- **The table**, lines joined by `\n` (no final newline), as comfy-table's `Display`. -/
def renderTable (header : List String) (rows : List (List String)) (aligns : List Align)
    (tw : Nat := 80) : String :=
  let n := header.length
  let cols : Array Column := (List.range n).toArray.map fun i =>
    (header :: rows).map fun r => ((r[i]?.getD "").splitOn "\n")
  let ws := arrange tw cols
  let top := hline ws '╭' '─' '┬' '╮'
  let hsep := hline ws '╞' '═' '╪' '╡'
  let rsep := hline ws '├' '╌' '┼' '┤'
  let bot := hline ws '╰' '─' '┴' '╯'
  let body := (rows.map (rowLines ws aligns)).intersperse [rsep] |>.flatten
  "\n".intercalate ([top] ++ rowLines ws aligns header ++ [hsep] ++ body ++ [bot])

/-! ## Numbers -/

/-- Round `num / den` to an integer, half to even. -/
def roundHalfEven (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if 2 * r > den then q + 1 else if 2 * r < den then q else if q % 2 == 0 then q else q + 1

/-- The IEEE double nearest `a / b` (`a, b > 0`), as `(m, e)` with value `m * 2^e`. -/
def f64Of (a b : Nat) : Nat × Int :=
  let e0 : Int := (Nat.log2 a : Int) - (Nat.log2 b : Int) - 52
  let scaled (e : Int) : Nat × Nat :=   -- numerator, denominator of a / (b * 2^e)
    if e ≥ 0 then (a, b * 2 ^ e.toNat) else (a * 2 ^ (-e).toNat, b)
  let e := if (scaled e0).1 < 2 ^ 52 * (scaled e0).2 then e0 - 1 else e0
  let e := if (scaled e).1 ≥ 2 ^ 53 * (scaled e).2 then e + 1 else e
  let (nu, de) := scaled e
  let m := roundHalfEven nu de
  if m == 2 ^ 53 then (2 ^ 52, e + 1) else (m, e)

/-- The value of a double as a fraction. -/
def fracOf (d : Nat × Int) : Nat × Nat :=
  if d.2 ≥ 0 then (d.1 * 2 ^ d.2.toNat, 1) else (d.1, 2 ^ (-d.2).toNat)

/-- Rust's `{:.1}` of a non-negative double. -/
def fmtFixed1 (d : Nat × Int) : String :=
  let (nu, de) := fracOf d
  let k := roundHalfEven (10 * nu) de
  toString (k / 10) ++ "." ++ toString (k % 10)

/-- `f64::round` of a non-negative double (half away from zero). -/
def roundAway (d : Nat × Int) : Nat :=
  let (nu, de) := fracOf d
  (2 * nu + de) / (2 * de)

/-- The product of a double by a natural number, rounded to a double. -/
def f64MulNat (d : Nat × Int) (k : Nat) : Nat × Int :=
  let (nu, de) := fracOf d
  if nu == 0 || k == 0 then (0, 0) else f64Of (nu * k) de

/-- bytesize's `display().si_short()`: `123B`, `1.5k`, `3.1M`, … -/
def siShort (bytes : Nat) : String :=
  if bytes < 1000 then toString bytes ++ "B" else
  let rec expOf : Nat → Nat → Nat
    | 0, e => e
    | f + 1, e => if bytes ≥ 1000 ^ (e + 1) then expOf f (e + 1) else e
  let e := expOf 7 1
  let pre := ("kMGTPE".toList[e - 1]?).getD 'E'
  fmtFixed1 (f64Of bytes (1000 ^ e)) ++ String.singleton pre

end Silmaril.Wasm.Tools.Meta.Table

end
