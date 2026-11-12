module

/-!
# URLs of `--source` and `--homepage` (a subset of the url crate 2.5.8)

wasm-metadata stores `Url::parse(s)?.to_string()`. `normalizeUrl s` is that string for the URLs
this subset handles, an error for the inputs it rejects, and `unsupported` otherwise:

* leading and trailing C0 controls and spaces are removed; a scheme `[A-Za-z][A-Za-z0-9+.-]*`
  is required and lower-cased;
* the special schemes `http`, `https`, `ws`, `wss`, `ftp` need `//`, a host of ASCII letters,
  digits, `-` and `.` (lower-cased; not ending in a numeric label) and an optional port (the
  scheme's default port is dropped); the path's `.` and `..` segments are resolved, an empty
  path becomes `/`; path, query and fragment are percent-encoded with the WHATWG sets;
* other schemes: the rest is kept when it holds only URL code points without `%`, `\` or
  whitespace.

Unsupported (an explicit error, not upstream's result): user info, IP addresses, non-ASCII
(IDNA) hosts, backslashes, tabs and newlines inside, `file:` URLs, and non-special URLs with
other characters.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta.Url

def special : List (String × Nat) :=
  [("http", 80), ("https", 443), ("ws", 80), ("wss", 443), ("ftp", 21)]

def hexU (n : Nat) : Char := "0123456789ABCDEF".toList[n]!

/-- Percent-encode the characters of `s` in the set `p` (and every non-ASCII byte). -/
def pctEncode (p : Char → Bool) (s : String) : String :=
  s.toList.foldl (fun acc c =>
    if c.toNat < 0x80 && !p c then acc.push c
    else (String.toUTF8 (String.singleton c)).toList.foldl (fun acc b =>
      (acc.push '%').push (hexU (b.toNat / 16)) |>.push (hexU (b.toNat % 16))) acc) ""

def c0 (c : Char) : Bool := c.toNat < 0x20 || c.toNat > 0x7e
def fragmentSet (c : Char) : Bool := c0 c || c ∈ [' ', '"', '<', '>', '`']
def querySet (c : Char) : Bool := c0 c || c ∈ [' ', '"', '#', '<', '>', '\'']
def pathSet (c : Char) : Bool := querySet c && c != '\'' || c ∈ ['?', '`', '{', '}', '^']

def isSingleDot (s : String) : Bool := s == "." || s.toLower == "%2e"
def isDoubleDot (s : String) : Bool :=
  let l := s.toLower
  l == ".." || l == ".%2e" || l == "%2e." || l == "%2e%2e"

/-- The path segments with dot segments resolved. -/
def resolvePath (segs : List String) : List String :=
  let n := segs.length
  (segs.zipIdx.foldl (fun acc (s, i) =>
    let last := i + 1 == n
    if isDoubleDot s then (if acc.isEmpty then acc else acc.dropLast) ++ (if last then [""] else [])
    else if isSingleDot s then acc ++ (if last then [""] else [])
    else acc ++ [s]) [])

/-- **`Url::parse(s).map(|u| u.to_string())`** on the supported subset. -/
def normalizeUrl (s0 : String) : Except String String := do
  let trim (l : List Char) := l.dropWhile fun c => c.toNat ≤ 0x20
  let s := String.ofList (trim (trim s0.toList).reverse).reverse
  let cs := s.toList
  let scheme := cs.takeWhile fun c => c.isAlphanum || c == '+' || c == '-' || c == '.'
  match cs.drop scheme.length with
  | ':' :: rest =>
    match scheme with
    | c :: _ => if !c.isAlpha then throw "relative URL without a base"
    | [] => throw "relative URL without a base"
    let scheme := (String.ofList scheme).toLower
    if rest.any (fun c => c == '\t' || c == '\n' || c == '\r' || c == '\\') then
      throw "unsupported URL form"
    match special.lookup scheme with
    | none =>
      if scheme == "file" then throw "unsupported URL form"
      if rest.all (fun c => 0x20 < c.toNat && c.toNat < 0x7f && c != '%' && c != '"' &&
          c != '<' && c != '>' && c != '`' && c != '{' && c != '}' && c != '^' && c != '|') then
        pure (scheme ++ ":" ++ String.ofList rest)
      else throw "unsupported URL form"
    | some defPort =>
      match rest with
      | '/' :: '/' :: r =>
        let auth := r.takeWhile fun c => c != '/' && c != '?' && c != '#'
        let r := r.drop auth.length
        if auth.contains '@' then throw "unsupported URL form"
        let hostC := auth.takeWhile (· != ':')
        let portC := (auth.drop hostC.length).drop 1
        if hostC.isEmpty then throw "empty host"
        if !hostC.all (fun c => c.isAlphanum || c == '-' || c == '.') then
          throw "unsupported URL form"
        let host := (String.ofList hostC).toLower
        let labels := (host.splitOn ".").filter (!·.isEmpty)
        if (labels.getLast?.map (fun l => l.toList.all Char.isDigit || l.startsWith "0x")).getD false then
          throw "unsupported URL form"
        let port ← if auth.contains ':' then
            if !portC.all Char.isDigit then throw "invalid port number" else
            if portC.isEmpty then pure "" else
            let p := (String.ofList portC).toNat!
            if p > 65535 then throw "invalid port number"
            pure (if p == defPort then "" else ":" ++ toString p)
          else pure ""
        let pathC := r.takeWhile fun c => c != '?' && c != '#'
        let r := r.drop pathC.length
        let queryC := if r.head? == some '?' then (r.drop 1).takeWhile (· != '#') else []
        let hasQuery := r.head? == some '?'
        let r := if hasQuery then r.drop (1 + queryC.length) else r
        let hasFrag := r.head? == some '#'
        let fragC := if hasFrag then r.drop 1 else []
        let segs := ((String.ofList pathC).splitOn "/").drop 1
        let segs := resolvePath segs
        let path := if segs.isEmpty then "/" else
          String.join (segs.map fun g => "/" ++ pctEncode pathSet g)
        pure (scheme ++ "://" ++ host ++ port ++ path ++
          (if hasQuery then "?" ++ pctEncode querySet (String.ofList queryC) else "") ++
          (if hasFrag then "#" ++ pctEncode fragmentSet (String.ofList fragC) else ""))
      | _ => throw "unsupported URL form"
  | _ => throw "relative URL without a base"

end Silmaril.Wasm.Tools.Meta.Url

end
