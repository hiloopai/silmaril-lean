module

public import Silmaril.Wasi.Versions.WitImport.KTokens.Defs
public import Silmaril.Wasi.Versions.WitImport.KSplit.Thms

@[expose] public section

/-!
# The kernel importer on tokens without doc comments: transfer

`importTokK_eq`: when each demoted text parses as its full text's tokens without doc comments
(`parseCharsK cs = parseTokK full`, the theorems `KF.….parseNd` of `KCert/Lex/*`), the kernel
importer on the full texts' tokens is the kernel importer on the demoted texts; `kTableTok_of`,
`kDropsTok_of` and `kRPkgTok_of` carry the tables over.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasm.Wit

/-- The kernel importer on tokens is the importer on the demoted texts. -/
theorem importTokK_eq {sel : Bool} {srcs fulls : List (List Char)}
    (h : List.Forall₂ (fun cs full => parseCharsK cs = parseTokK full) srcs fulls) :
    importTokK sel fulls = importKD sel srcs := by
  have hm : fulls.mapM parseTokStep = srcs.mapM parseStep := by
    induction h with
    | nil => rfl
    | cons hx _ ih =>
      rw [List.mapM_cons, List.mapM_cons, ih]
      simp only [parseTokStep, parseStep, hx]
      rfl
  unfold importTokK importKD
  rw [hm]

/-- The table of the kernel importer on tokens. -/
theorem kTableTok_of {ver sel : Bool} {srcs fulls : List (List Char)} {B : Binary.Package}
    {deps : Binary.Env} (h : List.Forall₂ (fun cs full => parseCharsK cs = parseTokK full) srcs fulls)
    (hk : importKD sel srcs = .ok (B, deps)) : kTableTok ver sel fulls = some (table ver B) := by
  unfold kTableTok
  rw [importTokK_eq h, hk]

/-- The drops of the kernel importer on tokens. -/
theorem kDropsTok_of {ver : Bool} {srcs fulls : List (List Char)} {B : Binary.Package}
    {deps : Binary.Env} (h : List.Forall₂ (fun cs full => parseCharsK cs = parseTokK full) srcs fulls)
    (hk : importKD false srcs = .ok (B, deps)) : kDropsTok ver fulls = some (drops ver B) := by
  unfold kDropsTok
  rw [importTokK_eq h, hk]

/-- The resolved package of the kernel importer on tokens. -/
theorem kRPkgTok_of {ver sel : Bool} {srcs fulls : List (List Char)} {B : Binary.Package}
    {deps : Binary.Env} (h : List.Forall₂ (fun cs full => parseCharsK cs = parseTokK full) srcs fulls)
    (hk : importKD sel srcs = .ok (B, deps)) :
    kRPkgTok ver sel fulls = some (rtable ver B, envOf B deps) := by
  unfold kRPkgTok
  rw [importTokK_eq h, hk]

end Silmaril.Wasi.Versions.WitImport
