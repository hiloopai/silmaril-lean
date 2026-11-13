module

public import Silmaril.Wasm.Wac.Emit.Defs
public import Silmaril.Wasm.Wac.Embed.Thms
public import Silmaril.Wasm.Wac.Splice.Thms
public import Silmaril.Wasm.Wac.Bridge.Graph.Thms
public import Silmaril.Wasm.Wac.Graph.Thms
public import Silmaril.Wasm.Component.Binary.Thms
public import Silmaril.Wasm.Perf.Splice.Thms

/-!
# WAC: the entry-point theorems of `wasm-wac compose --wasm` and `wasm-wac plug`

* `composeWasm_correct`: if `composeWasm` returns bytes `b`, the document elaborates and
  validates to a graph `g`, `g` encodes to a component `c`, and `b` parses back to `c` with
  its packages embedded (when asked), which is in the composition profile and lowers to the
  graph `toGraph S g` for every interface assignment `S` (when `g` has no value nodes);
* `composeWasm_toComp`: its component in the component IR, for packages `P`, is
  `Graph.toComp P (toGraph S g)` (`S` the interfaces of `P`), whose meaning is `Graph.sem` of
  the meanings of the packages (`denU_toComp`);
* `composeWasm_congr`: **substituting equivalent packages** (same interfaces, same `denU`)
  gives an equivalent composition, read off the produced binary.

What these do not say: that the component *types* written into the binary are right
(`Lower.graph` reads names and sorts; the binary is validated by `wasm-tools validate` in the
tests, see `docs/projects/wasm-components.md`), and anything about the embedded packages beyond
their position: the meaning of a package is the parameter `P`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Emit

open Silmaril.Wasm
open Silmaril.Wasm.Component.Binary

theorem composeAst_ok {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {d : FuncAlias.Document} {c : Ast} (h : composeAst env noms d = .ok c) :
    ∃ g, Bridge.elabDocXV (tablesOf noms d) env d = .ok g ∧ Bridge.encode (nomOf noms d) g = .ok c := by
  unfold composeAst at h
  cases he : elabGraph env noms d with
  | error e => rw [he] at h; cases h
  | ok g =>
    rw [he] at h
    refine ⟨g, ?_, h⟩
    unfold elabGraph at he
    split at he
    · rename_i g' hg; cases he; exact hg
    · cases he
    · cases he

theorem toBytes_ok {c : Ast} {b : ByteArray} (h : toBytes c = .ok b) : parse b = .ok c := by
  unfold toBytes at h
  split at h
  · rename_i b' hb; cases h; exact parse_encode hb
  · cases h

theorem lower_finish (S : Nat → PkgSig) (pkgs : List (String × Ast)) (embed : Bool) (c : Ast) :
    Lower.graph S (finish pkgs embed c) = Lower.graph S c := by
  cases embed
  · rfl
  · exact Embed.graph_embed S _ c

theorem profile_finish (pkgs : List (String × Ast)) (embed : Bool) (c : Ast) :
    Profile (finish pkgs embed c) ↔ Profile c := by
  cases embed
  · exact Iff.rfl
  · show isProfile (Embed.embed _ c) = true ↔ isProfile c = true
    rw [Embed.isProfile_embed]

/-- **Correctness of `wasm-wac compose --wasm`.** -/
theorem composeWasm_correct {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {pkgs : List (String × Ast)} {embed : Bool} {d : FuncAlias.Document} {b : ByteArray}
    (h : composeWasm env noms pkgs embed d = .ok b) :
    ∃ g c, Bridge.elabDocXV (tablesOf noms d) env d = .ok g ∧
      Bridge.encode (nomOf noms d) g = .ok c ∧
      parse b = .ok (finish pkgs embed c) ∧ Profile (finish pkgs embed c) ∧
      (Bridge.NoValue g → ∀ S, Lower.graph S (finish pkgs embed c) = .ok (Bridge.toGraph S g)) := by
  unfold composeWasm at h
  cases hc : composeAst env noms d with
  | error e => rw [hc] at h; cases h
  | ok c =>
    rw [hc] at h
    obtain ⟨g, hg, he⟩ := composeAst_ok hc
    refine ⟨g, c, hg, he, toBytes_ok h, (profile_finish _ _ _).2 (Bridge.encode_profile he), ?_⟩
    intro hnv S
    rw [lower_finish]
    exact Bridge.lower_encode S hnv he

open Silmaril.Wasm.Component in
/-- The produced binary in the component IR: for packages `P`, `Lower.toComp P` of the
parsed binary is the composition `Graph.toComp P` of the elaborated graph. -/
theorem composeWasm_toComp {M : Type} {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {pkgs : List (String × Ast)} {embed : Bool} {d : FuncAlias.Document} {b : ByteArray}
    (h : composeWasm env noms pkgs embed d = .ok b) (P : Nat → Comp M) :
    ∃ g a, Bridge.elabDocXV (tablesOf noms d) env d = .ok g ∧ parse b = .ok a ∧
      (Bridge.NoValue g →
        Lower.toComp P a = .ok ((Bridge.toGraph (fun k => sigOf (P k)) g).toComp P)) := by
  obtain ⟨g, c, hg, _, hp, _, hl⟩ := composeWasm_correct h
  refine ⟨g, _, hg, hp, fun hnv => ?_⟩
  unfold Lower.toComp
  rw [hl hnv]
  rfl

open Silmaril.Wasm.Component in
/-- **Equivalent packages give equivalent compositions**, read off the binary that
`wasm-wac compose --wasm` (and `plug`) writes: for two assignments of packages with the
same interfaces and the same meanings, the components of the binary have the same meaning. -/
theorem composeWasm_congr {M : Type} [CoreModule M] {env : PkgEnv}
    {noms : List (String × Bridge.NomTable)}
    {pkgs : List (String × Ast)} {embed : Bool} {d : FuncAlias.Document} {b : ByteArray}
    (h : composeWasm env noms pkgs embed d = .ok b)
    (hnv : ∀ g, Bridge.elabDocXV (tablesOf noms d) env d = .ok g → Bridge.NoValue g)
    {C C' : CoreSem M} {P P' : Nat → Comp M}
    (hs : ∀ k, sigOf (P k) = sigOf (P' k)) (heq : ∀ k, (P k).denU C = (P' k).denU C') :
    ∃ a X X', parse b = .ok a ∧ Lower.toComp P a = .ok X ∧ Lower.toComp P' a = .ok X' ∧
      X.denU C = X'.denU C' := by
  obtain ⟨g, a, hg, hp, ht⟩ := composeWasm_toComp h P
  obtain ⟨g', a', hg', hp', ht'⟩ := composeWasm_toComp h P'
  have hgg : g' = g := by rw [hg] at hg'; cases hg'; rfl
  have haa : a' = a := by rw [hp] at hp'; cases hp'; rfl
  rw [hgg, haa] at ht'
  have hS : (fun k => sigOf (P k)) = fun k => sigOf (P' k) := funext hs
  refine ⟨a, _, _, hp, ht (hnv g hg), ht' (hnv g hg), ?_⟩
  rw [hS]
  exact toComp_congr hs heq _

/-- **Correctness of the tool's `compose --wasm`** (byte splicing): the composition is the
encoding `c` of the elaborated graph, the bytes are `c` with the packages' bytes spliced in,
and when the packages' bytes are the canonical encodings of the ASTs `tbl` they parse back to
`c` with the packages embedded, which lowers to the graph. -/
theorem composeWasmRaw_correct {env : PkgEnv} {noms : List (String × Bridge.NomTable)}
    {raw : List (String × ByteArray)} {d : FuncAlias.Document} {b : ByteArray}
    (h : composeWasmRaw env noms raw d = .ok b) :
    ∃ g c, Bridge.elabDocXV (tablesOf noms d) env d = .ok g ∧
      Bridge.encode (nomOf noms d) g = .ok c ∧ Splice.splice (Splice.table raw) c = some b ∧
      ∀ tbl, Splice.Agrees tbl (Splice.table raw) →
        parse b = .ok (Embed.embed tbl c) ∧ Profile (Embed.embed tbl c) ∧
        (Bridge.NoValue g → ∀ S, Lower.graph S (Embed.embed tbl c) = .ok (Bridge.toGraph S g)) := by
  unfold composeWasmRaw at h
  rw [Silmaril.Wasm.Perf.Splice.spliceF_eq] at h
  cases hc : composeAst env noms d with
  | error e => rw [hc] at h; cases h
  | ok c =>
    rw [hc] at h
    obtain ⟨g, hg, he⟩ := composeAst_ok hc
    cases hs : Splice.splice (Splice.table raw) c with
    | none => simp only [hs, bind, Except.bind] at h; cases h
    | some b' =>
      simp only [hs, bind, Except.bind] at h
      cases h
      refine ⟨g, c, hg, he, hs, fun tbl ha => ⟨Splice.parse_splice ha hs, ?_, fun hnv S => ?_⟩⟩
      · show isProfile (Embed.embed tbl c) = true
        rw [Embed.isProfile_embed]; exact Bridge.encode_profile he
      · rw [Embed.graph_embed]; exact Bridge.lower_encode S hnv he

end Silmaril.Wasm.Wac.Emit
