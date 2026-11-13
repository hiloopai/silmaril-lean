module

public import Silmaril.Project.WasmP3Rust.TasksP3.Defs
public import Silmaril.Wasm.Component.BinaryP3.Project.Thms
public import Silmaril.Project.WasmP3Rust.Hello.P3.Thms
public import Silmaril.Project.WasmP3Rust.Echo.P3.Thms
public import Silmaril.Project.WasmP3Rust.Cat.P3.Thms
public import Silmaril.Project.WasmP3Rust.CatDebug.P3.Thms
public import Silmaril.Wasm.Resource.Protocol.Thms

/-!
# The WASI 0.3 Rust examples: whole-component theorems

**PROVED** for `hello.wasm`, `echo.wasm`, `cat.wasm` and `cat-debug.wasm`:

* `<n>_parses : Parses3 <N>.File.bytes`: `BinaryP3.parse` reads the file as `<N>.P3.ast`
  (`<N>.P3.parse_eq`, from the chunked certificates);
* `<n>_valid : Valid3 <N>.File.bytes` (`BinaryP3.wellScopedC3`, kernel evaluation on the AST);
* `<n>_hasWorld : HasWorld3 <N>.File.bytes Cli.command`: the component targets
  `wasi:cli/command@0.3.0` (`BinaryP3.World.targets`, kernel evaluation);
* **refuted**, the pass-1 statements of `Silmaril.Project.WasmP3Rust.Tasks.Defs`, which parse with
  the old grammar: `<n>_not_parses : ¬ Task.parses <N>.File.bytes`, and so (`not_valid`,
  `not_hasWorld`, `not_everyHost`) every statement built on `Binary.parse … = .ok _`. Their
  restatements on `BinaryP3.parse` are in `Silmaril.Project.WasmP3Rust.TasksP3.Defs`.

The second half of the module (`helloG_xtrace`, `everyHost_hello_no_ok`) shows why the
behavioural statements are restated with `WasiSat`.

A Silmaril addition.
-/


@[expose] public section

namespace Silmaril.Project.WasmP3Rust

open Silmaril.Wasm.Component

/-- The old grammar rejects a file the new one reads with async built-ins at the top level. -/
theorem not_parses_of {b : List UInt8} {c : BinaryP3.Ast}
    (h : BinaryP3.parse (arrOf b) = .ok c) (hc : BinaryP3.topV0 c = false) : ¬ Task.parses b :=
  fun ⟨c₀, h₀⟩ => BinaryP3.not_parse_v0 h hc c₀ h₀

theorem not_valid {b : List UInt8} (h : ¬ Task.parses b) : ¬ Task.valid b :=
  fun ⟨c, hc, _⟩ => h ⟨c, hc⟩

theorem not_hasWorld {b : List UInt8} (h : ¬ Task.parses b) (W : Silmaril.Wasm.Wit.Project.WorldType) :
    ¬ Task.hasWorld b W :=
  fun ⟨c, hc, _⟩ => h ⟨c, hc⟩

theorem not_everyHost {b : List UInt8} (h : ¬ Task.parses b)
    (den : Silmaril.Wasm.Component.Binary.Ast → Silmaril.Wasi.Versions.P3.p3World.Model) {S : Type}
    (G : Silmaril.Wasm.Resource.Protocol S Silmaril.Wasi.WEv) : ¬ Task.everyHost b den G :=
  fun ⟨c, hc, _⟩ => h ⟨c, hc⟩

/-! ### `Hello` -/

/-- **`Hello` parses** under the grammar with async built-ins. -/
theorem hello_parses : Parses3 Hello.File.bytes := ⟨_, Hello.P3.parse_eq⟩

/-- **`Hello` is well scoped.** -/
theorem hello_valid : Valid3 Hello.File.bytes :=
  ⟨_, Hello.P3.parse_eq, by decide +kernel⟩

/-- **`Hello` targets `wasi:cli/command@0.3.0`.** -/
theorem hello_hasWorld : HasWorld3 Hello.File.bytes Cli.command :=
  ⟨_, Hello.P3.parse_eq, by decide +kernel⟩

/-- `Hello` has async built-ins at the top level. -/
theorem hello_not_topV0 : BinaryP3.topV0 Hello.P3.ast = false := by decide +kernel

/-- **Refuted: the pass-1 statement `Task.parses`** (the old grammar rejects the file). -/
theorem hello_not_parses : ¬ Task.parses Hello.File.bytes :=
  not_parses_of Hello.P3.parse_eq hello_not_topV0

/-! ### `Echo` -/

/-- **`Echo` parses** under the grammar with async built-ins. -/
theorem echo_parses : Parses3 Echo.File.bytes := ⟨_, Echo.P3.parse_eq⟩

/-- **`Echo` is well scoped.** -/
theorem echo_valid : Valid3 Echo.File.bytes :=
  ⟨_, Echo.P3.parse_eq, by decide +kernel⟩

/-- **`Echo` targets `wasi:cli/command@0.3.0`.** -/
theorem echo_hasWorld : HasWorld3 Echo.File.bytes Cli.command :=
  ⟨_, Echo.P3.parse_eq, by decide +kernel⟩

/-- `Echo` has async built-ins at the top level. -/
theorem echo_not_topV0 : BinaryP3.topV0 Echo.P3.ast = false := by decide +kernel

/-- **Refuted: the pass-1 statement `Task.parses`** (the old grammar rejects the file). -/
theorem echo_not_parses : ¬ Task.parses Echo.File.bytes :=
  not_parses_of Echo.P3.parse_eq echo_not_topV0

/-! ### `Cat` -/

/-- **`Cat` parses** under the grammar with async built-ins. -/
theorem cat_parses : Parses3 Cat.File.bytes := ⟨_, Cat.P3.parse_eq⟩

/-- **`Cat` is well scoped.** -/
theorem cat_valid : Valid3 Cat.File.bytes :=
  ⟨_, Cat.P3.parse_eq, by decide +kernel⟩

/-- **`Cat` targets `wasi:cli/command@0.3.0`.** -/
theorem cat_hasWorld : HasWorld3 Cat.File.bytes Cli.command :=
  ⟨_, Cat.P3.parse_eq, by decide +kernel⟩

/-- `Cat` has async built-ins at the top level. -/
theorem cat_not_topV0 : BinaryP3.topV0 Cat.P3.ast = false := by decide +kernel

/-- **Refuted: the pass-1 statement `Task.parses`** (the old grammar rejects the file). -/
theorem cat_not_parses : ¬ Task.parses Cat.File.bytes :=
  not_parses_of Cat.P3.parse_eq cat_not_topV0

/-! ### `CatDebug` -/

/-- **`CatDebug` parses** under the grammar with async built-ins. -/
theorem catDebug_parses : Parses3 CatDebug.File.bytes := ⟨_, CatDebug.P3.parse_eq⟩

/-- **`CatDebug` is well scoped.** -/
theorem catDebug_valid : Valid3 CatDebug.File.bytes :=
  ⟨_, CatDebug.P3.parse_eq, by decide +kernel⟩

/-- **`CatDebug` targets `wasi:cli/command@0.3.0`.** -/
theorem catDebug_hasWorld : HasWorld3 CatDebug.File.bytes Cli.command :=
  ⟨_, CatDebug.P3.parse_eq, by decide +kernel⟩

/-- `CatDebug` has async built-ins at the top level. -/
theorem catDebug_not_topV0 : BinaryP3.topV0 CatDebug.P3.ast = false := by decide +kernel

/-- **Refuted: the pass-1 statement `Task.parses`** (the old grammar rejects the file). -/
theorem catDebug_not_parses : ¬ Task.parses CatDebug.File.bytes :=
  not_parses_of CatDebug.P3.parse_eq catDebug_not_topV0

/-! ### `targets` is not vacuous -/

open Silmaril.Wasm.Component.Binary in
/-- `Cli.command` with the environment import renamed to `@0.2.0`. -/
def commandNoEnv : Silmaril.Wasm.Wit.Project.WorldType :=
  Cli.command.set 1 (.import ⟨"wasi:cli/environment@0.2.0", .plain0⟩ (.instance 0))

open Silmaril.Wasm.Component.Binary in
/-- `Cli.command` with `stdout.write-via-stream` taking a `stream<u16>`. -/
def commandBadStdout : Silmaril.Wasm.Wit.Project.WorldType :=
  Cli.command.set 9 (.inst (.type (.instance (Cli.useT 3 "error-code" ++
    [.type (.val (.stream (some (.prim .u16)))),
     .type (.val (.result none (some (.idx 1)))),
     .type (.val (.future (some (.idx 3)))),
     .type (.func ⟨[("data", .idx 2)], some (.idx 4), false⟩),
     .export "write-via-stream" (.func 5)]))))

/-- `echo` needs `wasi:cli/environment@0.3.0`; `hello` does not. -/
theorem echo_needs_environment :
    BinaryP3.World.targets Echo.P3.ast commandNoEnv = false ∧
      BinaryP3.World.targets Hello.P3.ast commandNoEnv = true := by
  constructor <;> decide +kernel

/-- `hello` does not target a world whose stdout takes `stream<u16>`. -/
theorem hello_not_badStdout : BinaryP3.World.targets Hello.P3.ast commandBadStdout = false := by
  decide +kernel

/-- `wellScopedC3` checks the type operand of `stream.new`. -/
theorem hello_unbound_stream :
    BinaryP3.wellScopedC3 (.mk (Hello.P3.secs ++ [.canons [.streamNew 999]])) = false := by
  decide +kernel

/-- **Refuted: the pass-1 behavioural statements**, for every semantics `den`. -/
theorem not_pass1_behaviour (den : Silmaril.Wasm.Component.Binary.Ast → Silmaril.Wasi.Versions.P3.p3World.Model) :
    ¬ Task.hello_prints den ∧ ¬ Task.cat_copies den ∧ ¬ Task.catDebug_copies den ∧
      ¬ Task.cat_release_debug den :=
  ⟨not_everyHost hello_not_parses den _, not_everyHost cat_not_parses den _,
    not_everyHost catDebug_not_parses den _, fun ⟨a, _, ha, _, _⟩ => cat_not_parses ⟨a, ha⟩⟩

/-- **Refuted: the pass-1 statement for `echo`**, for every world, semantics and theory. -/
theorem not_echo_prints {S : Type} (W : Silmaril.Wasi.World) (den : Silmaril.Wasm.Component.Binary.Ast → W.Model)
    (T : Silmaril.Wasm.Resource.Protocol S Silmaril.Wasi.WEv) (args : List String) :
    ¬ Task.echo_prints W den T args :=
  fun ⟨c, hc, _⟩ => echo_not_parses ⟨c, hc⟩

end Silmaril.Project.WasmP3Rust

/-!
## What is wrong with the pass-1 behavioural targets

**PROVED** (`helloG_xtrace`, `everyHost_hello_no_ok`): `Task.everyHost b den helloG` checks
`helloG` on the *export* events of linked plays (`xtrace`), which contain no import answers, so
the stdout bytes `helloG` reads are empty there; it then holds only if `run` never returns `ok`.
So `Task.hello_prints den` (and `Task.cat_copies`, `Task.echo_prints` alike) can hold only for a
`den` under which `run` never succeeds on any host of the theory: it cannot be proved for a
faithful semantics. `Silmaril.Project.WasmP3Rust.TasksP3.Defs` restates the targets with
`WasiSat`, which reads all events.

**PROVED** as well (`<n>_not_parses`, `not_pass1_behaviour`, `not_echo_prints`, above): the
old statements also require `Binary.parse` (the grammar) to accept the file, which
it does not; so they are false for every `den`.

-/

namespace Silmaril.Project.WasmP3Rust

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Project.Shapes.Component (WasiEveryHost)

theorem osRun3_noImp (ch : Silmaril.Process.LPS.Word) :
    ∀ (q : OsSt) (t : List WEv), (∀ e ∈ t, e.isImp = false) → osRun3 ch q t = []
  | _, [], _ => rfl
  | q, e :: t, h => by
    have he : osStep3 ch q e = (q, []) := by
      have := h e List.mem_cons_self
      cases e <;> first | rfl | simp [WEv.isImp] at this
    simp only [osRun3, he, List.nil_append]
    exact osRun3_noImp ch q t fun e' he' => h e' (List.mem_cons_of_mem _ he')

/-- No output without import answers. -/
theorem stdoutBytes_noImp {t : List WEv} (h : ∀ e ∈ t, e.isImp = false) : stdoutBytes t = [] := by
  simp only [stdoutBytes, osTrace3, osRun3_noImp 0 {} t h, List.filterMap_nil]

/-- The export events of a linked play carry no import answers. -/
theorem xtrace_noImp {Y : Sig.{0}} {X : Set FnName} (p : List (Move Y (nsig X))) :
    ∀ e ∈ xtrace p, e.isImp = false := by
  intro e he
  obtain ⟨m, -, hm⟩ := List.mem_filterMap.1 he
  rcases m with _ | (⟨q⟩ | ⟨q, n⟩) <;> simp only [xev, Option.some.injEq, reduceCtorEq] at hm <;>
    (subst hm; rfl)

theorem ofTraces_run_some {P : List WEv → Bool} :
    ∀ (q t : List WEv), ((ofTraces P).run q t).isSome → t ≠ [] → P (q ++ t) = true
  | _, [], _, h => absurd rfl h
  | q, e :: t, h, _ => by
    have hs : (ofTraces P).step q e = if P (q ++ [e]) then some (q ++ [e]) else none := rfl
    rw [Protocol.run_cons, hs] at h
    split at h
    · rename_i hp
      rw [Option.bind_some] at h
      cases t with
      | nil => exact hp
      | cons e' t' =>
        have := ofTraces_run_some (q ++ [e]) (e' :: t') h (List.cons_ne_nil _ _)
        rwa [List.append_assoc, List.singleton_append] at this
    · simp at h

theorem loop_ne_nil (bs : ByteArray) : ∀ (n i : Nat) (r : List UInt8), bs.size - i = n →
    (r ≠ [] ∨ i < bs.size) → ByteArray.toList.loop bs i r ≠ []
  | 0, i, r, hn, h => by
    rw [ByteArray.toList.loop]
    have hi : ¬ i < bs.size := by omega
    simp only [hi, ite_false, ne_eq, List.reverse_eq_nil_iff]
    rcases h with h | h
    · exact h
    · exact absurd h hi
  | n + 1, i, r, hn, h => by
    rw [ByteArray.toList.loop]
    split
    · exact loop_ne_nil bs n (i + 1) _ (by omega) (.inl (List.cons_ne_nil _ _))
    · rename_i hi
      simp only [ne_eq, List.reverse_eq_nil_iff]
      rcases h with h | h
      · exact h
      · exact absurd h hi

theorem utf8_hello_ne_nil : utf8 "Hello, WASI 0.3!\n" ≠ [] := by
  have hs : "Hello, WASI 0.3!\n".toUTF8.size = 17 := by simp [String.size_toByteArray]; decide
  simp only [utf8, ne_eq, List.map_eq_nil_iff]
  exact loop_ne_nil _ _ 0 [] rfl (.inr (by rw [hs]; decide))

/-- **`helloG` on export events**: accepted only if `run` never returned `ok`. -/
theorem helloG_xtrace {t : List WEv} (h : ∀ e ∈ t, e.isImp = false) (hg : helloG.Accepts t) :
    runOk t = false := by
  cases t with
  | nil => rfl
  | cons e t' =>
    have hp := ofTraces_run_some (P := fun t => (stdoutBytes t).isPrefixOf
      (utf8 "Hello, WASI 0.3!\n") && (!runOk t || stdoutBytes t == utf8 "Hello, WASI 0.3!\n"))
      [] (e :: t') hg (List.cons_ne_nil _ _)
    rw [List.nil_append, stdoutBytes_noImp h] at hp
    cases hr : runOk (e :: t')
    · rfl
    · have hne : ([] == utf8 "Hello, WASI 0.3!\n") = false := by
        cases hu : utf8 "Hello, WASI 0.3!\n" with
        | nil => exact absurd hu utf8_hello_ne_nil
        | cons _ _ => rfl
      simp [hr, hne] at hp

/-- **The pass-1 target `Task.everyHost … helloG` forbids a successful `run`**: under it, no
linked play over a host of the theory has `run` return `ok`. -/
theorem everyHost_hello_no_ok {W : World} {S : Type} {σ : W.Model} {T : Protocol S WEv}
    (h : WasiEveryHost σ T helloG) (Y : Sig.{0}) (η : Host Y W.imports)
    (hη : (hostSat T.Accepts).holds η) (p : List (Move Y (nsig W.exports))) (hp : p ∈ link η σ) :
    runOk (xtrace p) = false :=
  helloG_xtrace (xtrace_noImp p) (h Y η hη p hp)

end Silmaril.Project.WasmP3Rust

end
