# Finite machines (`Silmaril.Automata`)

Finite state machines are silmaril's first **basic object kind**. A basic object has:

- typed Lean values;
- a named document form, stored as TOML and JSON;
- a proof that the typed values and the document agree;
- a content identity;
- categories, an institution and standard problem shapes.

The HTTP/2 stream state machine (RFC 9113 §5.1) is the first worked example.

## Layers

| Layer | Lean | What it is |
| --- | --- | --- |
| Names | `Automata.Named` | `FinNamed α`: a finite list of the elements, each with a distinct name. The command `silmaril_finite T` derives it, together with `Fintype`, for an inductive type `T` whose constructor arguments are themselves `FinNamed`. |
| Machines | `Automata.Machine` | `DMachine S L` is a deterministic partial machine, and `NMachine S L` a nondeterministic one with finite successor sets. Products are `prod`; `Marked.toNFA` gives a CSLib NFA. Relational machines **are** CSLib's `Cslib.LTS`, and unlabelled graphs are `LTS.UnlabelledTr`. `ReachVia lts P a b` is reachability by labels in `P`. `Marks S` is the marking layer (initial, accepting, rejecting and error states), and `Marked` is a machine together with its marks. |
| Decision procedures | `Automata.Decide` | Verified fixpoints on `Finset`s: `reachSet`, `simSet` and `bisimSet`. They are proved exact against `ReachVia` and CSLib's `Similarity` and `Bisimilarity`, so `decide` (or `machine_decide`) decides these problems. |
| Documents | `Automata.Spec` | `Spec` holds the states, labels and edges as names; `Layers` holds the marks. `Document` adds an identifier. `DMachine.toSpec` turns a typed machine into a spec, and `Spec.Typed` turns a spec back into a machine. There are JSON codecs, a TOML emitter, `Spec.canon` and `Document.canonJson`. |
| Categories | `Automata.Category` | `TMach`: typed machines with strict homomorphisms. `JMach`: valid deterministic JSON machines. `MarkedMach`, `Graph`, the functor into CSLib's `LTSCat`, and forgetful functors between them. |
| Institution | `Automata.Institution` | The machine institution, `inst : Sig ⥤ Room`, and its direct form `classic`. |
| Shapes | `Automata.Shapes` | `silmaril.shapes.machine.*`: reachability, set reachability, simulation, bisimulation, sentence satisfaction, word acceptance and language nonemptiness for typed machines; reachability, simulation, bisimulation and word acceptance for JSON machines, decidable without a typed machine. |
| Registry | `Automata.Registry` | The `machine` and `machine_binding` record kinds, and `#silmaril_machine_toml`. |

## Products and coproducts (`Automata.Ops`)

`RelMach` is the category of relational machines (CSLib LTSs) whose morphisms map states and
labels and preserve transitions. In it, `prod` (both components step, labels `L × K`) and `coprod`
(each side's transitions, labels `L ⊕ K`) are a genuine categorical product and coproduct
(`prodIsLimit`, `coprodIsColimit`). `TMach.toRelMach` sends typed machines there.

The strict-homomorphism category `TMach` does not have these: a projection would have to reflect
rejections that the product introduces.

The synchronous product `DMachine.prod` is different: both machines take the same label, and it
recognizes the intersection of the languages. It is the categorical product restricted to
diagonal labels (`sync_eq_prod_diag`).

## Main theorems

All of them use only the standard axioms.

- **Typed and JSON machines agree.**
  - `toSpec_step_iff`: the spec of a typed machine has exactly its steps, on names.
  - `stepFn_toSpec`: the generated step function is the typed one, mapped to names.
  - `toSpec_wf` and `toSpec_deterministic`.
- **Canonical identity.**
  - `Spec.canon_eq_iff`: two specs have the same canonical form iff they have the same states, labels and edges.
  - `canon_canon`.
  - `canon_eq_of_equivB`: the kernel-evaluable check that bindings use.
- **Attachments.** `step_iff_of_canon_eq`: two typed machines over different inductive types, bound to one document, have the same steps on corresponding names.
- **Categories.**
  - `JMach.equivalence : JMach ≌ TMach`. The functor is fully faithful by construction, because JSON machine morphisms are strict homomorphisms of the machines the specs denote. It is essentially surjective because every typed machine is isomorphic, through names, to the machine its spec denotes.
  - `MarkedMach.forget` and `toLTSCat` are faithful.
- **Institution.**
  - `sat_map_iff` is the satisfaction condition, and `Sen.map_id` and `Sen.map_comp` show that sentence translation is functorial.
  - `sat_toSpec_iff`: a typed machine and the model of its spec satisfy the same sentences, up to renaming to names.
- **Decision procedures.** `mem_reachSet`, `mem_simSet` and `mem_bisimSet`. They rest on `iterate_fix_of_inflationary` and `iterate_fix_of_deflationary`: an iteration on the finsets of a finite type reaches its fixpoint within `Fintype.card` steps.
- **Shapes.** `jsonReach_iff_of_bound` and `jsonBisimilar_iff_of_bound`: a decision on the typed side answers the JSON problem.

## The institution, precisely

| Part | Definition |
| --- | --- |
| Signatures | `Sig`: a type of state names `St` and a type of labels `Lb`. Morphisms are pairs of maps. |
| Sentences | `Sen Σ` is built from `step a l b` and `reach ls a b` (reachable using only labels in the list `ls`), closed under negation and conjunction. |
| Translation | `Sen.map σ` renames names and labels. |
| Models | `Model Σ`: a CSLib LTS over some state type, labelled by `Σ.Lb`, with an interpretation `ι` of the names. Models form a discrete category. |
| Reduct | Along `σ`, keep the states, take the transitions of `σ.lb l` as the transitions of `l`, and interpret the names through `σ.st`. |

Satisfaction is invariant under this reduct, which is the satisfaction condition. That is why reachability is *label restricted*. A reduct sees only the labels in the image of `σ`, so unrestricted reachability and deadlock freedom ("some label is enabled") are **not** invariant, and they are not sentences. They remain shapes over single machines. Simulation and bisimulation relate two models, so they are shapes and not sentences.

## Documents, sources and the project database

Machine documents are TOML records files under `silmaril/machines/`, read by `silmaril load`. Elaboration only reads files: `#silmaril_machine_toml "id" M marks` prints the table of a typed machine for the author to save.

```toml
[[machine]]
name = "silmaril.selftest.door"
states = ["closed", "locked", "open"]
labels = ["close", "lock", "open", "unlock"]
edges = [["closed", "lock", "locked"], ["closed", "open", "open"], ["locked", "unlock", "closed"], ["open", "close", "closed"]]
initial = ["closed"]

[[machine_binding]]
name = "silmaril.selftest.door.typed"
machine = "silmaril.selftest.door"
decl = "ProjectSelfTest.Machines.Door.machine"
marks = "ProjectSelfTest.Machines.Door.marks"
```

A `machine` record:

- defines the Lean constant `silmaril.selftest.door : Document`, so the JSON machine can be reasoned about on its own;
- fills `decl`;
- fills `deterministic`, checked by evaluation;
- fills `canonical`, the canonical JSON and the content identity.

A `machine_binding` elaborates the theorem `<name>.bound : (toSpec decl).canon = doc.spec.canon`, and `<name>.layers` for marks. The kernel checks it, so a binding exists only if the typed machine is the document. One document may carry several bindings. The self-test binds `silmaril.selftest.door` to two inductive types whose constructors are declared in different orders.

In the database (`sil project`), machines are objects of kind `machine` in the `machines` table, which has counts, `deterministic` and `canonical`. Bindings are in the `machine_bindings` table. The explorer has a **Machines** tab. Each machine page draws the graph from the canonical JSON: initial states have a thick border, accepting states a double border, rejecting states are orange and error states red. The page also lists the bindings.

## Names and identity

- **Document identifiers** use the record-name grammar: dot-separated `[a-z0-9_-]` segments. They are unique per kind in a project, as for every other object, and the project database gives them a sid.
- **State and label names** are local to a document. A derived instance names a nullary constructor `c`, a constructor with arguments `c(a,…)` and a structure `(a,…)`. The derivation checks that the names are distinct when it runs.
- **Content identity** is the canonical form, which sorts and deduplicates states, labels and edges. Declaration order is presentation, not identity. The canonical JSON text is what content addressing (CAS) or DASL identities would hash later. That is **not** implemented here.

## Coverage and boundary

Everything listed as deferred in the first version of this page is now implemented and proved:

| Former gap | Now |
| --- | --- |
| `FinNamed` for `Option`, `Prod`, `Sum` | Instances in `Named.Thms`. Pair components escape `,` and `\`, so distinctness is a theorem (`pairName_inj`) for every component type. |
| JSON codec round trip | `Document.ofJson?_toJson` and `Document.fromJson?_toJson`, with the same results for `Spec`, `Layers`, `Edge` and string lists, at the level of `Lean.Json` values. |
| Nondeterministic typed machines | `NMachine` (finite successor sets), `NMachine.toSpec` with `NMachine.toSpec_step_iff`. Bindings accept `NMachine`s, as in the self-test `silmaril.selftest.coin`. The decision procedures are generic over `NMachine`. |
| Marked category equivalence | `JMarked.equivalence : JMarked ≌ MarkedMach` (documents with layers), plus `JMarked.forget`. |
| Word problems | Shapes `accepts`, `nonempty` and `json.accepts`, all decidable. `Marked.nonempty_iff_reach` reduces nonemptiness to reachability. |
| Deciding unbound JSON machines | `Spec.restrict` with `jsonReach_iff_restrict`, `jsonSimulates_iff_restrict`, `jsonBisimilar_iff_restrict` and `jsonAccepts_iff`. Every JSON shape is `Decidable` on its own. |
| CSLib DFA/NFA bridge | `Marked.toNFA : NA.FinAcc` with `accepts_toNFA_iff` (same language). Runs are CSLib `MTr` (`run_some_iff_MTr`). |
| Composition | Synchronous products `DMachine.prod`, `NMachine.prod` and `Marked.prod`, with `accepts_prod_iff` (intersection). |

What remains outside this development, and why:

- **Text-level JSON.** Printing and parsing JSON text are Lean core's `Json.compress` and `Json.parse`. The round trip here is on `Lean.Json` values, where the codec lives.
- **Content addressing.** The canonical form (`Spec.canon`, `canon_eq_iff`) and its canonical JSON text are the content identity. Hashing it into a CID, or a DASL identity, is future project-database work and is deliberately not implemented here.
- **Nondeterministic categories.** The categories (`TMach`, `JMach`, `MarkedMach`, `JMarked`) are of deterministic machines with strict homomorphisms. Nondeterministic machines appear as LTSs in CSLib's `LTSCat`, through `toLTSCat` for deterministic ones.
- **Other compositions.** Products are implemented. Other compositions, such as sequential composition or the CFG composition this kind is meant to support, are future basic-object kinds.

## Checking

```sh
lake build --wfail +Silmaril.Automata.Shapes.Thms +Silmaril.Automata.Category.Thms \
  +Silmaril.Automata.Institution.Thms +Silmaril.Net.Http2.Stream.Thms ProjectSelfTest
make project-check   # the sil project self-test, golden examples/project/check.txt
```
