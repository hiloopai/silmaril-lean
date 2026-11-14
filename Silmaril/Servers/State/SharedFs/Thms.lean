module

public import Silmaril.Servers.State.SharedFs.Defs
public import Silmaril.Servers.State.OwnedFs.Thms
import Silmaril.Proofs.Servers.State.SharedFs

@[expose] public section

/-!
# State model (c), a shared file system: theorems (header)

PROVED (standard axioms), namespace `Silmaril.Servers.State.SharedFs`. Proofs in
`Silmaril.Proofs.Servers.State.SharedFs`.

Safety, whatever the environment does:

* **`static_safe`**: if the environment keeps an invariant `I` of the files (and the initial
  files satisfy it), each response of the static server to `r` is `staticAnswer loc fs r` for
  some files `fs` satisfying `I` (with `I := fun _ => True`: some files); the histories are
  linearizable with respect to that loose stateless specification (`static_linearizable`);
* **`store_safe`**: each response of the store is a `storeStep` answer from some store.

Functional correctness for files nobody else touches:

* **`static_untouched`**: a request whose file (if any) the environment never touches is
  answered as with the initial files, `staticAnswer loc fs₀ r`;
* **`store_refines`**: if the environment never touches a key's file (it may change every
  other file in the preopen), the store refines the component-state store holding
  `view enc fs₀`, and is linearizable with respect to `storeStep` (`store_linearizable`).

Linearizability on the untouched keys, when the environment changes the files of other keys:

* **`store_linearizable_on`**: if the environment never touches the file of a key of `K` (it
  may change the files of every other key, and every other file), the store is linearizable
  with respect to `kvOn K` from the initial store on `K`, and refines its closed server
  (`store_refines_on`);
* `kvOn_true`: on all keys, `kvOn` is the component-state store `kv`.
-/

namespace Silmaril.Servers.State.SharedFs

open Silmaril.Net.Http Silmaril.Cli Silmaril.Servers.State.OwnedFs Silmaril.Servers.State.Component

theorem static_linearizable (loc : Target → Option FPath) {fs₀ : Fs} {E : Fs → Fs → Prop}
    {I : Fs → Prop} (h₀ : I fs₀) (hE : Keeps E I) :
    (sharedStatic loc fs₀ E).Sat (Linearizable (staticSafe loc I) ()) :=
  (Proofs.Servers.State.SharedFs.staticSafeAbs loc h₀ hE).sat_linearizable

theorem static_safe {loc : Target → Option FPath} {fs₀ : Fs} {E : Fs → Fs → Prop}
    {I : Fs → Prop} (h₀ : I fs₀) (hE : Keeps E I) {H : Hist Request Response}
    (hH : (sharedStatic loc fs₀ E).Hists H) {i : Nat} {r : Request} {s : Response}
    (hc : Ev.call i r ∈ H) (hr : Ev.ret i s ∈ H) : ∃ fs, I fs ∧ s = staticAnswer loc fs r :=
  let ⟨_, _, h⟩ := (Proofs.Servers.State.SharedFs.staticSafeAbs loc h₀ hE).sat_answer hH hc hr; h

theorem static_untouched {loc : Target → Option FPath} {fs₀ : Fs} {E : Fs → Fs → Prop}
    {P : FPath → Prop} (hE : Untouched E P) {H : Hist Request Response}
    (hH : (sharedStatic loc fs₀ E).Hists H) {i : Nat} {r : Request} {s : Response}
    (hc : Ev.call i r ∈ H) (hr : Ev.ret i s ∈ H) (hP : ∀ p, loc r.target = some p → P p) :
    s = staticAnswer loc fs₀ r := by
  obtain ⟨fs, hfs, rfl⟩ := static_safe (I := fun fs => ∀ p, P p → fs p = fs₀ p)
    (fun _ _ => rfl) (fun s s' hs h p hp => (hE s s' h p hp).trans (hs p hp)) hH hc hr
  refine Proofs.Servers.State.SharedFs.staticAnswer_congr loc r ?_
  cases h : loc r.target with
  | none => rfl
  | some p => exact hfs p (hP p h)

theorem store_safe {enc : Target → FPath} (hinj : Function.Injective enc) {fs₀ : Fs}
    {E : Fs → Fs → Prop} {H : Hist Request Response} (hH : (sharedStore enc fs₀ E).Hists H)
    {i : Nat} {r : Request} {s : Response} (hc : Ev.call i r ∈ H) (hr : Ev.ret i s ∈ H) :
    ∃ S S', storeStep S r = (s, S') :=
  let ⟨_, _, h⟩ := (Proofs.Servers.State.SharedFs.storeSafeAbs hinj fs₀ E).sat_answer hH hc hr; h

theorem store_refines {enc : Target → FPath} (hinj : Function.Injective enc) (fs₀ : Fs)
    {E : Fs → Fs → Prop} (hE : Untouched E fun p => ∃ t, enc t = p) :
    (sharedStore enc fs₀ E).Refines (kvServer (view enc fs₀)) :=
  (Proofs.Servers.State.SharedFs.storeKeysAbs hinj fs₀ hE).refines

theorem store_linearizable {enc : Target → FPath} (hinj : Function.Injective enc) (fs₀ : Fs)
    {E : Fs → Fs → Prop} (hE : Untouched E fun p => ∃ t, enc t = p) :
    (sharedStore enc fs₀ E).Sat (Linearizable kv (view enc fs₀)) :=
  (Proofs.Servers.State.SharedFs.storeKeysAbs hinj fs₀ hE).sat_linearizable

theorem store_linearizable_on {enc : Target → FPath} (hinj : Function.Injective enc) (fs₀ : Fs)
    (K : Target → Prop) [DecidablePred K] {E : Fs → Fs → Prop}
    (hE : Untouched E fun p => ∃ t, K t ∧ enc t = p) :
    (sharedStore enc fs₀ E).Sat (Linearizable (kvOn K) (restrictKeys K (view enc fs₀))) :=
  (Proofs.Servers.State.SharedFs.storeOnAbs hinj fs₀ K hE).sat_linearizable

theorem store_refines_on {enc : Target → FPath} (hinj : Function.Injective enc) (fs₀ : Fs)
    (K : Target → Prop) [DecidablePred K] {E : Fs → Fs → Prop}
    (hE : Untouched E fun p => ∃ t, K t ∧ enc t = p) :
    (sharedStore enc fs₀ E).Refines (Server.closed (kvOn K) (restrictKeys K (view enc fs₀))) :=
  (Proofs.Servers.State.SharedFs.storeOnAbs hinj fs₀ K hE).refines

theorem kvOn_true (S : Store) (r : Request) (resp : Response) (S' : Store) :
    kvOn (fun _ => True) S r resp S' ↔ kv S r resp S' :=
  ⟨fun h => h.1 trivial, fun h => ⟨fun _ => h, fun h' => (h' trivial).elim⟩⟩

end Silmaril.Servers.State.SharedFs
