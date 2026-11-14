module

public import Silmaril.Wasi.Versions.WitImport.Dflt.Defs
public import Silmaril.Wasi.Versions.WitImport.RFree.Thms
public import Silmaril.Wasi.Versions.WitImport.RTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables3.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables29.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables29.Defs
public import Silmaril.Wasi.Theory.Thms
public import Silmaril.Wasi.Host.Thms

@[expose] public section

/-!
# The default host is a model of the imported typing

* **`dfltImpl_witR`**: for a package `P` with `Defaults P`, the default host `dfltImpl P` is a
  concrete model of the resolved WIT typing theory `witRTh P`: every answer it gives has the
  resolved result type of its function.
* **`rpkgs_defaults`**: `Defaults` holds, by kernel evaluation, for all twenty resolved packages:
  the 0.2.12 `io2P`, `clocks2P`, `cli2P`, `fs2P`, `rand2P`, `sock2P`, `http2P`, the 0.3.2
  `rand3P`, `clocks3P`, `cli3P`, `fs3P`, `sock3P`, `http3P`, and the 0.2.9 `io29P`, `clocks29P`,
  `cli29P`, `fs29P`, `rand29P`, `sock29P`, `http29P`.

So each imported typing theory has a concrete model, which answers every (stable) function of
every vendored 0.2.9, 0.2.12 and 0.3.2 package. This is consistency, not behaviour: the
default host never fails, returns empty lists and handle `0`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Games (Sig)

/-- Every answer of the default host has the resolved result type of its function. -/
theorem dfltImpl_ok {P : RPkg} (hP : Defaults P = true) (p : List WEv) (f : FnName)
    (a : List Silmaril.Wasm.Component.Val) : witROk P (.imp f a (dfltImpl P p f a)) = true := by
  cases h : P.1.lookup f with
  | none => simp [witROk, h]
  | some x =>
    obtain ⟨i, s⟩ := x
    have hm : (f, (i, s)) ∈ P.1 := rlookup_mem h
    have hd : resOkR P.2 i s (dfltAns P.2 i s) = true := List.all_eq_true.1 hP _ hm
    simp [witROk, dfltImpl, h, hd]

/-- The typing says nothing about events that are not answers. -/
theorem witROk_of_not_imp (P : RPkg) {e : WEv} (he : e.isImp = false) : witROk P e = true := by
  cases e <;> simp_all [witROk, WEv.isImp]

/-- **The default host is a concrete model of the resolved WIT typing theory.** -/
theorem dfltImpl_witR {Y : Sig.{0}} {I : Set FnName} {P : RPkg} (hP : Defaults P = true) :
    (hostSat (witRTh P).Accepts).holds (concrete (Y := Y) (I := I) (dfltImpl P)) :=
  concrete_sat _ fun _ ht => follows_pointwise (dfltImpl_ok hP) (fun _ he => witROk_of_not_imp P he) ht

/-- **Every resolved package has default answers** (kernel evaluation). -/
theorem rpkgs_defaults :
    [io2P, clocks2P, cli2P, fs2P, rand2P, sock2P, http2P, rand3P, clocks3P, cli3P, fs3P, sock3P,
      http3P, io29P, clocks29P, cli29P, fs29P, rand29P, sock29P, http29P].all Defaults = true := by
  decide +kernel

end Silmaril.Wasi.Versions.WitImport
