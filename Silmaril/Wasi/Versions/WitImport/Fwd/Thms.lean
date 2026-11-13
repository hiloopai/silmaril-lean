module

public import Silmaril.Wasi.Versions.WitImport.Fwd.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables3.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables29.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables29.Defs
public import Silmaril.Wasi.Versions.Stateful.Thms
public import Silmaril.Wasi.Versions.WitImport.FwdPairs.Small.Thms
public import Silmaril.Wasi.Versions.WitImport.FwdPairs.Small29.Thms
public import Silmaril.Wasi.Versions.WitImport.FwdPairs.Fs.Thms
public import Silmaril.Wasi.Versions.WitImport.FwdPairs.Fs29.Thms
public import Silmaril.Wasi.Versions.WitImport.FwdPairs.Sock.Thms
public import Silmaril.Wasi.Versions.WitImport.FwdPairs.Sock29.Thms
public import Silmaril.Wasi.Versions.WitImport.FwdPairs.Http.Thms
public import Silmaril.Wasi.Versions.WitImport.FwdPairs.Http29.Thms

@[expose] public section

/-!
# Forwarding adapters are models of the WIT typing

* **`fwd_typed`**: for a forwarding map whose pairs have free signatures with the same types
  (`FwdOk P Q M`), a typed answer of the imported function is a typed answer of the exported one.
* **`fwd_model`**: over every host of the import package's typing `witRTh P`, the forwarder
  `fwdBody M` is a model of the export package's typing `witRTh Q`.
* **`fwdOk_all`**: `FwdOk` holds, by kernel evaluation, for the computed pairs `fwdPairs` in
  both directions between the 0.3.2 packages and the 0.2.12 and 0.2.9 packages of `random`,
  `clocks`, `cli`, `filesystem`, `sockets` and `http`.
* **`fwd3_names`**, **`fwd2_names`**: the pairs between 0.2.12 and 0.3.2, sixteen in each
  direction: `wasi:random` (four byte and `u64` functions), `wasi:cli` (`get-environment`,
  `get-arguments`, `exit`, `exit-with-code`, the three `get-terminal-*`), `wasi:filesystem`
  (`descriptor.is-same-object`, `get-directories`) and `wasi:http` (`[constructor]fields`,
  `fields.clone`, `[constructor]request-options`). `wasi:clocks` and `wasi:sockets` have none:
  every common function mentions a named type.

These are relations (b) and (c) at the level of the WIT typing only: the forwarder says nothing
about behaviour. For `wasi:random` the behavioural relations are `p3OverP2R_model` and
`p2OverP3R_model` (`Silmaril.Wasi.Versions.Random.Over`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions (WpInv ag_of_wpInv link_model ofSBody)
open Silmaril.Games (Sig)

/-- The answer check depends on the result type only. -/
theorem resOk_congr_res {s s' : Binary.Sig} (h : s.result = s'.result) (r : Option (List Val)) :
    resOk s r = resOk s' r := by
  unfold resOk
  rw [h]

/-- The argument check depends on the parameter types only. -/
theorem argsOk_congr_params {s s' : Binary.Sig} (h : s.params.map Prod.snd = s'.params.map Prod.snd)
    (a : List Val) : argsOk s a = argsOk s' a := by
  unfold argsOk
  rw [h]

/-- Free signatures with the same types give the same resolved check, in any environments. -/
theorem witR_sig_congr {E E' : TyEnv} {i i' : Binary.IfaceName} {s s' : Binary.Sig}
    (hs : sigFree s = true) (hs' : sigFree s' = true) (ht : sigTypes s = sigTypes s')
    (a : List Val) (r : Option (List Val)) :
    (!argsOkR E i s a || resOkR E i s r) = (!argsOkR E' i' s' a || resOkR E' i' s' r) := by
  rw [argsOkR_free hs, resOkR_free hs, argsOkR_free hs', resOkR_free hs',
    argsOk_congr_params (congrArg Prod.fst ht), resOk_congr_res (congrArg Prod.snd ht)]

/-- An entry of a forwardable map: both lookups succeed, with free signatures of the same
types. -/
theorem fwd_entry {P Q : RPkg} {M : FwdMap} (hM : FwdOk P Q M = true) {fg : FnName × FnName}
    (hm : fg ∈ M) : ∃ i s i' s', Q.1.lookup fg.1 = some (i, s) ∧ P.1.lookup fg.2 = some (i', s') ∧
      sigFree s = true ∧ sigFree s' = true ∧ sigTypes s = sigTypes s' := by
  have he := List.all_eq_true.1 hM fg hm
  revert he
  cases hq : Q.1.lookup fg.1 with
  | none => simp
  | some x =>
    cases hp : P.1.lookup fg.2 with
    | none => simp
    | some y =>
      intro he
      have he' : (sigFree x.2 = true ∧ sigFree y.2 = true) ∧ sigTypes x.2 = sigTypes y.2 := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using he
      exact ⟨x.1, x.2, y.1, y.2, rfl, rfl, he'.1.1, he'.1.2, he'.2⟩

/-- **A typed answer of the imported function is a typed answer of the exported one.** -/
theorem fwd_typed {P Q : RPkg} {M : FwdMap} (hM : FwdOk P Q M = true) {f : FnName}
    (hf : f ∈ fwdX M) (a : List Val) (r : Option (List Val))
    (h : witROk P (.imp (fwdTo M f) a r) = true) : witROk Q (.imp f a r) = true := by
  obtain ⟨⟨f', g⟩, hm, rfl⟩ := List.mem_map.1 hf
  obtain ⟨g', hg'⟩ := lookup_some_of_mem hm
  have hto : fwdTo M f' = g' := by simp [fwdTo, hg']
  obtain ⟨i, s, i', s', hq, hp, hs, hs', ht⟩ := fwd_entry hM (rlookup_mem hg')
  have hP : (!argsOkR P.2 i' s' a || resOkR P.2 i' s' r) = true := by
    simpa [witROk, hto, hp] using h
  have hQ : (!argsOkR Q.2 i s a || resOkR Q.2 i s r) = true := by
    rw [witR_sig_congr hs hs' ht a r]
    exact hP
  simpa [witROk, hq] using hQ

/-- A pointwise step succeeds exactly on accepted events. -/
theorem fwdP_step {ok : WEv → Bool} {q q' : Unit} {e : WEv}
    (h : (pointwise ok).step q e = some q') : ok e = true := by
  by_contra hn
  simp [pointwise, hn] at h

/-- A pointwise step on an accepted event. -/
theorem fwdP_step_of {ok : WEv → Bool} {q : Unit} {e : WEv} (h : ok e = true) :
    (pointwise ok).step q e = some () := by
  simp [pointwise, h]

/-- The invariant of the forwarder (none needed). -/
theorem fwd_inv {P Q : RPkg} {M : FwdMap} (hM : FwdOk P Q M = true) :
    WpInv (fwdBody M) () (witRTh P) (witRTh Q) (fun _ _ _ => True) where
  init := trivial
  call := fun _ _ _ q _ _ _ h => ⟨(), fwdP_step_of (fwd_typed hM q.1.2 _ _ (fwdP_step h)), trivial⟩

/-- **The forwarder is a model of the export package's typing over every host of the import
package's typing.** -/
theorem fwd_model {Y : Sig.{0}} {P Q : RPkg} {M : FwdMap} (hM : FwdOk P Q M = true)
    {η : Host Y (fwdI M)} (hη : (hostSat (witRTh P).Accepts).holds η) :
    (hostSat (witRTh Q).Accepts).holds (link η (ofSBody (fwdBody M) ())) :=
  link_model (ag_of_wpInv (fwd_inv hM)) hη

/-- The package pairs: (0.2.x, 0.3.2). -/
def fwdPkgs : List (RPkg × RPkg) :=
  [(rand2P, rand3P), (clocks2P, clocks3P), (cli2P, cli3P), (fs2P, fs3P), (sock2P, sock3P),
    (http2P, http3P), (rand29P, rand3P), (clocks29P, clocks3P), (cli29P, cli3P), (fs29P, fs3P),
    (sock29P, sock3P), (http29P, http3P)]

/-- **The computed pairs are forwardable, in both directions** (kernel evaluation, one pair at a
time in the `FwdPairs` modules, assembled here by rewriting). -/
theorem fwdOk_all :
    fwdPkgs.all (fun pq => FwdOk pq.1 pq.2 (fwdPairs pq.1 pq.2) &&
      FwdOk pq.2 pq.1 (fwdPairs pq.2 pq.1)) = true := by
  simp only [fwdPkgs, List.all_cons, List.all_nil, Bool.and_true, fwdOk_rand3, fwdOk_clocks3,
    fwdOk_cli3, fwdOk_fs3, fwdOk_sock3, fwdOk_http3, fwdOk_rand2, fwdOk_clocks2, fwdOk_cli2,
    fwdOk_fs2, fwdOk_sock2, fwdOk_http2, fwdOk_rand3_29, fwdOk_clocks3_29, fwdOk_cli3_29,
    fwdOk_fs3_29, fwdOk_sock3_29, fwdOk_http3_29, fwdOk_rand29, fwdOk_clocks29, fwdOk_cli29,
    fwdOk_fs29, fwdOk_sock29, fwdOk_http29]

/-- The interface and name of each exported function. -/
def fwdNames (M : FwdMap) : List (String × String) := M.map fun x => (x.1.iface, x.1.fn)

/-- **0.3.2 over 0.2.12**: the exported 0.3 functions. -/
theorem fwd3_names :
    fwdNames ((fwdPkgs.take 6).flatMap fun pq => fwdPairs pq.1 pq.2) =
      [("wasi:random/insecure@0.3.2", "get-insecure-random-bytes"),
       ("wasi:random/insecure@0.3.2", "get-insecure-random-u64"),
       ("wasi:random/random@0.3.2", "get-random-bytes"),
       ("wasi:random/random@0.3.2", "get-random-u64"),
       ("wasi:cli/environment@0.3.2", "get-environment"),
       ("wasi:cli/environment@0.3.2", "get-arguments"),
       ("wasi:cli/exit@0.3.2", "exit"), ("wasi:cli/exit@0.3.2", "exit-with-code"),
       ("wasi:cli/terminal-stdin@0.3.2", "get-terminal-stdin"),
       ("wasi:cli/terminal-stdout@0.3.2", "get-terminal-stdout"),
       ("wasi:cli/terminal-stderr@0.3.2", "get-terminal-stderr"),
       ("wasi:filesystem/types@0.3.2", "[method]descriptor.is-same-object"),
       ("wasi:filesystem/preopens@0.3.2", "get-directories"),
       ("wasi:http/types@0.3.2", "[constructor]fields"),
       ("wasi:http/types@0.3.2", "[method]fields.clone"),
       ("wasi:http/types@0.3.2", "[constructor]request-options")] := by
  rw [show fwdPkgs.take 6 = [(rand2P, rand3P), (clocks2P, clocks3P), (cli2P, cli3P), (fs2P, fs3P),
      (sock2P, sock3P), (http2P, http3P)] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, fwdPairs_rand3, fwdPairs_clocks3, fwdPairs_cli3,
    fwdPairs_fs3, fwdPairs_sock3, fwdPairs_http3]
  decide +kernel

/-- **0.2.12 over 0.3.2**: the exported 0.2 functions (the same sixteen). -/
theorem fwd2_names :
    fwdNames ((fwdPkgs.take 6).flatMap fun pq => fwdPairs pq.2 pq.1) =
      [("wasi:random/insecure", "get-insecure-random-bytes"),
       ("wasi:random/insecure", "get-insecure-random-u64"),
       ("wasi:random/random", "get-random-bytes"), ("wasi:random/random", "get-random-u64"),
       ("wasi:cli/environment", "get-environment"), ("wasi:cli/environment", "get-arguments"),
       ("wasi:cli/exit", "exit"), ("wasi:cli/exit", "exit-with-code"),
       ("wasi:cli/terminal-stdin", "get-terminal-stdin"),
       ("wasi:cli/terminal-stdout", "get-terminal-stdout"),
       ("wasi:cli/terminal-stderr", "get-terminal-stderr"),
       ("wasi:filesystem/types", "[method]descriptor.is-same-object"),
       ("wasi:filesystem/preopens", "get-directories"),
       ("wasi:http/types", "[constructor]fields"), ("wasi:http/types", "[method]fields.clone"),
       ("wasi:http/types", "[constructor]request-options")] := by
  rw [show fwdPkgs.take 6 = [(rand2P, rand3P), (clocks2P, clocks3P), (cli2P, cli3P), (fs2P, fs3P),
      (sock2P, sock3P), (http2P, http3P)] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, fwdPairs_rand2, fwdPairs_clocks2, fwdPairs_cli2,
    fwdPairs_fs2, fwdPairs_sock2, fwdPairs_http2]
  decide +kernel

/-- **0.2.9 over 0.3.2**: the exported 0.2.9 functions: the 0.2.12 ones without
`exit-with-code`. -/
theorem fwd29_names :
    fwdNames ((fwdPkgs.drop 6).flatMap fun pq => fwdPairs pq.2 pq.1) =
      (fwdNames ((fwdPkgs.take 6).flatMap fun pq => fwdPairs pq.2 pq.1)).filter
        (·.2 != "exit-with-code") := by
  rw [show fwdPkgs.drop 6 = [(rand29P, rand3P), (clocks29P, clocks3P), (cli29P, cli3P),
      (fs29P, fs3P), (sock29P, sock3P), (http29P, http3P)] from rfl]
  rw [show fwdPkgs.take 6 = [(rand2P, rand3P), (clocks2P, clocks3P), (cli2P, cli3P), (fs2P, fs3P),
      (sock2P, sock3P), (http2P, http3P)] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, fwdPairs_rand29, fwdPairs_clocks29,
    fwdPairs_cli29, fwdPairs_fs29, fwdPairs_sock29, fwdPairs_http29, fwdPairs_rand2,
    fwdPairs_clocks2, fwdPairs_cli2, fwdPairs_fs2, fwdPairs_sock2, fwdPairs_http2]
  decide +kernel

end Silmaril.Wasi.Versions.WitImport
