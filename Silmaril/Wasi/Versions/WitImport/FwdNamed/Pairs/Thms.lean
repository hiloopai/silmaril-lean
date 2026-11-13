module

public import Silmaril.Wasi.Versions.WitImport.FwdNamed.Thms
public import Silmaril.Wasi.Versions.WitImport.RTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables3.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables29.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables29.Defs

@[expose] public section

/-!
# Forwarding across named types between the vendored versions

The maps below were printed by evaluating `fwdPairsN` on the imported packages (`clocks`, `http`;
for `rand`, `cli`, `filesystem` and `sockets` it finds the same pairs as `fwdPairs`, for
`sockets` none, because every socket signature names an `error-code` whose cases differ). They
are not trusted: `FwdOkN` on each map is checked by the kernel, which is all `fwdN_model` needs.
That `fwdPairsN` computes exactly these maps is not kernel-checked here.

New compared with `fwdPairs` (free signatures):

* `wasi:clocks/monotonic-clock` `now`: `instant` (0.2) and `mark` (0.3) are both aliases of `u64`.
* `wasi:http/types` `[method]fields.get`, `[method]fields.has`: `field-name` is an alias of
  `field-key = string` in 0.2 and of `string` in 0.3 (two alias steps against one).

The other three http pairs (`[constructor]fields`, `[method]fields.clone`,
`[constructor]request-options`) are already found by `fwdPairs`. The 0.2.x function names are
unversioned, so the same maps serve 0.2.9 and 0.2.12.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-- 0.3.2 `monotonic-clock.now` over 0.2.x. -/
def namedClocks3 : FwdMap :=
  [(⟨"wasi:clocks/monotonic-clock@0.3.2", "now"⟩, ⟨"wasi:clocks/monotonic-clock", "now"⟩)]

/-- 0.2.x `monotonic-clock.now` over 0.3.2. -/
def namedClocks2 : FwdMap :=
  [(⟨"wasi:clocks/monotonic-clock", "now"⟩, ⟨"wasi:clocks/monotonic-clock@0.3.2", "now"⟩)]

/-- 0.3.2 `fields` and `request-options` over 0.2.x. -/
def namedHttp3 : FwdMap :=
  [(⟨"wasi:http/types@0.3.2", "[constructor]fields"⟩, ⟨"wasi:http/types", "[constructor]fields"⟩),
    (⟨"wasi:http/types@0.3.2", "[method]fields.get"⟩, ⟨"wasi:http/types", "[method]fields.get"⟩),
    (⟨"wasi:http/types@0.3.2", "[method]fields.has"⟩, ⟨"wasi:http/types", "[method]fields.has"⟩),
    (⟨"wasi:http/types@0.3.2", "[method]fields.clone"⟩, ⟨"wasi:http/types", "[method]fields.clone"⟩),
    (⟨"wasi:http/types@0.3.2", "[constructor]request-options"⟩, ⟨"wasi:http/types", "[constructor]request-options"⟩)]

/-- 0.2.x `fields` and `request-options` over 0.3.2. -/
def namedHttp2 : FwdMap :=
  [(⟨"wasi:http/types", "[constructor]fields"⟩, ⟨"wasi:http/types@0.3.2", "[constructor]fields"⟩),
    (⟨"wasi:http/types", "[method]fields.get"⟩, ⟨"wasi:http/types@0.3.2", "[method]fields.get"⟩),
    (⟨"wasi:http/types", "[method]fields.has"⟩, ⟨"wasi:http/types@0.3.2", "[method]fields.has"⟩),
    (⟨"wasi:http/types", "[method]fields.clone"⟩, ⟨"wasi:http/types@0.3.2", "[method]fields.clone"⟩),
    (⟨"wasi:http/types", "[constructor]request-options"⟩, ⟨"wasi:http/types@0.3.2", "[constructor]request-options"⟩)]

theorem fwdOkN_clocks3 : FwdOkN clocks2P clocks3P namedClocks3 = true := by decide +kernel
theorem fwdOkN_clocks2 : FwdOkN clocks3P clocks2P namedClocks2 = true := by decide +kernel
theorem fwdOkN_clocks3_29 : FwdOkN clocks29P clocks3P namedClocks3 = true := by decide +kernel
theorem fwdOkN_clocks29 : FwdOkN clocks3P clocks29P namedClocks2 = true := by decide +kernel
theorem fwdOkN_http3 : FwdOkN http2P http3P namedHttp3 = true := by decide +kernel
theorem fwdOkN_http2 : FwdOkN http3P http2P namedHttp2 = true := by decide +kernel
theorem fwdOkN_http3_29 : FwdOkN http29P http3P namedHttp3 = true := by decide +kernel
theorem fwdOkN_http29 : FwdOkN http3P http29P namedHttp2 = true := by decide +kernel

/-- **0.3.2 over 0.2.12 across named types** (`monotonic-clock.now`, `fields`): over every host
of the 0.2.12 typing, the forwarder is a model of the 0.3.2 typing. -/
theorem fwdN_clocks3_model {Y : Silmaril.Games.Sig.{0}} {η : Host Y (fwdI namedClocks3)}
    (hη : (hostSat (witRTh clocks2P).Accepts).holds η) :
    (hostSat (witRTh clocks3P).Accepts).holds (link η (Versions.ofSBody (fwdBody namedClocks3) ())) :=
  fwdN_model fwdOkN_clocks3 hη

theorem fwdN_http3_model {Y : Silmaril.Games.Sig.{0}} {η : Host Y (fwdI namedHttp3)}
    (hη : (hostSat (witRTh http2P).Accepts).holds η) :
    (hostSat (witRTh http3P).Accepts).holds (link η (Versions.ofSBody (fwdBody namedHttp3) ())) :=
  fwdN_model fwdOkN_http3 hη

end Silmaril.Wasi.Versions.WitImport
