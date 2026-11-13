module

public import Silmaril.Wasi.Versions.WitImport.Fwd.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables3.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables29.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables29.Defs

@[expose] public section

/-!
# Forwarding pairs, computed once: cli, clocks, rand

Each `fwdPairs P Q` of `Silmaril.Wasi.Versions.WitImport.Fwd.Thms` is stated here as a literal
list, checked by the kernel (`decide +kernel`), and `FwdOk` is checked on that literal. The
pairs are split over several modules so each stays under the module time budget; `Fwd.Thms`
assembles `fwdOk_all` and the name lists from these equations by rewriting. The literals were
printed by evaluating `fwdPairs` (not trusted: the kernel checks each equation).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-- Forwarding pairs, 0.3.2 `rand` over 0.2.12. -/
theorem fwdPairs_rand3 : fwdPairs rand2P rand3P =
    [(⟨"wasi:random/insecure@0.3.2", "get-insecure-random-bytes"⟩,
       ⟨"wasi:random/insecure", "get-insecure-random-bytes"⟩),
      (⟨"wasi:random/insecure@0.3.2", "get-insecure-random-u64"⟩,
       ⟨"wasi:random/insecure", "get-insecure-random-u64"⟩),
      (⟨"wasi:random/random@0.3.2", "get-random-bytes"⟩,
       ⟨"wasi:random/random", "get-random-bytes"⟩),
      (⟨"wasi:random/random@0.3.2", "get-random-u64"⟩,
       ⟨"wasi:random/random", "get-random-u64"⟩)] := by
  decide +kernel

/-- The pairs of 0.3.2 `rand` over 0.2.12 are forwardable. -/
theorem fwdOk_rand3 : FwdOk rand2P rand3P (fwdPairs rand2P rand3P) = true := by
  rw [fwdPairs_rand3]
  decide +kernel

/-- Forwarding pairs, 0.2.12 `rand` over 0.3.2. -/
theorem fwdPairs_rand2 : fwdPairs rand3P rand2P =
    [(⟨"wasi:random/insecure", "get-insecure-random-bytes"⟩,
       ⟨"wasi:random/insecure@0.3.2", "get-insecure-random-bytes"⟩),
      (⟨"wasi:random/insecure", "get-insecure-random-u64"⟩,
       ⟨"wasi:random/insecure@0.3.2", "get-insecure-random-u64"⟩),
      (⟨"wasi:random/random", "get-random-bytes"⟩,
       ⟨"wasi:random/random@0.3.2", "get-random-bytes"⟩),
      (⟨"wasi:random/random", "get-random-u64"⟩,
       ⟨"wasi:random/random@0.3.2", "get-random-u64"⟩)] := by
  decide +kernel

/-- The pairs of 0.2.12 `rand` over 0.3.2 are forwardable. -/
theorem fwdOk_rand2 : FwdOk rand3P rand2P (fwdPairs rand3P rand2P) = true := by
  rw [fwdPairs_rand2]
  decide +kernel

/-- Forwarding pairs, 0.3.2 `clocks` over 0.2.12. -/
theorem fwdPairs_clocks3 : fwdPairs clocks2P clocks3P =
    [] := by
  decide +kernel

/-- The pairs of 0.3.2 `clocks` over 0.2.12 are forwardable. -/
theorem fwdOk_clocks3 : FwdOk clocks2P clocks3P (fwdPairs clocks2P clocks3P) = true := by
  rw [fwdPairs_clocks3]
  decide +kernel

/-- Forwarding pairs, 0.2.12 `clocks` over 0.3.2. -/
theorem fwdPairs_clocks2 : fwdPairs clocks3P clocks2P =
    [] := by
  decide +kernel

/-- The pairs of 0.2.12 `clocks` over 0.3.2 are forwardable. -/
theorem fwdOk_clocks2 : FwdOk clocks3P clocks2P (fwdPairs clocks3P clocks2P) = true := by
  rw [fwdPairs_clocks2]
  decide +kernel

/-- Forwarding pairs, 0.3.2 `cli` over 0.2.12. -/
theorem fwdPairs_cli3 : fwdPairs cli2P cli3P =
    [(⟨"wasi:cli/environment@0.3.2", "get-environment"⟩,
       ⟨"wasi:cli/environment", "get-environment"⟩),
      (⟨"wasi:cli/environment@0.3.2", "get-arguments"⟩,
       ⟨"wasi:cli/environment", "get-arguments"⟩),
      (⟨"wasi:cli/exit@0.3.2", "exit"⟩,
       ⟨"wasi:cli/exit", "exit"⟩),
      (⟨"wasi:cli/exit@0.3.2", "exit-with-code"⟩,
       ⟨"wasi:cli/exit", "exit-with-code"⟩),
      (⟨"wasi:cli/terminal-stdin@0.3.2", "get-terminal-stdin"⟩,
       ⟨"wasi:cli/terminal-stdin", "get-terminal-stdin"⟩),
      (⟨"wasi:cli/terminal-stdout@0.3.2", "get-terminal-stdout"⟩,
       ⟨"wasi:cli/terminal-stdout", "get-terminal-stdout"⟩),
      (⟨"wasi:cli/terminal-stderr@0.3.2", "get-terminal-stderr"⟩,
       ⟨"wasi:cli/terminal-stderr", "get-terminal-stderr"⟩)] := by
  decide +kernel

/-- The pairs of 0.3.2 `cli` over 0.2.12 are forwardable. -/
theorem fwdOk_cli3 : FwdOk cli2P cli3P (fwdPairs cli2P cli3P) = true := by
  rw [fwdPairs_cli3]
  decide +kernel

/-- Forwarding pairs, 0.2.12 `cli` over 0.3.2. -/
theorem fwdPairs_cli2 : fwdPairs cli3P cli2P =
    [(⟨"wasi:cli/environment", "get-environment"⟩,
       ⟨"wasi:cli/environment@0.3.2", "get-environment"⟩),
      (⟨"wasi:cli/environment", "get-arguments"⟩,
       ⟨"wasi:cli/environment@0.3.2", "get-arguments"⟩),
      (⟨"wasi:cli/exit", "exit"⟩,
       ⟨"wasi:cli/exit@0.3.2", "exit"⟩),
      (⟨"wasi:cli/exit", "exit-with-code"⟩,
       ⟨"wasi:cli/exit@0.3.2", "exit-with-code"⟩),
      (⟨"wasi:cli/terminal-stdin", "get-terminal-stdin"⟩,
       ⟨"wasi:cli/terminal-stdin@0.3.2", "get-terminal-stdin"⟩),
      (⟨"wasi:cli/terminal-stdout", "get-terminal-stdout"⟩,
       ⟨"wasi:cli/terminal-stdout@0.3.2", "get-terminal-stdout"⟩),
      (⟨"wasi:cli/terminal-stderr", "get-terminal-stderr"⟩,
       ⟨"wasi:cli/terminal-stderr@0.3.2", "get-terminal-stderr"⟩)] := by
  decide +kernel

/-- The pairs of 0.2.12 `cli` over 0.3.2 are forwardable. -/
theorem fwdOk_cli2 : FwdOk cli3P cli2P (fwdPairs cli3P cli2P) = true := by
  rw [fwdPairs_cli2]
  decide +kernel

end Silmaril.Wasi.Versions.WitImport
