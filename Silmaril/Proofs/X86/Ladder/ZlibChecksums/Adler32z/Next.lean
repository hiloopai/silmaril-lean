module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Inv

/-!
# `adler32_z`: arriving at an offset

`nextAt (cuts c) (stops c) μ cont o s` for each of the 297 instruction offsets `o` of the
listing: the cut invariant and the measure bound at the four loop heads and after the prologue (`0x20`), `Q` at the four
`ret`s, and the continuation elsewhere. Generated (one `rfl` lemma per offset), so that the
segment VC never unfolds `nextAt` at an unevaluated offset (see `SegVC9`).

`adler_vc [lemmas]` is `seg_vc9` with the listing lookups `lkN` and these `nxN`.
-/

@[expose] public section

set_option maxRecDepth 100000

namespace Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z

open Silmaril.X86 (MState)

theorem nx0 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 0 s = cont 0 s := rfl
theorem nx2 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 2 s = cont 2 s := rfl
theorem nx5 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 5 s = cont 5 s := rfl
theorem nx8 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 8 s = cont 8 s := rfl
theorem nx12 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 12 s = cont 12 s := rfl
theorem nx14 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 14 s = cont 14 s := rfl
theorem nx18 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 18 s = cont 18 s := rfl
theorem nx20 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 20 s = cont 20 s := rfl
theorem nx23 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 23 s = cont 23 s := rfl
theorem nx25 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 25 s = cont 25 s := rfl
theorem nx26 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 26 s = cont 26 s := rfl
theorem nx27 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 27 s = cont 27 s := rfl
theorem nx32 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 32 s =
      (InvP c s ∧ Silmaril.X86.SegVC.bound μ (c.n + 1)) := rfl
theorem nx36 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 36 s = cont 36 s := rfl
theorem nx42 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 42 s = cont 42 s := rfl
theorem nx45 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 45 s = cont 45 s := rfl
theorem nx51 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 51 s = cont 51 s := rfl
theorem nx54 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 54 s = cont 54 s := rfl
theorem nx58 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 58 s = cont 58 s := rfl
theorem nx64 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 64 s = cont 64 s := rfl
theorem nx71 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 71 s = cont 71 s := rfl
theorem nx77 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 77 s = cont 77 s := rfl
theorem nx84 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 84 s = cont 84 s := rfl
theorem nx89 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 89 s = cont 89 s := rfl
theorem nx94 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 94 s = cont 94 s := rfl
theorem nx101 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 101 s = cont 101 s := rfl
theorem nx106 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 106 s = cont 106 s := rfl
theorem nx111 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 111 s = cont 111 s := rfl
theorem nx118 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 118 s = cont 118 s := rfl
theorem nx128 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 128 s = (InvA c s ∧ Silmaril.X86.SegVC.bound μ (meas c .r8 s)) := rfl
theorem nx132 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 132 s = cont 132 s := rfl
theorem nx137 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 137 s = cont 137 s := rfl
theorem nx141 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 141 s = cont 141 s := rfl
theorem nx146 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 146 s = cont 146 s := rfl
theorem nx151 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 151 s = cont 151 s := rfl
theorem nx154 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 154 s = cont 154 s := rfl
theorem nx159 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 159 s = cont 159 s := rfl
theorem nx164 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 164 s = cont 164 s := rfl
theorem nx167 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 167 s = cont 167 s := rfl
theorem nx172 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 172 s = cont 172 s := rfl
theorem nx177 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 177 s = cont 177 s := rfl
theorem nx180 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 180 s = cont 180 s := rfl
theorem nx183 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 183 s = cont 183 s := rfl
theorem nx188 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 188 s = cont 188 s := rfl
theorem nx193 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 193 s = cont 193 s := rfl
theorem nx196 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 196 s = cont 196 s := rfl
theorem nx199 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 199 s = cont 199 s := rfl
theorem nx204 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 204 s = cont 204 s := rfl
theorem nx209 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 209 s = cont 209 s := rfl
theorem nx212 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 212 s = cont 212 s := rfl
theorem nx215 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 215 s = cont 215 s := rfl
theorem nx218 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 218 s = cont 218 s := rfl
theorem nx221 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 221 s = cont 221 s := rfl
theorem nx224 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 224 s = cont 224 s := rfl
theorem nx227 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 227 s = cont 227 s := rfl
theorem nx231 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 231 s = cont 231 s := rfl
theorem nx236 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 236 s = cont 236 s := rfl
theorem nx239 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 239 s = cont 239 s := rfl
theorem nx244 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 244 s = cont 244 s := rfl
theorem nx249 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 249 s = cont 249 s := rfl
theorem nx253 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 253 s = cont 253 s := rfl
theorem nx258 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 258 s = cont 258 s := rfl
theorem nx263 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 263 s = cont 263 s := rfl
theorem nx268 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 268 s = cont 268 s := rfl
theorem nx271 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 271 s = cont 271 s := rfl
theorem nx276 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 276 s = cont 276 s := rfl
theorem nx279 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 279 s = cont 279 s := rfl
theorem nx282 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 282 s = cont 282 s := rfl
theorem nx287 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 287 s = cont 287 s := rfl
theorem nx290 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 290 s = cont 290 s := rfl
theorem nx293 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 293 s = cont 293 s := rfl
theorem nx296 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 296 s = cont 296 s := rfl
theorem nx299 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 299 s = cont 299 s := rfl
theorem nx302 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 302 s = cont 302 s := rfl
theorem nx305 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 305 s = cont 305 s := rfl
theorem nx308 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 308 s = cont 308 s := rfl
theorem nx311 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 311 s = cont 311 s := rfl
theorem nx314 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 314 s = cont 314 s := rfl
theorem nx317 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 317 s = cont 317 s := rfl
theorem nx320 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 320 s = cont 320 s := rfl
theorem nx323 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 323 s = cont 323 s := rfl
theorem nx326 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 326 s = cont 326 s := rfl
theorem nx331 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 331 s = cont 331 s := rfl
theorem nx336 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 336 s = cont 336 s := rfl
theorem nx339 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 339 s = cont 339 s := rfl
theorem nx342 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 342 s = cont 342 s := rfl
theorem nx348 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 348 s = cont 348 s := rfl
theorem nx358 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 358 s = cont 358 s := rfl
theorem nx363 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 363 s = cont 363 s := rfl
theorem nx368 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 368 s = cont 368 s := rfl
theorem nx371 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 371 s = cont 371 s := rfl
theorem nx374 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 374 s = cont 374 s := rfl
theorem nx377 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 377 s = cont 377 s := rfl
theorem nx380 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 380 s = cont 380 s := rfl
theorem nx383 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 383 s = cont 383 s := rfl
theorem nx387 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 387 s = cont 387 s := rfl
theorem nx394 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 394 s = cont 394 s := rfl
theorem nx397 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 397 s = cont 397 s := rfl
theorem nx407 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 407 s = cont 407 s := rfl
theorem nx410 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 410 s = cont 410 s := rfl
theorem nx413 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 413 s = cont 413 s := rfl
theorem nx416 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 416 s = cont 416 s := rfl
theorem nx419 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 419 s = cont 419 s := rfl
theorem nx422 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 422 s = cont 422 s := rfl
theorem nx426 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 426 s = cont 426 s := rfl
theorem nx433 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 433 s = cont 433 s := rfl
theorem nx436 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 436 s = cont 436 s := rfl
theorem nx443 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 443 s = cont 443 s := rfl
theorem nx448 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 448 s = cont 448 s := rfl
theorem nx453 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 453 s = cont 453 s := rfl
theorem nx460 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 460 s = cont 460 s := rfl
theorem nx466 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 466 s = cont 466 s := rfl
theorem nx471 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 471 s = cont 471 s := rfl
theorem nx474 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 474 s = cont 474 s := rfl
theorem nx480 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 480 s = cont 480 s := rfl
theorem nx485 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 485 s = cont 485 s := rfl
theorem nx486 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 486 s = cont 486 s := rfl
theorem nx487 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 487 s = cont 487 s := rfl
theorem nx489 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 489 s = cont 489 s := rfl
theorem nx493 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 493 s = cont 493 s := rfl
theorem nx495 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 495 s = cont 495 s := rfl
theorem nx497 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 497 s = cont 497 s := rfl
theorem nx500 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 500 s = cont 500 s := rfl
theorem nx502 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 502 s = Q c s := rfl
theorem nx503 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 503 s = cont 503 s := rfl
theorem nx506 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 506 s = cont 506 s := rfl
theorem nx508 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 508 s = cont 508 s := rfl
theorem nx513 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 513 s = cont 513 s := rfl
theorem nx517 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 517 s = (InvB c s ∧ Silmaril.X86.SegVC.bound μ (meas c .rcx s)) := rfl
theorem nx520 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 520 s = cont 520 s := rfl
theorem nx524 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 524 s = cont 524 s := rfl
theorem nx527 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 527 s = cont 527 s := rfl
theorem nx530 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 530 s = cont 530 s := rfl
theorem nx533 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 533 s = cont 533 s := rfl
theorem nx535 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 535 s = cont 535 s := rfl
theorem nx540 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 540 s = cont 540 s := rfl
theorem nx547 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 547 s = cont 547 s := rfl
theorem nx549 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 549 s = cont 549 s := rfl
theorem nx556 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 556 s = cont 556 s := rfl
theorem nx561 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 561 s = cont 561 s := rfl
theorem nx566 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 566 s = cont 566 s := rfl
theorem nx576 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 576 s = cont 576 s := rfl
theorem nx577 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 577 s = cont 577 s := rfl
theorem nx578 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 578 s = cont 578 s := rfl
theorem nx581 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 581 s = cont 581 s := rfl
theorem nx584 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 584 s = cont 584 s := rfl
theorem nx586 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 586 s = cont 586 s := rfl
theorem nx588 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 588 s = cont 588 s := rfl
theorem nx590 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 590 s = cont 590 s := rfl
theorem nx593 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 593 s = cont 593 s := rfl
theorem nx596 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 596 s = cont 596 s := rfl
theorem nx599 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 599 s = cont 599 s := rfl
theorem nx602 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 602 s = cont 602 s := rfl
theorem nx606 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 606 s = cont 606 s := rfl
theorem nx613 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 613 s = cont 613 s := rfl
theorem nx616 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 616 s = cont 616 s := rfl
theorem nx619 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 619 s = cont 619 s := rfl
theorem nx623 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 623 s = cont 623 s := rfl
theorem nx626 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 626 s = cont 626 s := rfl
theorem nx628 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 628 s = Q c s := rfl
theorem nx629 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 629 s = cont 629 s := rfl
theorem nx632 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 632 s = cont 632 s := rfl
theorem nx635 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 635 s = cont 635 s := rfl
theorem nx642 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 642 s = cont 642 s := rfl
theorem nx644 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 644 s = cont 644 s := rfl
theorem nx651 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 651 s = cont 651 s := rfl
theorem nx656 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 656 s = cont 656 s := rfl
theorem nx659 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 659 s = cont 659 s := rfl
theorem nx665 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 665 s = cont 665 s := rfl
theorem nx667 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 667 s = cont 667 s := rfl
theorem nx673 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 673 s = cont 673 s := rfl
theorem nx677 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 677 s = cont 677 s := rfl
theorem nx678 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 678 s = cont 678 s := rfl
theorem nx679 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 679 s = cont 679 s := rfl
theorem nx682 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 682 s = cont 682 s := rfl
theorem nx684 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 684 s = cont 684 s := rfl
theorem nx686 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 686 s = cont 686 s := rfl
theorem nx688 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 688 s = cont 688 s := rfl
theorem nx690 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 690 s = Q c s := rfl
theorem nx691 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 691 s = cont 691 s := rfl
theorem nx695 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 695 s = cont 695 s := rfl
theorem nx701 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 701 s = cont 701 s := rfl
theorem nx705 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 705 s = cont 705 s := rfl
theorem nx710 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 710 s = cont 710 s := rfl
theorem nx714 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 714 s = cont 714 s := rfl
theorem nx717 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 717 s = cont 717 s := rfl
theorem nx721 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 721 s = cont 721 s := rfl
theorem nx725 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 725 s = cont 725 s := rfl
theorem nx730 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 730 s = cont 730 s := rfl
theorem nx734 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 734 s = cont 734 s := rfl
theorem nx739 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 739 s = (InvC c s ∧ Silmaril.X86.SegVC.bound μ (meas c .rcx s)) := rfl
theorem nx742 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 742 s = cont 742 s := rfl
theorem nx747 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 747 s = cont 747 s := rfl
theorem nx752 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 752 s = cont 752 s := rfl
theorem nx757 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 757 s = cont 757 s := rfl
theorem nx760 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 760 s = cont 760 s := rfl
theorem nx764 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 764 s = cont 764 s := rfl
theorem nx768 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 768 s = cont 768 s := rfl
theorem nx771 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 771 s = cont 771 s := rfl
theorem nx776 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 776 s = cont 776 s := rfl
theorem nx781 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 781 s = cont 781 s := rfl
theorem nx784 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 784 s = cont 784 s := rfl
theorem nx787 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 787 s = cont 787 s := rfl
theorem nx792 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 792 s = cont 792 s := rfl
theorem nx797 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 797 s = cont 797 s := rfl
theorem nx800 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 800 s = cont 800 s := rfl
theorem nx803 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 803 s = cont 803 s := rfl
theorem nx807 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 807 s = cont 807 s := rfl
theorem nx811 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 811 s = cont 811 s := rfl
theorem nx814 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 814 s = cont 814 s := rfl
theorem nx817 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 817 s = cont 817 s := rfl
theorem nx822 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 822 s = cont 822 s := rfl
theorem nx825 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 825 s = cont 825 s := rfl
theorem nx828 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 828 s = cont 828 s := rfl
theorem nx831 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 831 s = cont 831 s := rfl
theorem nx834 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 834 s = cont 834 s := rfl
theorem nx837 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 837 s = cont 837 s := rfl
theorem nx840 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 840 s = cont 840 s := rfl
theorem nx843 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 843 s = cont 843 s := rfl
theorem nx846 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 846 s = cont 846 s := rfl
theorem nx849 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 849 s = cont 849 s := rfl
theorem nx852 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 852 s = cont 852 s := rfl
theorem nx855 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 855 s = cont 855 s := rfl
theorem nx858 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 858 s = cont 858 s := rfl
theorem nx861 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 861 s = cont 861 s := rfl
theorem nx865 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 865 s = cont 865 s := rfl
theorem nx870 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 870 s = cont 870 s := rfl
theorem nx875 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 875 s = cont 875 s := rfl
theorem nx878 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 878 s = cont 878 s := rfl
theorem nx882 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 882 s = cont 882 s := rfl
theorem nx885 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 885 s = cont 885 s := rfl
theorem nx890 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 890 s = cont 890 s := rfl
theorem nx895 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 895 s = cont 895 s := rfl
theorem nx898 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 898 s = cont 898 s := rfl
theorem nx902 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 902 s = cont 902 s := rfl
theorem nx905 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 905 s = cont 905 s := rfl
theorem nx908 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 908 s = cont 908 s := rfl
theorem nx911 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 911 s = cont 911 s := rfl
theorem nx914 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 914 s = cont 914 s := rfl
theorem nx917 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 917 s = cont 917 s := rfl
theorem nx920 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 920 s = cont 920 s := rfl
theorem nx923 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 923 s = cont 923 s := rfl
theorem nx926 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 926 s = cont 926 s := rfl
theorem nx931 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 931 s = cont 931 s := rfl
theorem nx936 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 936 s = cont 936 s := rfl
theorem nx940 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 940 s = cont 940 s := rfl
theorem nx943 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 943 s = cont 943 s := rfl
theorem nx949 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 949 s = cont 949 s := rfl
theorem nx954 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 954 s = cont 954 s := rfl
theorem nx957 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 957 s = cont 957 s := rfl
theorem nx962 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 962 s = cont 962 s := rfl
theorem nx965 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 965 s = cont 965 s := rfl
theorem nx968 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 968 s = cont 968 s := rfl
theorem nx972 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 972 s = cont 972 s := rfl
theorem nx977 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 977 s = cont 977 s := rfl
theorem nx980 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 980 s = cont 980 s := rfl
theorem nx982 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 982 s = cont 982 s := rfl
theorem nx987 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 987 s = cont 987 s := rfl
theorem nx992 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 992 s = (InvD c s ∧ Silmaril.X86.SegVC.bound μ (meas c .r8 s)) := rfl
theorem nx996 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 996 s = cont 996 s := rfl
theorem nx1000 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1000 s = cont 1000 s := rfl
theorem nx1003 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1003 s = cont 1003 s := rfl
theorem nx1006 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1006 s = cont 1006 s := rfl
theorem nx1009 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1009 s = cont 1009 s := rfl
theorem nx1011 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1011 s = cont 1011 s := rfl
theorem nx1016 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1016 s = cont 1016 s := rfl
theorem nx1026 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1026 s = cont 1026 s := rfl
theorem nx1029 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1029 s = cont 1029 s := rfl
theorem nx1032 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1032 s = cont 1032 s := rfl
theorem nx1035 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1035 s = cont 1035 s := rfl
theorem nx1038 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1038 s = cont 1038 s := rfl
theorem nx1041 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1041 s = cont 1041 s := rfl
theorem nx1044 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1044 s = cont 1044 s := rfl
theorem nx1048 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1048 s = cont 1048 s := rfl
theorem nx1055 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1055 s = cont 1055 s := rfl
theorem nx1058 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1058 s = cont 1058 s := rfl
theorem nx1063 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1063 s = cont 1063 s := rfl
theorem nx1066 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1066 s = cont 1066 s := rfl
theorem nx1071 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1071 s = cont 1071 s := rfl
theorem nx1074 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1074 s = cont 1074 s := rfl
theorem nx1077 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1077 s = cont 1077 s := rfl
theorem nx1080 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1080 s = cont 1080 s := rfl
theorem nx1083 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1083 s = cont 1083 s := rfl
theorem nx1087 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1087 s = cont 1087 s := rfl
theorem nx1094 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1094 s = cont 1094 s := rfl
theorem nx1097 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1097 s = cont 1097 s := rfl
theorem nx1102 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1102 s = cont 1102 s := rfl
theorem nx1107 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1107 s = cont 1107 s := rfl
theorem nx1108 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1108 s = cont 1108 s := rfl
theorem nx1113 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1113 s = cont 1113 s := rfl
theorem nx1114 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1114 s = cont 1114 s := rfl
theorem nx1116 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1116 s = cont 1116 s := rfl
theorem nx1118 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1118 s = cont 1118 s := rfl
theorem nx1120 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1120 s = cont 1120 s := rfl
theorem nx1122 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1122 s = Q c s := rfl
theorem nx1123 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1123 s = cont 1123 s := rfl
theorem nx1130 (c : Ctx) (μ : Option Nat) (cont : Nat → MState → Prop) (s : MState) :
    Silmaril.X86.SegVC.nextAt (cuts c) (stops c) μ cont 1130 s = cont 1130 s := rfl

/-- `adler_vc [lemmas]`: `seg_vc9` over `adlerListing` with the cut points and stops of
`cuts c`/`stops c`. -/
syntax "adler_vc " " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| adler_vc [$ls,*]) => `(tactic|
      adler_vc0 [Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx0, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx2, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx5, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx8, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx12, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx14, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx18, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx20, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx23, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx25, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx26, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx27, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx32, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx36, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx42, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx45, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx51, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx54, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx58, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx64, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx71, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx77, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx84, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx89, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx94, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx101, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx106, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx111, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx118, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx128, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx132, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx137, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx141, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx146, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx151, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx154, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx159, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx164, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx167, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx172, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx177, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx180, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx183, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx188, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx193, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx196, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx199, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx204, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx209, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx212, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx215, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx218, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx221, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx224, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx227, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx231, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx236, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx239, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx244, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx249, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx253, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx258, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx263, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx268, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx271, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx276, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx279, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx282, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx287, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx290, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx293, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx296, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx299, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx302, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx305, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx308, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx311, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx314, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx317, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx320, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx323, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx326, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx331, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx336, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx339, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx342, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx348, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx358, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx363, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx368, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx371, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx374, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx377, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx380, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx383, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx387, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx394, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx397, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx407, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx410, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx413, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx416, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx419, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx422, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx426, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx433, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx436, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx443, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx448, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx453, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx460, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx466, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx471, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx474, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx480, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx485, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx486, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx487, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx489, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx493, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx495, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx497, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx500, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx502, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx503, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx506, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx508, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx513, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx517, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx520, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx524, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx527, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx530, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx533, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx535, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx540, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx547, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx549, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx556, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx561, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx566, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx576, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx577, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx578, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx581, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx584, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx586, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx588, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx590, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx593, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx596, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx599, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx602, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx606, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx613, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx616, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx619, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx623, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx626, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx628, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx629, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx632, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx635, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx642, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx644, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx651, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx656, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx659, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx665, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx667, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx673, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx677, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx678, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx679, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx682, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx684, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx686, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx688, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx690, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx691, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx695, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx701, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx705, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx710, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx714, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx717, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx721, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx725, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx730, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx734, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx739, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx742, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx747, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx752, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx757, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx760, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx764, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx768, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx771, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx776, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx781, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx784, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx787, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx792, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx797, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx800, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx803, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx807, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx811, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx814, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx817, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx822, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx825, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx828, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx831, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx834, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx837, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx840, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx843, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx846, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx849, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx852, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx855, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx858, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx861, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx865, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx870, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx875, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx878, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx882, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx885, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx890, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx895, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx898, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx902, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx905, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx908, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx911, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx914, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx917, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx920, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx923, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx926, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx931, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx936, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx940, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx943, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx949, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx954, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx957, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx962, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx965, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx968, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx972, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx977, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx980, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx982, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx987, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx992, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx996, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1000, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1003, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1006, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1009, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1011, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1016, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1026, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1029, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1032, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1035, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1038, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1041, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1044, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1048, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1055, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1058, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1063, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1066, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1071, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1074, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1077, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1080, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1083, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1087, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1094, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1097, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1102, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1107, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1108, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1113, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1114, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1116, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1118, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1120, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1122, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1123, Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.nx1130, $ls,*])

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z
