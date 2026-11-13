//! Import a specification institution's API into Rust.
//!
//! An institution's *signature* is a set of typed Wasm imports (for example the `spec`
//! module's `attest : [] -> []` and `assert : [i32] -> []`). The [`institution!`] macro turns
//! such a signature into Rust items, Curry–Howard style:
//!
//! * the signature becomes a trait `Api` (one method per import), so a Rust program generic over
//!   `A: Api` is a program *over* the institution's vocabulary;
//! * on `wasm32` the zero-sized `Wasm` implements `Api` by calling the real Wasm imports
//!   (`#[link(wasm_import_module = ...)]`), and the module-level functions call them directly;
//! * everywhere, `Observer<F>` implements `Api` by handing each call to a closure as an `Event`,
//!   so the same program can be run natively and its import trace inspected by unit tests and
//!   property tests.
//!
//! A *sentence* about the program is a question about its import calls ("`attest` is never
//! called while export `status` is active", "`assert` never receives `0`"). Those are answered on
//! the compiled `.wasm` by Silmaril's verified checker `wasm-verify`; see the README.
//!
//! ```ignore
//! institution::institution! {
//!     /// Specification imports.
//!     pub mod spec = "spec" {
//!         fn attest();
//!         fn assert(cond: i32);
//!     }
//! }
//! ```
#![no_std]

/// Declare an institution's imports. See the crate documentation.
///
/// Syntax: `vis mod NAME = "wasm-module" { fn f(arg: Ty, ...); ... }`. Every function returns
/// `()`; argument types must be Wasm scalars (`i32`, `u32`, `i64`, `u64`, `f32`, `f64`).
#[macro_export]
macro_rules! institution {
    (
        $(#[$meta:meta])*
        $vis:vis mod $name:ident = $module:literal {
            $(
                $(#[$fmeta:meta])*
                fn $f:ident ( $( $a:ident : $t:ty ),* $(,)? );
            )*
        }
    ) => {
        $(#[$meta])*
        #[allow(dead_code)]
        $vis mod $name {
            /// The Wasm import module name of this institution.
            pub const MODULE: &str = $module;

            /// The names of the imports, in declaration order.
            pub const IMPORTS: &[&str] = &[$(stringify!($f)),*];

            /// One import call, as observed natively.
            #[allow(non_camel_case_types)]
            #[derive(Clone, Copy, Debug, PartialEq)]
            pub enum Event {
                $( $(#[$fmeta])* $f ( $($t),* ), )*
            }

            /// The institution's signature as a trait: one method per import.
            pub trait Api {
                $( $(#[$fmeta])* fn $f(&mut self $(, $a: $t)*); )*
            }

            /// The real imports (only on Wasm targets).
            #[derive(Clone, Copy, Debug, Default)]
            pub struct Wasm;

            #[cfg(target_family = "wasm")]
            mod ffi {
                #[link(wasm_import_module = $module)]
                unsafe extern "C" {
                    $( pub safe fn $f($($a: $t),*); )*
                }
            }

            #[cfg(target_family = "wasm")]
            impl Api for Wasm {
                $( #[inline(always)] fn $f(&mut self $(, $a: $t)*) { ffi::$f($($a),*) } )*
            }

            $(
                $(#[$fmeta])*
                #[cfg(target_family = "wasm")]
                #[inline(always)]
                pub fn $f($($a: $t),*) { ffi::$f($($a),*) }
            )*

            /// A native implementation that reports every call to a closure.
            pub struct Observer<F>(pub F);

            impl<F: FnMut(Event)> Api for Observer<F> {
                $( fn $f(&mut self $(, $a: $t)*) { (self.0)(Event::$f($($a),*)) } )*
            }
        }
    };
}
