//! A PIN door lock, written once against two institutions:
//!
//! * `spec` (the specification vocabulary): `attest()` says "the door opened", and
//!   `assert(cond)` says "`cond` holds here";
//! * `door` (the hardware): `unlock()`, `lock()`, `alarm()`.
//!
//! The machine has three states, `Locked`, `Open` and `Alarm`. `enter(pin)` in `Locked` opens the
//! door on the right PIN and counts wrong PINs; the third wrong PIN sounds the alarm, after which
//! nothing opens the door. `lock()` closes an open door. `status()` reads the state.
//!
//! At the unlock transition the program states its own safety property by calling
//! `spec.assert(pin == PIN)`, then `spec.attest()`, then `door.unlock()`. The questions about the
//! compiled module are questions about these import calls (see the README).
//!
//! `BUGGY = true` compiles the same machine with the PIN comparison inverted.
#![cfg_attr(target_family = "wasm", no_std)]

institution::institution! {
    /// The specification institution.
    pub mod spec = "spec" {
        /// The door opened (a "may attest" witness).
        fn attest();
        /// An assertion: a call with `0` is a violation.
        fn assert(cond: i32);
    }
}

institution::institution! {
    /// The door hardware.
    pub mod door = "door" {
        /// Release the bolt.
        fn unlock();
        /// Engage the bolt.
        fn lock();
        /// Sound the alarm.
        fn alarm();
    }
}

/// The PIN.
pub const PIN: i32 = 1234;
/// Wrong PINs before the alarm.
pub const MAX_WRONG: u32 = 3;

/// The machine's states.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(i32)]
pub enum State {
    Locked = 0,
    Open = 1,
    Alarm = 2,
}

/// The machine: its state and the number of wrong PINs so far.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Lock {
    pub state: State,
    pub wrong: u32,
}

impl Default for Lock {
    fn default() -> Self {
        Self::new()
    }
}

impl Lock {
    /// The initial state: locked, no wrong PINs.
    pub const fn new() -> Self {
        Lock {
            state: State::Locked,
            wrong: 0,
        }
    }

    /// Enter a PIN.
    pub fn enter<const BUGGY: bool, S: spec::Api, D: door::Api>(
        &mut self,
        s: &mut S,
        d: &mut D,
        pin: i32,
    ) {
        if self.state != State::Locked {
            return;
        }
        let accept = if BUGGY { pin != PIN } else { pin == PIN };
        if accept {
            s.assert((pin == PIN) as i32);
            s.attest();
            self.state = State::Open;
            self.wrong = 0;
            d.unlock();
        } else {
            self.wrong += 1;
            if self.wrong >= MAX_WRONG {
                self.state = State::Alarm;
                d.alarm();
            }
        }
    }

    /// Close an open door.
    pub fn lock<D: door::Api>(&mut self, d: &mut D) {
        if self.state == State::Open {
            self.state = State::Locked;
            d.lock();
        }
    }

    /// The state, as an `i32`.
    pub fn status(&self) -> i32 {
        self.state as i32
    }
}

/// A global `Lock` for a single-threaded Wasm instance. `with` copies the state out and back,
/// so a re-entrant export call from inside an import sees the old state (no aliasing).
pub struct Global(core::cell::UnsafeCell<Lock>);

// SAFETY: Wasm instances without threads are single-threaded; `with` never holds a reference
// into the cell across a call.
unsafe impl Sync for Global {}

impl Global {
    pub const fn new() -> Self {
        Global(core::cell::UnsafeCell::new(Lock::new()))
    }

    pub fn with<R>(&self, f: impl FnOnce(&mut Lock) -> R) -> R {
        let p = self.0.get();
        // SAFETY: plain reads and writes through the raw pointer; see the `Sync` impl.
        let mut l = unsafe { p.read() };
        let r = f(&mut l);
        unsafe { p.write(l) };
        r
    }
}

impl Default for Global {
    fn default() -> Self {
        Self::new()
    }
}

/// Define the Wasm exports `enter`, `lock` and `status` and the panic handler.
#[macro_export]
macro_rules! door_exports {
    ($buggy:expr) => {
        static LOCK: $crate::Global = $crate::Global::new();

        #[unsafe(no_mangle)]
        pub extern "C" fn enter(pin: i32) {
            LOCK.with(|l| {
                l.enter::<{ $buggy }, _, _>(&mut $crate::spec::Wasm, &mut $crate::door::Wasm, pin)
            })
        }

        #[unsafe(no_mangle)]
        pub extern "C" fn lock() {
            LOCK.with(|l| l.lock(&mut $crate::door::Wasm))
        }

        #[unsafe(no_mangle)]
        pub extern "C" fn status() -> i32 {
            LOCK.with(|l| l.status())
        }

        #[panic_handler]
        fn panic(_: &core::panic::PanicInfo) -> ! {
            core::arch::wasm32::unreachable()
        }
    };
}
