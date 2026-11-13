//! Native property tests of the door lock: random sequences of export calls, run on the same
//! Rust source with both institutions observed (`Observer`), and temporal questions asked of
//! the resulting import trace.

use door_lock::{Lock, PIN, State, door, spec};
use proptest::prelude::*;
use proptest::test_runner::{Config, TestCaseError, TestRunner};

/// One import call of either institution.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Ev {
    Spec(spec::Event),
    Door(door::Event),
}

/// One export call.
#[derive(Clone, Copy, Debug)]
enum Call {
    Enter(i32),
    Lock,
    Status,
}

fn call() -> impl Strategy<Value = Call> {
    prop_oneof![
        // Mostly the right PIN or a near miss, so every state is visited.
        prop_oneof![Just(PIN), Just(0), Just(PIN + 1), any::<i32>()].prop_map(Call::Enter),
        Just(Call::Lock),
        Just(Call::Status),
    ]
}

/// Run a sequence of export calls from the initial state; the import trace and final state.
fn run<const BUGGY: bool>(calls: &[Call]) -> (Vec<Ev>, Lock) {
    let log = std::cell::RefCell::new(Vec::new());
    let mut s = spec::Observer(|e| log.borrow_mut().push(Ev::Spec(e)));
    let mut d = door::Observer(|e| log.borrow_mut().push(Ev::Door(e)));
    let mut l = Lock::new();
    for c in calls {
        match *c {
            Call::Enter(p) => l.enter::<BUGGY, _, _>(&mut s, &mut d, p),
            Call::Lock => l.lock(&mut d),
            Call::Status => {
                l.status();
            }
        }
    }
    (log.into_inner(), l)
}

/// "`assert` never receives false."
fn assert_never_false(t: &[Ev]) -> bool {
    !t.contains(&Ev::Spec(spec::Event::assert(0)))
}

/// "`attest` is only ever called right after `assert(1)`, and `unlock` only right after
/// `attest`" (so: the door opens only when the PIN was right).
fn unlock_after_code_ok(t: &[Ev]) -> bool {
    t.iter().enumerate().all(|(k, e)| match e {
        Ev::Spec(spec::Event::attest()) => k > 0 && t[k - 1] == Ev::Spec(spec::Event::assert(1)),
        Ev::Door(door::Event::unlock()) => k > 0 && t[k - 1] == Ev::Spec(spec::Event::attest()),
        _ => true,
    })
}

/// "After `alarm`, the door never unlocks."
fn no_unlock_after_alarm(t: &[Ev]) -> bool {
    match t.iter().position(|e| *e == Ev::Door(door::Event::alarm())) {
        Some(k) => !t[k..].contains(&Ev::Door(door::Event::unlock())),
        None => true,
    }
}

/// "`unlock` and `lock` alternate, starting with `unlock`."
fn bolt_alternates(t: &[Ev]) -> bool {
    let bolt: Vec<_> = t
        .iter()
        .filter_map(|e| match e {
            Ev::Door(d @ (door::Event::unlock() | door::Event::lock())) => Some(*d),
            _ => None,
        })
        .collect();
    bolt.iter().enumerate().all(|(k, d)| {
        *d == if k % 2 == 0 {
            door::Event::unlock()
        } else {
            door::Event::lock()
        }
    })
}

#[test]
fn right_pin_opens() {
    let (t, l) = run::<false>(&[Call::Enter(PIN)]);
    assert_eq!(l.state, State::Open);
    assert_eq!(
        t,
        vec![
            Ev::Spec(spec::Event::assert(1)),
            Ev::Spec(spec::Event::attest()),
            Ev::Door(door::Event::unlock())
        ]
    );
}

#[test]
fn three_wrong_pins_alarm() {
    let (t, l) = run::<false>(&[
        Call::Enter(1),
        Call::Enter(2),
        Call::Enter(3),
        Call::Enter(PIN),
    ]);
    assert_eq!(l.state, State::Alarm);
    assert_eq!(t, vec![Ev::Door(door::Event::alarm())]);
}

proptest! {
    #[test]
    fn correct_satisfies_every_property(calls in prop::collection::vec(call(), 0..40)) {
        let (t, _) = run::<false>(&calls);
        prop_assert!(assert_never_false(&t));
        prop_assert!(unlock_after_code_ok(&t));
        prop_assert!(no_unlock_after_alarm(&t));
        prop_assert!(bolt_alternates(&t));
    }
}

/// The buggy machine: proptest finds (and shrinks) a call sequence violating
/// `assert_never_false`. The shrunk counterexample is a single wrong PIN.
#[test]
fn buggy_is_refuted() {
    let mut runner = TestRunner::new(Config {
        failure_persistence: None,
        ..Config::default()
    });
    let r = runner.run(&prop::collection::vec(call(), 0..40), |calls| {
        let (t, _) = run::<true>(&calls);
        if assert_never_false(&t) {
            Ok(())
        } else {
            Err(TestCaseError::fail("assert(0)"))
        }
    });
    match r {
        Err(proptest::test_runner::TestError::Fail(_, calls)) => {
            println!("buggy counterexample (shrunk): {calls:?}");
            assert_eq!(calls.len(), 1);
            assert!(matches!(calls[0], Call::Enter(p) if p != PIN));
        }
        other => panic!("expected a counterexample, got {other:?}"),
    }
}
