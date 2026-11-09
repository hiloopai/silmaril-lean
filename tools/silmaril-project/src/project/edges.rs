//! Edge kinds: the one table of the record kinds that declare DAG edges, what R6 allows
//! at their endpoints, how scope follows them, and how statuses flow along them.
//!
//! `check` is generic over this table: adding an edge kind (v0.2's `refines`, `compose`,
//! `transfer`) is one [`Record`] variant in `schema.rs`, one arm in [`parts`] and one row in
//! [`EDGE_KINDS`], plus a [`Rule`] variant only when no existing rule fits.

use super::schema::Record;

/// Which way a transferred status goes along an edge `parent → child`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dir {
    /// From the parent to the child.
    Down,
    /// From the child to the parent.
    Up,
}

/// How statuses flow along the edges of one record kind.
#[derive(Debug, Clone, Copy)]
pub enum Rule {
    /// Declared edges: nothing flows.
    Declared,
    /// The parent gets the status once every child of the record holds. The edges of the whole
    /// dump count, so a record with a missing or out-of-scope child never fires.
    AllChildrenHold(&'static str),
    /// The parent gets the status once the child fails.
    ChildFails(&'static str),
    /// `(direction, status, needs the record's fixed values to parse)`, over in-scope edges.
    Transfer(&'static [(Dir, &'static str, bool)]),
}

/// One record kind that declares edges.
#[derive(Debug)]
pub struct EdgeKind {
    /// The record kind (`Record::kind`).
    pub record: &'static str,
    /// The `edges.kind` column.
    pub kind: &'static str,
    /// R6: an endpoint may be a group.
    pub groups: bool,
    /// R6: both endpoints are arity-0 problems.
    pub closed: bool,
    /// Scope follows the edge from the child up to the parent too (statuses flow both ways).
    pub scope_up: bool,
    pub rule: Rule,
}

/// The `instance` transfer rules: THM and UNS go down, SAT and CSA go up; THM down and
/// CSA up need every value the instance fixes to parse.
pub const INSTANCE_RULES: &[(Dir, &str, bool)] = &[
    (Dir::Down, "THM", true),
    (Dir::Down, "UNS", false),
    (Dir::Up, "SAT", false),
    (Dir::Up, "CSA", true),
];

/// Every edge kind. Propagation applies the rules in this order within one round.
pub const EDGE_KINDS: &[EdgeKind] = &[
    EdgeKind {
        record: "children",
        kind: "sub",
        groups: true,
        closed: false,
        scope_up: false,
        rule: Rule::Declared,
    },
    EdgeKind {
        record: "refutation_route",
        kind: "refute",
        groups: false,
        closed: true,
        scope_up: false,
        rule: Rule::ChildFails("UNS"),
    },
    EdgeKind {
        record: "decomposition",
        kind: "sub",
        groups: true,
        closed: true,
        scope_up: false,
        rule: Rule::AllChildrenHold("THM"),
    },
    EdgeKind {
        record: "instance",
        kind: "instance",
        groups: false,
        closed: false,
        scope_up: true,
        rule: Rule::Transfer(INSTANCE_RULES),
    },
];

/// The edge kind of a record kind, if it declares edges.
pub fn edge_kind(record: &str) -> Option<&'static EdgeKind> {
    EDGE_KINDS.iter().find(|k| k.record == record)
}

/// The edges a record declares: `(parent, children, via)`, `via` being the proof or the
/// instance decl (none for declared edges).
pub fn parts(r: &Record) -> Option<(&str, Vec<&String>, Option<&String>)> {
    Some(match r {
        Record::Children(c) => (&c.name, c.children.iter().collect(), None),
        Record::Decomposition(d) => (&d.parent, d.children.iter().collect(), Some(&d.proof)),
        Record::RefutationRoute(rr) => (&rr.parent, vec![&rr.child], Some(&rr.proof)),
        Record::Instance(i) => (&i.of, vec![&i.name], Some(&i.decl)),
        _ => return None,
    })
}

/// The values a record fixes, whose parse obligations condition its transfer rules (and are
/// in scope with it).
pub fn fixed_values(r: &Record) -> Vec<&str> {
    match r {
        Record::Instance(i) => i.args.iter().filter_map(|a| a.value.as_deref()).collect(),
        _ => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::project::schema::KINDS;

    #[test]
    fn edge_kinds_are_record_kinds() {
        for k in EDGE_KINDS {
            assert!(KINDS.iter().any(|(r, _)| *r == k.record), "{}", k.record);
            assert_eq!(edge_kind(k.record).map(|e| e.kind), Some(k.kind));
        }
    }
}
