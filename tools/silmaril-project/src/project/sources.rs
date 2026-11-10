//! Node and answer sources: the tables of what declares DAG nodes and what
//! establishes statuses, in the style of [`super::edges::EDGE_KINDS`].
//!
//! `check` is generic over these tables. A layer that adds a node kind (a record that declares a
//! problem or a group) adds one [`NODE_SOURCES`] row; a layer that adds a way to establish a
//! status adds one [`ANSWER_SOURCES`] row. Arity-0 problems from silmaril's own `@[problem]`
//! (the dump's `problems` list) are the base nodes and are read before the table.

use super::schema::{Arg, Dump, Record};

/// A DAG node: a problem (`prop`, any arity) or a group.
#[derive(Debug, Clone)]
pub struct Node {
    pub kind: &'static str,
    pub decl: Option<String>,
    pub module: String,
    pub arity: i64,
    pub room: Option<String>,
    pub args: Vec<Arg>,
    pub title: Option<String>,
    pub doc: Option<String>,
    pub sid_override: Option<String>,
}

impl Node {
    /// An arity-0 problem (silmaril's `@[problem]`).
    pub fn closed(decl: &str, module: &str) -> Self {
        Node {
            kind: "prop",
            decl: Some(decl.into()),
            module: module.into(),
            arity: 0,
            room: None,
            args: Vec::new(),
            title: None,
            doc: None,
            sid_override: None,
        }
    }
}

/// What a node source does when its record's name is already a node.
#[derive(Debug, Clone, Copy)]
pub enum Existing {
    /// Refine an arity-0 `@[problem]`: the record must have arity 0, and its room is copied.
    Refine,
    /// Report this error at the record; the record's node replaces the old one.
    Error(&'static str),
}

/// One record kind that declares DAG nodes.
pub struct NodeSource {
    /// The record kind (`Record::kind`).
    pub record: &'static str,
    /// The node a record declares, named by the record's key.
    pub node: fn(&Record) -> Option<Node>,
    /// What to check on a new node: an error message, if any.
    pub check: fn(&Record) -> Option<String>,
    pub existing: Existing,
}

/// Every node source, in the order the dump lists records (one pass over the records).
pub const NODE_SOURCES: &[NodeSource] = &[
    NodeSource {
        record: "predicate",
        node: |r| match r {
            Record::Predicate(d) => Some(Node {
                arity: d.arity,
                room: d.room.clone(),
                args: d.args.clone(),
                ..Node::closed(&d.decl, &d.module)
            }),
            _ => None,
        },
        check: |r| match r {
            Record::Predicate(d) => {
                let positions: Vec<i64> = d.args.iter().map(|a| a.pos).collect();
                (d.arity < 0 || positions != (0..d.arity).collect::<Vec<_>>())
                    .then(|| format!("args must be positions 0..{}", d.arity))
            }
            _ => None,
        },
        existing: Existing::Refine,
    },
    NodeSource {
        record: "group",
        node: |r| match r {
            Record::Group(g) => Some(Node {
                kind: "group",
                decl: None,
                module: g.module.clone(),
                arity: 0,
                room: None,
                args: Vec::new(),
                title: g.title.clone(),
                doc: g.doc.clone(),
                sid_override: g.sid.clone(),
            }),
            _ => None,
        },
        check: |_| None,
        existing: Existing::Error("is also a problem"),
    },
];

/// The node source of a record kind, if it declares nodes.
pub fn node_source(record: &str) -> Option<&'static NodeSource> {
    NODE_SOURCES.iter().find(|s| s.record == record)
}

/// One answer: a theorem that establishes `status` of `problem`.
pub struct AnswerDecl<'a> {
    pub problem: &'a str,
    pub decl: &'a str,
    pub module: &'a str,
    /// An SZS status; anything else is an error (R5).
    pub status: &'a str,
    /// The `answers.source` column.
    pub source: &'a str,
    pub witness: Option<&'a Vec<String>>,
    pub axioms: &'a [String],
}

/// One place answers come from.
pub struct AnswerSource {
    pub answers: for<'a> fn(&'a Dump) -> Vec<AnswerDecl<'a>>,
}

/// Every answer source. The first reason found for a status is the one recorded, so the order
/// is part of the `statuses` table.
pub const ANSWER_SOURCES: &[AnswerSource] = &[
    // `@[answers "N" s]` records (layer 1).
    AnswerSource {
        answers: |dump| {
            dump.records
                .iter()
                .filter_map(|r| match r {
                    Record::Answer(a) => Some(AnswerDecl {
                        problem: &a.name,
                        decl: &a.decl,
                        module: &a.module,
                        status: &a.status,
                        source: "answers",
                        witness: a.witness.as_ref(),
                        axioms: &a.axioms,
                    }),
                    _ => None,
                })
                .collect()
        },
    },
    // silmaril's `@[solves]` (THM) and `@[refutes]` (UNS) (layer 0).
    AnswerSource {
        answers: |dump| {
            dump.solutions
                .iter()
                .map(|s| AnswerDecl {
                    problem: &s.problem,
                    decl: &s.decl,
                    module: &s.module,
                    status: match s.kind.as_str() {
                        "solves" => "THM",
                        "refutes" => "UNS",
                        _ => "",
                    },
                    source: &s.kind,
                    witness: None,
                    axioms: &s.axioms,
                })
                .collect()
        },
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::project::schema::KINDS;

    #[test]
    fn node_sources_are_record_kinds() {
        for s in NODE_SOURCES {
            assert!(KINDS.iter().any(|(r, _)| *r == s.record), "{}", s.record);
            assert_eq!(node_source(s.record).map(|x| x.record), Some(s.record));
        }
        assert!(!ANSWER_SOURCES.is_empty());
    }
}
