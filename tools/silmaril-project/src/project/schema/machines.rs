//! Machines: the `machine` record (a machine document, `Silmaril.Automata.Document`) and the
//! `machine_binding` record (a typed Lean machine proved equal to a document).
//!
//! A machine row keeps the counts and the canonical JSON (`canonical`: states, labels and edges
//! sorted and deduplicated, keys sorted), which is the document's content identity and what the
//! explorer draws (layers included), and, for a machine with one initial state, its immediate-
//! dominator table (`dominators`, state → dominator, compact JSON) with the kernel-checked theorem
//! that proves it (`dominator_theorem`). The lists as written stay in the records file; the layer
//! lists are read only to accept them.
use super::*;
use serde::Deserialize;

table! {
    Machine = "machines", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
        doc: Option<String> = "TEXT",
        deterministic: bool = "INTEGER NOT NULL",
        #[serde(skip)] n_states: i64 = "INTEGER NOT NULL",
        #[serde(skip)] n_labels: i64 = "INTEGER NOT NULL",
        #[serde(skip)] n_edges: i64 = "INTEGER NOT NULL",
        canonical: String = "TEXT NOT NULL",
        dominators: Option<serde_json::Value> = "TEXT",
        dominator_theorem: Option<String> = "TEXT",
    }
    extra {
        #[serde(rename = "sid")] sid_override: Option<String>,
        #[serde(default)] states: Vec<String>,
        #[serde(default)] labels: Vec<String>,
        #[serde(default)] edges: Vec<[String; 3]>,
        #[serde(default)] #[allow(dead_code)] initial: Vec<String>,
        #[serde(default)] #[allow(dead_code)] accepting: Vec<String>,
        #[serde(default)] #[allow(dead_code)] rejecting: Vec<String>,
        #[serde(default)] #[allow(dead_code)] error: Vec<String>,
    }
}

table! {
    MachineBinding = "machine_bindings", key("name") {
        name: String = "TEXT NOT NULL",
        machine: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        marks: Option<String> = "TEXT",
        theorem: String = "TEXT NOT NULL",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
        doc: Option<String> = "TEXT",
    }
}
