//! Layer 4, rooms: the `room` record.
use super::*;
use serde::Deserialize;

table! {
    /// `silmaril room NAME := R` over silmaril's `Room`; Lean fills `sen` and `mod` (the
    /// pretty-printed sentence type and model carrier).
    Room = "rooms", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        sen: String = "TEXT NOT NULL",
        r#mod: String = "TEXT NOT NULL",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
        doc: Option<String> = "TEXT",
    }
    extra { #[serde(rename = "sid")] sid_override: Option<String>, }
}
