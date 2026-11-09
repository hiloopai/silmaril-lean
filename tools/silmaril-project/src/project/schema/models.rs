//! Layer 5, models and specs: the `model` and `spec` records.
use super::*;
use serde::Deserialize;

table! {
    Spec = "specs", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        model: Option<String> = "TEXT",
        format: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
        doc: Option<String> = "TEXT",
    }
    extra { #[serde(rename = "sid")] sid_override: Option<String>, }
}

table! {
    Model = "models", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
        doc: Option<String> = "TEXT",
    }
    extra { #[serde(rename = "sid")] sid_override: Option<String>, }
}
