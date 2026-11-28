use crate::analysis;
use crate::dwarf::InlineHints;
use crate::elf::{clone_base, outline_name, Image, Inventory, Pair};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

pub struct Build<'a> {
    pub id: &'a str,
    pub functions: Vec<NamedFunction>,
    pub names: BTreeMap<String, Vec<usize>>,
    pub inline: InlineHints,
    pub exports: BTreeSet<String>,
    pub inventory: Inventory,
    pub pair: Pair,
}

pub struct NamedFunction {
    pub names: BTreeSet<String>,
    pub address: u64,
    pub bytes: Vec<u8>,
    pub metrics: analysis::Function,
    pub sample_bytes: Option<String>,
}

impl<'a> Build<'a> {
    pub fn new(id: &'a str, image: Image<'_>, inline: InlineHints, pair: Pair) -> Self {
        let mut names = BTreeMap::<String, Vec<_>>::new();
        let mut functions = Vec::new();
        for span in &image.spans {
            for name in &span.names {
                names.entry(name.clone()).or_default().push(functions.len());
            }
            functions.push(NamedFunction {
                names: span.names.clone(),
                address: span.address,
                bytes: span.bytes.to_vec(),
                metrics: analysis::analyze(&image, span),
                sample_bytes: (span.bytes.len() <= 32
                    && span
                        .names
                        .iter()
                        .any(|name| analysis::SAMPLES.contains(&name.as_str())))
                .then(|| crate::hex(span.bytes)),
            });
        }
        Self {
            id,
            functions,
            names,
            inline,
            exports: image.exports,
            inventory: image.inventory,
            pair,
        }
    }

    pub fn summary(&self) -> Summary<'_> {
        let mut counts = analysis::Counts::default();
        let mut named_targets = BTreeMap::new();
        let mut direct_edges = 0;
        for f in &self.functions {
            counts.add(&f.metrics.counts);
            direct_edges += f.metrics.direct_callees.len();
            for (name, sites) in &f.metrics.special_targets {
                *named_targets.entry(name.as_str()).or_default() += sites;
            }
        }
        let samples = analysis::SAMPLES
            .iter()
            .map(|&name| {
                let sample = match self.names.get(name).map(Vec::as_slice) {
                    Some(&[i]) => {
                        let f = &self.functions[i];
                        Some(Sample {
                            address: f.address,
                            size_bytes: f.bytes.len(),
                            names: &f.names,
                            short_slice_hex: f.sample_bytes.as_deref(),
                            exact_sha256: &f.metrics.exact,
                            normalized_sha256: f.metrics.normalized.as_deref(),
                            counts: &f.metrics.counts,
                            direct_callees: &f.metrics.direct_callees,
                            transfer_examples: &f.metrics.transfer_examples,
                            table_examples: &f.metrics.table_examples,
                        })
                    }
                    _ => None,
                };
                (name, sample)
            })
            .collect();
        Summary {
            inventory: &self.inventory,
            stripped_pair: &self.pair,
            inline_hints: &self.inline,
            symbol_names: self.names.len(),
            dynamic_export_names: self.exports.len(),
            usable_bytes: self.functions.iter().map(|f| f.bytes.len()).sum(),
            distinct_direct_call_edges: direct_edges,
            unresolved_indirect_call_sites: counts.indirect_call_sites
                - counts.got_named_indirect_call_sites,
            unresolved_indirect_jump_sites: counts.indirect_jump_sites
                - counts.got_named_indirect_jump_sites,
            counts,
            outline_name_examples: self
                .names
                .keys()
                .map(String::as_str)
                .filter(|name| outline_name(name))
                .take(6)
                .collect(),
            named_targets,
            samples,
        }
    }
}

#[derive(Serialize)]
struct Sample<'a> {
    address: u64,
    size_bytes: usize,
    names: &'a BTreeSet<String>,
    short_slice_hex: Option<&'a str>,
    exact_sha256: &'a str,
    normalized_sha256: Option<&'a str>,
    counts: &'a analysis::Counts,
    direct_callees: &'a BTreeSet<String>,
    transfer_examples: &'a [analysis::Transfer],
    table_examples: &'a [analysis::Table],
}

#[derive(Serialize)]
pub struct Summary<'a> {
    inventory: &'a Inventory,
    stripped_pair: &'a Pair,
    inline_hints: &'a InlineHints,
    symbol_names: usize,
    dynamic_export_names: usize,
    usable_bytes: usize,
    distinct_direct_call_edges: usize,
    unresolved_indirect_call_sites: usize,
    unresolved_indirect_jump_sites: usize,
    counts: analysis::Counts,
    outline_name_examples: Vec<&'a str>,
    named_targets: BTreeMap<&'a str, usize>,
    samples: BTreeMap<&'a str, Option<Sample<'a>>>,
}

#[derive(Default, Serialize)]
pub struct Direction {
    total_spans: usize,
    total_bytes: usize,
    matched_bytes: usize,
    symbol_names: usize,
    dynamic_export_names: usize,
    ambiguous_spans: usize,
    unmatched_spans: usize,
    unmatched_clone_hint_only: usize,
    unmatched_inline_hint_only: usize,
    unmatched_clone_and_inline_hint: usize,
    unmatched_unknown: usize,
    normalized_spans_all: usize,
    cfg_spans_all: usize,
    cfg_edges_all: usize,
    cfg_edges_both_eligible: usize,
    direct_call_edges_all: usize,
    direct_call_edges_both_decoded: usize,
}

#[derive(Default, Serialize)]
pub struct Overlap {
    intersecting_symbol_names: usize,
    intersecting_dynamic_export_names: usize,
    matched_spans: usize,
    exact_spans: usize,
    exact_bytes: usize,
    normalized_eligible_pairs: usize,
    normalized_equal_pairs: usize,
    normalized_equal_exact_different_pairs: usize,
    cfg_eligible_pairs: usize,
    cfg_equal_pairs: usize,
    intersecting_cfg_edges: usize,
    call_graph_eligible_pairs: usize,
    intersecting_direct_call_edges: usize,
}

#[derive(Serialize)]
pub struct Comparison<'a> {
    left: &'a str,
    right: &'a str,
    left_denominators: Direction,
    right_denominators: Direction,
    overlap: Overlap,
}

fn candidates(source: &Build<'_>, target: &Build<'_>) -> Vec<BTreeSet<usize>> {
    source
        .functions
        .iter()
        .map(|f| {
            f.names
                .iter()
                .filter_map(|name| target.names.get(name))
                .flatten()
                .copied()
                .collect()
        })
        .collect()
}

fn denominator(
    source: &Build<'_>,
    target: &Build<'_>,
    peers: &[BTreeSet<usize>],
    reverse: &[BTreeSet<usize>],
) -> Direction {
    let mut totals = Direction {
        total_spans: source.functions.len(),
        symbol_names: source.names.len(),
        dynamic_export_names: source.exports.len(),
        ..Default::default()
    };
    let target_bases: BTreeSet<_> = target
        .names
        .keys()
        .filter_map(|name| clone_base(name))
        .collect();
    for (i, f) in source.functions.iter().enumerate() {
        totals.total_bytes += f.bytes.len();
        totals.normalized_spans_all += usize::from(f.metrics.normalized.is_some());
        if let Some(cfg) = &f.metrics.cfg {
            totals.cfg_spans_all += 1;
            totals.cfg_edges_all += cfg.edges.len();
        }
        totals.direct_call_edges_all += f.metrics.direct_callees.len();
        match peers[i].len() {
            0 => {
                totals.unmatched_spans += 1;
                let clone = f.names.iter().any(|name| {
                    let base = clone_base(name).unwrap_or(name);
                    target_bases.contains(base) || (base != name && target.names.contains_key(base))
                });
                let inline = f.names.iter().any(|name| {
                    target
                        .inline
                        .sites_by_name
                        .contains_key(clone_base(name).unwrap_or(name))
                });
                match (clone, inline) {
                    (true, true) => totals.unmatched_clone_and_inline_hint += 1,
                    (true, false) => totals.unmatched_clone_hint_only += 1,
                    (false, true) => totals.unmatched_inline_hint_only += 1,
                    (false, false) => totals.unmatched_unknown += 1,
                }
            }
            1 if reverse[*peers[i].first().unwrap()].len() == 1 => {}
            _ => totals.ambiguous_spans += 1,
        }
    }
    totals
}

pub fn compare<'a>(left: &Build<'a>, right: &Build<'a>) -> Comparison<'a> {
    let forward = candidates(left, right);
    let reverse = candidates(right, left);
    let mut left_denominators = denominator(left, right, &forward, &reverse);
    let mut right_denominators = denominator(right, left, &reverse, &forward);
    let mut overlap = Overlap {
        intersecting_symbol_names: left
            .names
            .keys()
            .filter(|name| right.names.contains_key(*name))
            .count(),
        intersecting_dynamic_export_names: left.exports.intersection(&right.exports).count(),
        ..Default::default()
    };
    for (i, peers) in forward.iter().enumerate() {
        let Some(&j) = peers
            .first()
            .filter(|&&j| peers.len() == 1 && reverse[j].len() == 1)
        else {
            continue;
        };
        let a = &left.functions[i];
        let b = &right.functions[j];
        overlap.matched_spans += 1;
        left_denominators.matched_bytes += a.bytes.len();
        right_denominators.matched_bytes += b.bytes.len();
        let exact = a.bytes == b.bytes;
        if exact {
            overlap.exact_spans += 1;
            overlap.exact_bytes += a.bytes.len();
        }
        if let (Some(a), Some(b)) = (&a.metrics.normalized, &b.metrics.normalized) {
            overlap.normalized_eligible_pairs += 1;
            overlap.normalized_equal_pairs += usize::from(a == b);
            overlap.normalized_equal_exact_different_pairs += usize::from(a == b && !exact);
        }
        if let (Some(a), Some(b)) = (&a.metrics.cfg, &b.metrics.cfg) {
            overlap.cfg_eligible_pairs += 1;
            overlap.cfg_equal_pairs += usize::from(a == b);
            overlap.intersecting_cfg_edges += a.edges.intersection(&b.edges).count();
            left_denominators.cfg_edges_both_eligible += a.edges.len();
            right_denominators.cfg_edges_both_eligible += b.edges.len();
        }
        if a.metrics.counts.analyzed_spans == 1 && b.metrics.counts.analyzed_spans == 1 {
            overlap.call_graph_eligible_pairs += 1;
            let a = &a.metrics.direct_callees;
            let b = &b.metrics.direct_callees;
            overlap.intersecting_direct_call_edges += a.intersection(b).count();
            left_denominators.direct_call_edges_both_decoded += a.len();
            right_denominators.direct_call_edges_both_decoded += b.len();
        }
    }

    for direction in [&left_denominators, &right_denominators] {
        assert_eq!(
            direction.total_spans,
            overlap.matched_spans + direction.ambiguous_spans + direction.unmatched_spans
        );
    }
    Comparison {
        left: left.id,
        right: right.id,
        left_denominators,
        right_denominators,
        overlap,
    }
}
