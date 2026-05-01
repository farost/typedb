/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

// let's start with a simple and fast global list of NAME = COUNTER for now.

use std::{
    sync::{
        OnceLock,
        atomic::{AtomicU64, Ordering},
    },
    thread,
    time::Duration,
};

use crate::constants::server::PERF_COUNTERS_ENABLED;

pub struct Counter {
    counter: AtomicU64,
    enabled: bool,
}

impl Counter {
    const fn new(enabled: bool) -> Self {
        Self { counter: AtomicU64::new(0), enabled }
    }

    pub fn increment(&self) {
        if self.enabled {
            self.counter.fetch_add(1, Ordering::Relaxed);
        }
    }

    pub fn update_max(&self, value: u64) {
        if self.enabled {
            self.counter.fetch_max(value, Ordering::Relaxed);
        }
    }

    pub fn value(&self) -> u64 {
        self.counter.load(Ordering::Relaxed)
    }
}

pub struct Timer {
    count: AtomicU64,
    nanos: AtomicU64,
    enabled: bool,
}

impl Timer {
    pub const fn new(enabled: bool) -> Self {
        Self { count: AtomicU64::new(0), nanos: AtomicU64::new(0), enabled }
    }

    #[inline]
    pub fn record(&self, nanos: u64) {
        if self.enabled {
            self.count.fetch_add(1, Ordering::Relaxed);
            self.nanos.fetch_add(nanos, Ordering::Relaxed);
        }
    }

    pub fn count(&self) -> u64 {
        self.count.load(Ordering::Relaxed)
    }

    pub fn nanos(&self) -> u64 {
        self.nanos.load(Ordering::Relaxed)
    }
}

pub static QUERY_CACHE_HITS: Counter = Counter::new(PERF_COUNTERS_ENABLED);
pub static QUERY_CACHE_MISSES: Counter = Counter::new(PERF_COUNTERS_ENABLED);
pub static QUERY_CACHE_FLUSH: Counter = Counter::new(PERF_COUNTERS_ENABLED);

pub static TXN_OPEN_TOTAL: Timer = Timer::new(PERF_COUNTERS_ENABLED);
pub static TXN_OPEN_RECORD: Timer = Timer::new(PERF_COUNTERS_ENABLED);
pub static TXN_OPEN_RECORD_LOCK_WAIT: Timer = Timer::new(PERF_COUNTERS_ENABLED);
pub static TXN_OPEN_BLOCKING: Timer = Timer::new(PERF_COUNTERS_ENABLED);
pub static TXN_TABLE_SIZE_PEAK: Counter = Counter::new(PERF_COUNTERS_ENABLED);
pub static WAL_FSYNC_FILE: Timer = Timer::new(PERF_COUNTERS_ENABLED);
pub static WAL_FSYNC_DIRECTORY: Timer = Timer::new(PERF_COUNTERS_ENABLED);
pub static COMMIT_WRITE_TOTAL: Timer = Timer::new(PERF_COUNTERS_ENABLED);
pub static COMMIT_WRITE_FINALISE: Timer = Timer::new(PERF_COUNTERS_ENABLED);
pub static COMMIT_WRITE_DATA_COMMIT: Timer = Timer::new(PERF_COUNTERS_ENABLED);
pub static COMMIT_WRITE_SPAWN_BLOCKING_GAP: Timer = Timer::new(PERF_COUNTERS_ENABLED);
pub static STORAGE_SNAPSHOT_COMMIT: Timer = Timer::new(PERF_COUNTERS_ENABLED);
pub static STORAGE_SET_INITIAL_PUT_STATUS: Timer = Timer::new(PERF_COUNTERS_ENABLED);
pub static SNAPSHOT_ID_NEW: Counter = Counter::new(PERF_COUNTERS_ENABLED);
pub static COMMIT_HAS_CHANGES_CALLS: Counter = Counter::new(PERF_COUNTERS_ENABLED);

pub trait DumpItem: Sync {
    fn format(&self) -> String;
}

impl DumpItem for Counter {
    fn format(&self) -> String {
        format!("n={}", self.value())
    }
}

impl DumpItem for Timer {
    fn format(&self) -> String {
        let n = self.count();
        let total = self.nanos();
        let avg = if n == 0 { 0 } else { total / n };
        format!("n={} total={} avg={}", n, format_nanos(total), format_nanos(avg))
    }
}

fn format_nanos(nanos: u64) -> String {
    if nanos < 1_000 {
        format!("{}ns", nanos)
    } else if nanos < 1_000_000 {
        format!("{:.2}us", nanos as f64 / 1_000.0)
    } else {
        format!("{:.2}ms", nanos as f64 / 1_000_000.0)
    }
}

static DUMP_ITEMS: &[(&'static str, &'static dyn DumpItem)] = &[
    ("QUERY_CACHE_HITS", &QUERY_CACHE_HITS),
    ("QUERY_CACHE_MISSES", &QUERY_CACHE_MISSES),
    ("QUERY_CACHE_FLUSH", &QUERY_CACHE_FLUSH),
    ("TXN_OPEN_TOTAL", &TXN_OPEN_TOTAL),
    ("TXN_OPEN_RECORD", &TXN_OPEN_RECORD),
    ("TXN_OPEN_RECORD_LOCK_WAIT", &TXN_OPEN_RECORD_LOCK_WAIT),
    ("TXN_OPEN_BLOCKING", &TXN_OPEN_BLOCKING),
    ("TXN_TABLE_SIZE_PEAK", &TXN_TABLE_SIZE_PEAK),
    ("WAL_FSYNC_FILE", &WAL_FSYNC_FILE),
    ("WAL_FSYNC_DIRECTORY", &WAL_FSYNC_DIRECTORY),
    ("COMMIT_WRITE_TOTAL", &COMMIT_WRITE_TOTAL),
    ("COMMIT_WRITE_FINALISE", &COMMIT_WRITE_FINALISE),
    ("COMMIT_WRITE_DATA_COMMIT", &COMMIT_WRITE_DATA_COMMIT),
    ("COMMIT_WRITE_SPAWN_BLOCKING_GAP", &COMMIT_WRITE_SPAWN_BLOCKING_GAP),
    ("STORAGE_SNAPSHOT_COMMIT", &STORAGE_SNAPSHOT_COMMIT),
    ("STORAGE_SET_INITIAL_PUT_STATUS", &STORAGE_SET_INITIAL_PUT_STATUS),
    ("SNAPSHOT_ID_NEW", &SNAPSHOT_ID_NEW),
    ("COMMIT_HAS_CHANGES_CALLS", &COMMIT_HAS_CHANGES_CALLS),
];

pub fn dump() -> String {
    let mut out = String::new();
    for (name, item) in DUMP_ITEMS {
        out.push_str("[perf] ");
        out.push_str(name);
        out.push(' ');
        out.push_str(&item.format());
        out.push('\n');
    }
    out
}

static DUMP_THREAD_STARTED: OnceLock<()> = OnceLock::new();

pub fn spawn_periodic_dump(interval: Duration) {
    if !PERF_COUNTERS_ENABLED {
        return;
    }
    let mut spawned = false;
    DUMP_THREAD_STARTED.get_or_init(|| {
        spawned = true;
    });
    if !spawned {
        return;
    }
    thread::Builder::new()
        .name("perf-dump".to_string())
        .spawn(move || {
            loop {
                thread::sleep(interval);
                eprintln!("[perf] === dump ===");
                eprint!("{}", dump());
            }
        })
        .expect("Failed to spawn perf-dump thread");
}
