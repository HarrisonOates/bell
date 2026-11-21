// Copyright 2026 Harrison Oates
// SPDX-License-Identifier: Apache-2.0

/// Informational work accounting. This counter never interrupts a check, even
/// when its reporting range is exhausted.
#[derive(Default)]
pub(crate) struct Work {
    pub used: u64,
}

impl Work {
    pub fn tick(&mut self) {
        self.charge(1);
    }
    pub fn charge(&mut self, amount: u64) {
        self.used = self.used.saturating_add(amount);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn work_reporting_never_stops_at_the_old_limit_or_on_overflow() {
        let mut work = Work::default();
        work.charge(10_000_000);
        work.tick();
        assert_eq!(work.used, 10_000_001);
        work.charge(u64::MAX);
        work.tick();
        assert_eq!(work.used, u64::MAX);
    }
}
