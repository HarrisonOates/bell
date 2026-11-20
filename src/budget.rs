use crate::report::{Diagnostic, Result, Status};
use std::time::{Duration, Instant};

pub(crate) struct Budget {
    pub used: u64,
    limit: u64,
    started: Instant,
    timeout: Option<Duration>,
}

impl Budget {
    pub fn new(limit: u64, timeout: Option<Duration>) -> Self {
        Self {
            used: 0,
            limit,
            started: Instant::now(),
            timeout,
        }
    }
    pub fn tick(&mut self) -> Result<()> {
        self.charge(1)
    }
    pub fn charge(&mut self, amount: u64) -> Result<()> {
        if amount > self.limit.saturating_sub(self.used) {
            return Err(Diagnostic::new(
                Status::LimitExceeded,
                "work_limit",
                "validation work limit exceeded",
            ));
        }
        self.used += amount;
        if self.timeout.is_some_and(|t| self.started.elapsed() >= t) {
            return Err(Diagnostic::new(
                Status::LimitExceeded,
                "timeout",
                "validation time limit exceeded",
            ));
        }
        Ok(())
    }
}
