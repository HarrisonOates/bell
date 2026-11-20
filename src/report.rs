use serde::Serialize;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Status {
    Valid,
    InvalidPlan,
    InputError,
    Unsupported,
    LimitExceeded,
    UnsolvabilityReport,
    InternalError,
    ProfileRejected,
}

impl Status {
    pub fn exit_code(self) -> u8 {
        match self {
            Self::Valid => 0,
            Self::InvalidPlan => 1,
            Self::InputError => 2,
            Self::Unsupported => 3,
            Self::LimitExceeded => 4,
            Self::UnsolvabilityReport => 5,
            Self::InternalError => 6,
            Self::ProfileRejected => 7,
        }
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct Location {
    pub file: String,
    pub line: u32,
    pub column: u32,
}

impl Location {
    pub(crate) fn new(file: &str, pos: hddl_analyzer::TokenPosition) -> Self {
        Self {
            file: file.into(),
            line: pos.line + 1,
            column: pos.column + 1,
        }
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct Diagnostic {
    pub status: Status,
    pub code: String,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<Box<Location>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub occurrence: Option<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub counterexample: Vec<String>,
}

impl Diagnostic {
    pub(crate) fn new(status: Status, code: &str, message: impl Into<String>) -> Self {
        Self {
            status,
            code: code.into(),
            message: message.into(),
            location: None,
            occurrence: None,
            counterexample: vec![],
        }
    }
    pub(crate) fn input(code: &str, message: impl Into<String>) -> Self {
        Self::new(Status::InputError, code, message)
    }
    pub(crate) fn invalid(code: &str, message: impl Into<String>) -> Self {
        Self::new(Status::InvalidPlan, code, message)
    }
    pub(crate) fn unsupported(message: impl Into<String>) -> Self {
        Self::new(Status::Unsupported, "unsupported_feature", message)
    }
    pub(crate) fn at(mut self, location: Location) -> Self {
        self.location = Some(Box::new(location));
        self
    }
    pub(crate) fn task(mut self, id: &str) -> Self {
        self.occurrence = Some(id.into());
        self
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(l) = &self.location {
            write!(f, "{}:{}:{}: ", l.file, l.line, l.column)?;
        }
        write!(f, "{}: {}", self.code, self.message)?;
        if let Some(id) = &self.occurrence {
            write!(f, " [occurrence {id}]")?;
        }
        if !self.counterexample.is_empty() {
            write!(
                f,
                "\n  failing prefix: {}",
                self.counterexample.join(" -> ")
            )?;
        }
        Ok(())
    }
}
impl std::error::Error for Diagnostic {}

pub(crate) type Result<T> = std::result::Result<T, Diagnostic>;

#[derive(Debug, Serialize)]
pub struct Metrics {
    pub actions: usize,
    pub makespan: usize,
    /// Decimal string keeps integer sums exact in JSON consumers.
    pub cost: String,
    pub objective: String,
    pub quality: String,
}

#[derive(Debug, Serialize)]
pub struct Report {
    pub schema_version: u32,
    pub validator_version: &'static str,
    pub status: Status,
    pub work: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metrics: Option<Metrics>,
    pub diagnostics: Vec<Diagnostic>,
}
