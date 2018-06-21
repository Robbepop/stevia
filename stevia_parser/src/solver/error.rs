use solver::Command;

use std;

/// The current exeuction mode of the SMT solver.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ExecutionMode {
    /// The starting mode.
    ///
    /// # Note
    ///
    /// This state is reached after initialization of an SMT solver
    /// or after resetting it via the `reset` command.
    Start,
    /// The asstion mode.
    ///
    /// # Note
    ///
    /// This is the state reached after asserting anything.
    Assert,
    /// The sat mode.
    ///
    /// # Note
    ///
    /// This state is reached after the solver found the current
    /// input to be satisfiable.
    Sat,
    /// The unsat mode.
    ///
    /// # Note
    ///
    /// This state is reached after the solver found the current
    /// input to be unsatisfiable.
    Unsat,
}

/// Represents the unsupported entity.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnsupportedEntity {
    /// The command is unsupported.
    Command(Command),
    /// The theory is unsupported.
    Theory(String),
    /// Something that is not further specified is unsupported.
    Other,
}

/// The kind of the respective response error.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ResponseErrorKind {
    /// Some entity is unsupported.
    Unsupported(UnsupportedEntity),
    /// A supported command was unexpected given the current execution mode of the solver.
    UnexpectedCommand { cmd: Command, mode: ExecutionMode },
}

/// An error response from the SMT solver back to the parser.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResponseError {
    kind: ResponseErrorKind,
}

impl ResponseError {
    /// Returns the kind of `self`.
    pub fn kind(&self) -> &ResponseErrorKind {
        &self.kind
    }

    /// Transforms `self` into its kind.
    pub fn into_kind(self) -> ResponseErrorKind {
        self.kind
    }

    /// Creates a new response error given the error kind.
    pub(self) fn new(kind: ResponseErrorKind) -> Self {
        Self { kind }
    }

    /// Creates a new response error indicated that something is unsupported.
    ///
    /// # Note
    ///
    /// This means that something that is not further specified is unsupported.
    pub fn unsupported() -> Self {
        Self::new(ResponseErrorKind::Unsupported(UnsupportedEntity::Other))
    }

    /// Creates a new response error indicating that the given command is unsupported.
    pub fn unsupported_command(cmd: Command) -> Self {
        Self::new(ResponseErrorKind::Unsupported(UnsupportedEntity::Command(
            cmd,
        )))
    }

    /// Creates a new response error indicating that the given theory is unsupported.
    pub fn unsupported_theory<S>(name: S) -> Self
    where
        S: Into<String>,
    {
        Self::new(ResponseErrorKind::Unsupported(UnsupportedEntity::Theory(
            name.into(),
        )))
    }

    /// Creates a new response error indicating that the given command was unexpected
    /// given the current execution mode of the solver. However, the given command is
    /// supported in general.
    pub fn unexpected_command(cmd: Command, mode: ExecutionMode) -> Self {
        Self::new(ResponseErrorKind::UnexpectedCommand { cmd, mode })
    }
}

impl std::fmt::Display for ResponseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use self::ResponseErrorKind::*;
        match self.kind() {
            Unsupported(entity) => {
                use self::UnsupportedEntity::*;
                match entity {
                    Theory(theory) => write!(f, "encountered unsupported theory: {:?}", theory),
                    Command(command) => write!(f, "encountered unsupported command: {:?}", command),
                    Other => write!(f, "encountered unsupported entity"),
                }
            }
            UnexpectedCommand { cmd, mode } => write!(
                f,
                "encountered unexpected command (= {:?}) in the current execution mode (= {:?})",
                cmd, mode
            ),
        }
    }
}

impl std::error::Error for ResponseError {
    fn description(&self) -> &'static str {
        use self::ResponseErrorKind::*;
        match self.kind() {
            Unsupported(_) => "encountered unsupported entity (theory, command, etc..)",
            UnexpectedCommand { .. } => {
                "encountered unexpected command in the current execution mode"
            }
        }
    }

    fn cause(&self) -> Option<&std::error::Error> {
        None
    }
}

/// Convenience type alias for `ResponseError`.
///
/// This enables the SMT solver to communicate error or success back
/// to the SMTLib2 parser.
pub type ResponseResult = std::result::Result<(), ResponseError>;
