use std::fmt;

pub type Range = std::ops::Range<usize>;
pub type Key<'a> = &'a str;

/// Represents Structured Field Value data types.
#[derive(Debug, PartialEq)]
pub enum Value {
    /// InnerList represents Inner lists.
    InnerList,
    /// String represents Strings.  range is the starting and ending
    /// positions in the input byte array.  escape is true if String
    /// contains `\` escaped character.
    String { range: Range, escape: bool },
    /// Token represents Tokens.  It contains the starting and ending
    /// positions in the input byte array.
    Token(Range),
    /// Integer represents Integers.
    Integer(i64),
    /// Decimal represents Decimals.  numer is the numerator and denom
    /// is the denominator of the number when it is represented in a
    /// rational number.
    Decimal { numer: i64, denom: i64 },
    Date(i64),
    /// ByteSeq represents Byte Sequences.  It contains the starting
    /// and ending positions in the input byte array.
    ByteSeq(Range),
    /// Bool represents Booleans.
    Bool(bool),
    /// DispString represents Display Strings.  It contains the
    /// starting and ending positions in the input byte array.
    DispString(Range),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::InnerList => {
                write!(f, "<InnerList>")
            }
            Value::String { range, escape } => {
                write!(f, "<String>{{{range:#?} escape={escape}}}",)
            }
            Value::Token(range) => {
                write!(f, "<Token>{{{range:#?}}}")
            }
            Value::Integer(v) => {
                write!(f, "<Integer>{{{v}}}")
            }
            Value::Decimal { numer, denom } => {
                write!(f, "<Decimal>{{{numer}/{denom}}}")
            }
            Value::Date(v) => {
                write!(f, "<Date>{{{v}}}")
            }
            Value::ByteSeq(range) => {
                write!(f, "<ByteSeq>{{{range:#?}}}")
            }
            Value::Bool(v) => {
                write!(f, "<Bool>{{{v}}}")
            }
            Value::DispString(range) => {
                write!(f, "<DispString>{{{range:#?}}}")
            }
        }
    }
}
