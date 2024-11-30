//! [RFC 9651](https://datatracker.ietf.org/doc/html/rfc9651)
//! Structured Field Values parser.
//!
//! Provides Structured Field Values parser that is designed not to do
//! any extra allocation, like allocating maps, lists, and Strings,
//! and do the minimal stuff to parse the input data.
//!
//! This is an example of parsing [RFC
//! 9218](https://datatracker.ietf.org/doc/html/rfc9218) Priority
//! header field:
//!
//! ```
//! use sfparse::{Parser, Value};
//!
//! let mut urgency :i32 = 3;
//! let mut incremental = false;
//! let mut p = Parser::new("u=2, i".as_bytes());
//!
//! loop {
//!     match p.parse_dict().unwrap() {
//!         None => break,
//!         Some(("u", Value::Integer(v))) if (0i64..=7i64).contains(&v) => urgency = v as i32,
//!         Some(("i", Value::Bool(v))) => incremental = v,
//!         _ => (),
//!     }
//! }
//!
//! println!("urgency={urgency} incremental={incremental}");
//! ```
mod parser;
mod utf8;
mod value;

pub use crate::parser::{Parser, Error};
pub use crate::value::Value;
