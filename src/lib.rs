//! A `#![no_std]`, high-performance parser for HTTP Structured Field
//! Values ([RFC 8941](https://datatracker.ietf.org/doc/html/rfc8941)
//! / [RFC 9651](https://datatracker.ietf.org/doc/html/rfc9651)).
//!
//! Designed for zero-copy and zero-allocation operation, `sfparse`
//! parses input data in-place without allocating dynamic data
//! structures (such as maps, lists, or strings).  It provides
//! minimal, stream-oriented parsing primitives suitable for
//! memory-constrained environments and high-throughput network
//! applications.
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
#![no_std]

mod parser;
mod utf8;
mod value;

pub use crate::parser::{Error, Parser};
pub use crate::value::Value;
