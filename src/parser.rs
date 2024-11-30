use std::fmt;

use crate::utf8;
pub use crate::value::{Key, Value};

pub type Range = std::ops::Range<usize>;
pub type IKey = Range;

pub struct Parser<'a> {
    data: &'a [u8],
    pos: usize,
    state: State,
}

enum Op {
    Before,
    BeforeParams,
    Params,
    After,
}

struct StateSt {
    inner_list: bool,
    op: Op,
}

enum State {
    Initial,
    Dict(StateSt),
    List(StateSt),
    Item(StateSt),
}

impl State {
    fn op(&self) -> &Op {
        match self {
            State::Initial => panic!("unreachable"),
            State::Dict(sst) | State::List(sst) | State::Item(sst) => &sst.op,
        }
    }

    fn state(&self) -> &StateSt {
        match self {
            State::Initial => panic!("unreachable"),
            State::Dict(sst) | State::List(sst) | State::Item(sst) => sst,
        }
    }

    fn set_op(&mut self, new_op: Op) {
        match self {
            State::Initial => panic!("unreachable"),
            State::Dict(sst) | State::List(sst) | State::Item(sst) => {
                sst.op = new_op;
            }
        }
    }

    fn unset_inner_list(&mut self) {
        match self {
            State::Initial => panic!("unreachable"),
            State::Dict(sst) | State::List(sst) | State::Item(sst) => sst.inner_list = false,
        }
    }
}

/// Errors encountered while parsing data as Structured Field values.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// Error encountered while parsing data.  index is the position
    /// in data that caused the error.  index might be the length of
    /// data if it prematurely ends when [Parser] needs more input.
    ParseError { index: usize },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::ParseError { index } => {
                write!(f, "parse error at position {index}")
            }
        }
    }
}

impl std::error::Error for Error {}

/// Parser is [RFC
/// 9651](https://datatracker.ietf.org/doc/html/rfc9651) Structured
/// Field Values parser.  It is designed not to do any extra
/// allocation, like allocating maps, lists, and Strings, and do the
/// minimal stuff to parse the input data.
impl Parser<'_> {
    /// Creates new Parser with the given data.
    pub fn new(data: &[u8]) -> Parser {
        Parser {
            data: data,
            pos: 0,
            state: State::Initial,
        }
    }

    /// Returns the next item.  If there is no parameter left, this
    /// function returns `Ok(None)`.
    ///
    /// ```
    /// use sfparse::Parser;
    ///
    /// let mut p = Parser::new("1235".as_bytes());
    ///
    /// match p.parse_item().unwrap() {
    ///     None => (),
    ///     Some(v) => println!("{v}"),
    /// }
    /// ```
    ///
    /// To get the parameters attached to the item, call
    /// [Parser::parse_param()].
    ///
    /// ```
    /// use sfparse::Parser;
    ///
    /// let mut p = Parser::new("foo;f;g".as_bytes());
    ///
    /// match p.parse_item().unwrap() {
    ///     None => (),
    ///     Some(v) => {
    ///         println!("{v}");
    ///
    ///         loop {
    ///             match p.parse_param().unwrap() {
    ///                 None => break,
    ///                 Some((k, v)) => println!("{k}: {v}"),
    ///             }
    ///         }
    ///     }
    /// }
    /// ```
    ///
    /// To ensure that the data given to [Parser] just contains a
    /// single item, call this method again and verify that it returns
    /// `Ok(None)`.
    pub fn parse_item(&mut self) -> Result<Option<Value>, Error> {
        match &self.state {
            State::Initial => {
                self.discard_sp();

                if self.eof() {
                    return Err(Error::ParseError { index: self.pos });
                }
            }
            State::Item(StateSt {
                inner_list: true,
                op: Op::Before,
            }) => {
                self.skip_inner_list()?;
                self.skip_params()?;
                self.discard_sp();

                if !self.eof() {
                    return Err(Error::ParseError { index: self.pos });
                }

                return Ok(None);
            }
            State::Item(StateSt {
                inner_list: false,
                op: Op::BeforeParams,
            }) => {
                self.skip_params()?;
                self.discard_sp();

                if !self.eof() {
                    return Err(Error::ParseError { index: self.pos });
                }

                return Ok(None);
            }
            State::Item(StateSt {
                inner_list: false,
                op: Op::After,
            }) => {
                self.discard_sp();

                if !self.eof() {
                    return Err(Error::ParseError { index: self.pos });
                }

                return Ok(None);
            }
            _ => panic!("unreachable"),
        }

        if self.data[self.pos] == b'(' {
            self.pos += 1;
            self.state = State::Item(StateSt {
                inner_list: true,
                op: Op::Before,
            });

            return Ok(Some(Value::InnerList));
        }

        let v = self.parse_bare_item()?;

        self.state = State::Item(StateSt {
            inner_list: false,
            op: Op::BeforeParams,
        });

        Ok(Some(v))
    }

    /// Returns the next key and item in a parameter list.  If there
    /// is no parameter left, this function returns `Ok(None)`.
    ///
    /// Application should keep calling this method until it returns
    /// either `Ok(None)` or `Err(Error)`.
    ///
    /// ```
    /// use sfparse::Parser;
    ///
    /// let mut p = Parser::new("a,b;q=0.5".as_bytes());
    ///
    /// loop {
    ///     match p.parse_list().unwrap() {
    ///          None => break,
    ///          Some(v) => {
    ///              println!("{v}");
    ///
    ///              loop {
    ///                  match p.parse_param().unwrap() {
    ///                      None => break,
    ///                      Some((k, v)) => println!("{k}: {v}"),
    ///                  }
    ///              }
    ///          }
    ///     }
    /// }
    /// ```
    pub fn parse_param(&mut self) -> Result<Option<(Key, Value)>, Error> {
        match self.state.op() {
            Op::Before => {
                self.skip_inner_list()?;
                self.state.set_op(Op::Params);
            }
            Op::BeforeParams => self.state.set_op(Op::Params),
            Op::Params => (),
            _ => panic!("unreachable"),
        }

        if self.eof() || self.data[self.pos] != b';' {
            self.state.set_op(Op::After);

            return Ok(None);
        }

        self.pos += 1;
        self.discard_sp();

        if self.eof() {
            return Err(Error::ParseError { index: self.pos });
        }

        let ik = self.parse_key()?;

        if self.eof() || self.data[self.pos] != b'=' {
            return Ok(Some((
                unsafe { std::str::from_utf8_unchecked(&self.data[ik]) },
                Value::Bool(true),
            )));
        }

        self.pos += 1;

        if self.eof() {
            return Err(Error::ParseError { index: self.pos });
        }

        let v = self.parse_bare_item()?;

        Ok(Some((
            unsafe { std::str::from_utf8_unchecked(&self.data[ik]) },
            v,
        )))
    }

    /// Parses the data as dictionary and returns the next key and
    /// item.  If there is no pair left, this function returns
    /// `Ok(None)`.
    ///
    /// Application should keep calling this method until it returns
    /// either `Ok(None)` or `Err(Error)`.
    ///
    /// ```
    /// use sfparse::Parser;
    ///
    /// let mut p = Parser::new(r#"en="Applepie", da=:w4ZibGV0w6ZydGU=:"#.as_bytes());
    ///
    /// loop {
    ///     match p.parse_dict().unwrap() {
    ///          None => break,
    ///          Some((k, v)) => println!("{k}: {v}"),
    ///     }
    /// }
    /// ```
    ///
    /// If [Value::InnerList] is returned, and a caller is interested
    /// in its members, call [Parser::parse_inner_list()].  Otherwise,
    /// calling [Parser::parse_dict] returns the next key/item pair.
    ///
    /// ```
    /// use sfparse::{Parser, Value};
    ///
    /// let mut p = Parser::new("a=(1 2 3)".as_bytes());
    ///
    /// loop {
    ///     match p.parse_dict().unwrap() {
    ///          None => break,
    ///          Some((k, Value::InnerList)) => {
    ///              println!("InnerList");
    ///
    ///              loop {
    ///                  match p.parse_inner_list().unwrap() {
    ///                      None => break,
    ///                      Some(v) => println!("{v}"),
    ///                  }
    ///              }
    ///          }
    ///          Some((k, v)) => println!("{k}: {v}"),
    ///     }
    /// }
    /// ```
    ///
    /// To get the parameters attached to the key/item pair, call
    /// [Parser::parse_param()].
    ///
    /// ```
    /// use sfparse::Parser;
    ///
    /// let mut p = Parser::new("a,b;q=0.5".as_bytes());
    ///
    /// loop {
    ///     match p.parse_dict().unwrap() {
    ///          None => break,
    ///          Some(("b", _)) => {
    ///              loop {
    ///                  match p.parse_param().unwrap() {
    ///                      None => break,
    ///                      Some((k, v)) => println!("{k}: {v}"),
    ///                  }
    ///              }
    ///          }
    ///          _ => (),
    ///     }
    /// }
    /// ```
    ///
    /// This method does no effect to verify the uniqueness of the
    /// key.
    pub fn parse_dict(&mut self) -> Result<Option<(Key, Value)>, Error> {
        match self.state {
            State::Dict(StateSt {
                inner_list: true,
                op: Op::Before,
            }) => {
                self.skip_inner_list()?;
                self.skip_params()?;
                self.next_key_or_item()?;
            }
            State::Dict(StateSt {
                inner_list: false,
                op: Op::BeforeParams,
            }) => {
                self.skip_params()?;
                self.next_key_or_item()?;
            }
            State::Dict(StateSt {
                inner_list: false,
                op: Op::After,
            }) => self.next_key_or_item()?,
            State::Initial => self.discard_sp(),
            _ => panic!("unreachable"),
        }

        if self.eof() {
            return Ok(None);
        }

        let ik = self.parse_key()?;
        let v = self.parse_dict_value()?;

        Ok(Some((
            unsafe { std::str::from_utf8_unchecked(&self.data[ik]) },
            v,
        )))
    }

    /// Parses the data as list and returns the next item.  If there
    /// is no item left, this function returns `Ok(None)`.
    ///
    /// Application should keep calling this method until it returns
    /// either `Ok(None)` or `Err(Error)`.
    ///
    /// ```
    /// use sfparse::Parser;
    ///
    /// let mut p = Parser::new(r#"abc;a=1;b=2; cde_456, (ghi;jk=4 l);q="9";r=w"#.as_bytes());
    ///
    /// loop {
    ///     match p.parse_list().unwrap() {
    ///          None => break,
    ///          Some(v) => println!("{v}"),
    ///     }
    /// }
    /// ```
    ///
    /// If [Value::InnerList] is returned, and a caller is interested
    /// in its members, call [Parser::parse_inner_list()].  Otherwise,
    /// calling [Parser::parse_list] returns the next item.
    ///
    /// ```
    /// use sfparse::{Parser, Value};
    ///
    /// let mut p = Parser::new("(1 2 3);f, foo".as_bytes());
    ///
    /// loop {
    ///     match p.parse_list().unwrap() {
    ///          None => break,
    ///          Some(Value::InnerList) => {
    ///              println!("InnerList");
    ///
    ///              loop {
    ///                  match p.parse_inner_list().unwrap() {
    ///                      None => break,
    ///                      Some(v) => println!("{v}"),
    ///                  }
    ///              }
    ///          }
    ///          Some(v) => println!("{v}"),
    ///     }
    /// }
    /// ```
    ///
    /// To get the parameters attached to the item, call
    /// [Parser::parse_param()].
    ///
    /// ```
    /// use sfparse::Parser;
    ///
    /// let mut p = Parser::new("a,b;q=0.5".as_bytes());
    ///
    /// loop {
    ///     match p.parse_list().unwrap() {
    ///          None => break,
    ///          Some(v) => {
    ///              println!("{v}");
    ///
    ///              loop {
    ///                  match p.parse_param().unwrap() {
    ///                      None => break,
    ///                      Some((k, v)) => println!("{k}: {v}"),
    ///                  }
    ///              }
    ///          }
    ///     }
    /// }
    /// ```
    pub fn parse_list(&mut self) -> Result<Option<Value>, Error> {
        match self.state {
            State::List(StateSt {
                inner_list: true,
                op: Op::Before,
            }) => {
                self.skip_inner_list()?;
                self.skip_params()?;
                self.next_key_or_item()?;
            }
            State::List(StateSt {
                inner_list: false,
                op: Op::BeforeParams,
            }) => {
                self.skip_params()?;
                self.next_key_or_item()?;
            }
            State::List(StateSt {
                inner_list: false,
                op: Op::After,
            }) => self.next_key_or_item()?,
            State::Initial => self.discard_sp(),
            _ => panic!("unreachable"),
        }

        if self.eof() {
            return Ok(None);
        }

        if self.data[self.pos] == b'(' {
            self.pos += 1;
            self.state = State::List(StateSt {
                inner_list: true,
                op: Op::Before,
            });

            return Ok(Some(Value::InnerList));
        }

        let v = self.parse_bare_item()?;

        self.state = State::List(StateSt {
            inner_list: false,
            op: Op::BeforeParams,
        });

        Ok(Some(v))
    }

    /// Returns the next item in an inner list.  If there is no item
    /// left, this function returns `Ok(None)`.
    ///
    /// Application should keep calling this method until it returns
    /// either `Ok(None)` or `Err(Error)`.
    ///
    /// ```
    /// use sfparse::{Parser, Value};
    ///
    /// let mut p = Parser::new("(1 2 3);f, foo".as_bytes());
    ///
    /// loop {
    ///     match p.parse_list() {
    ///          Ok(None) => break,
    ///          Ok(Some(Value::InnerList)) => {
    ///              println!("InnerList");
    ///
    ///              loop {
    ///                  match p.parse_inner_list() {
    ///                      Ok(None) => break,
    ///                      Ok(Some(v)) => println!("{v}"),
    ///                      Err(err) => panic!("{err}"),
    ///                  }
    ///              }
    ///          }
    ///          Ok(Some(v)) => println!("{v}"),
    ///          Err(err) => panic!("{err}"),
    ///     }
    /// }
    /// ```
    ///
    /// To get the parameters attached to the item, call
    /// [Parser::parse_param()].
    ///
    /// ```
    /// use sfparse::{Parser, Value};
    ///
    /// let mut p = Parser::new("(1 2 3);f, foo".as_bytes());
    ///
    /// loop {
    ///     match p.parse_list() {
    ///          Ok(None) => break,
    ///          Ok(Some(Value::InnerList)) => {
    ///              println!("InnerList");
    ///
    ///              loop {
    ///                  match p.parse_inner_list() {
    ///                      Ok(None) => break,
    ///                      Ok(Some(v)) => {
    ///                          println!("{v}");
    ///
    ///                          loop {
    ///                              match p.parse_param() {
    ///                                  Ok(None) => break,
    ///                                  Ok(Some((k, v))) => println!("{k}: {v}"),
    ///                                  Err(err) => panic!("{err}"),
    ///                              }
    ///                          }
    ///                      }
    ///                      Err(err) => panic!("{err}"),
    ///                  }
    ///              }
    ///          }
    ///          Ok(Some(v)) => println!("{v}"),
    ///          Err(err) => panic!("{err}"),
    ///     }
    /// }
    /// ```
    ///
    pub fn parse_inner_list(&mut self) -> Result<Option<Value>, Error> {
        match self.state.state() {
            StateSt {
                inner_list: true,
                op: Op::Before,
            } => {
                self.discard_sp();
                if self.eof() {
                    return Err(Error::ParseError { index: self.pos });
                }
            }
            StateSt {
                inner_list: true,
                op: Op::BeforeParams,
            } => {
                self.skip_params()?;
                self.parse_inner_list_after()?;
            }
            StateSt {
                inner_list: true,
                op: Op::After,
            } => self.parse_inner_list_after()?,
            _ => panic!("unreachable"),
        }

        if self.data[self.pos] == b')' {
            self.pos += 1;
            self.state.unset_inner_list();
            self.state.set_op(Op::BeforeParams);

            return Ok(None);
        }

        let v = self.parse_bare_item()?;

        self.state.set_op(Op::BeforeParams);

        Ok(Some(v))
    }
}

impl Parser<'_> {
    fn discard_sp(&mut self) {
        match self.data[self.pos..].iter().position(|&x| x != b' ') {
            Some(pos) => self.pos += pos,
            None => self.pos = self.data.len(),
        }
    }

    fn discard_ows(&mut self) {
        match self.data[self.pos..]
            .iter()
            .position(|&x| x != b' ' && x != b'\t')
        {
            Some(pos) => self.pos += pos,
            None => self.pos = self.data.len(),
        }
    }

    fn skip_inner_list(&mut self) -> Result<(), Error> {
        loop {
            match self.parse_inner_list() {
                Ok(None) => return Ok(()),
                Ok(_) => (),
                Err(err) => return Err(err),
            }
        }
    }

    fn skip_params(&mut self) -> Result<(), Error> {
        loop {
            let Some(_) = self.parse_param()? else {
                return Ok(());
            };
        }
    }

    fn eof(&self) -> bool {
        self.pos == self.data.len()
    }

    fn next_key_or_item(&mut self) -> Result<(), Error> {
        self.discard_ows();

        if self.eof() {
            return Ok(());
        }

        if self.data[self.pos] != b',' {
            return Err(Error::ParseError { index: self.pos });
        }

        self.pos += 1;
        self.discard_ows();

        if self.eof() {
            return Err(Error::ParseError { index: self.pos });
        }

        Ok(())
    }

    fn parse_key(&mut self) -> Result<IKey, Error> {
        match self.data[self.pos] {
            b'*' | b'a'..=b'z' => (),
            _ => return Err(Error::ParseError { index: self.pos }),
        }

        let base = self.pos;
        self.pos += 1;

        match self.data[self.pos..].iter().position(|&x| match x {
            b'_' | b'-' | b'.' | b'*' | b'0'..=b'9' | b'a'..=b'z' => false,
            _ => true,
        }) {
            Some(pos) => self.pos += pos,
            None => self.pos = self.data.len(),
        }

        Ok(IKey {
            start: base,
            end: self.pos,
        })
    }

    fn parse_dict_value(&mut self) -> Result<Value, Error> {
        if self.eof() || self.data[self.pos] != b'=' {
            self.state = State::Dict(StateSt {
                inner_list: false,
                op: Op::BeforeParams,
            });

            return Ok(Value::Bool(true));
        }

        self.pos += 1;

        if self.eof() {
            return Err(Error::ParseError { index: self.pos });
        }

        if self.data[self.pos] == b'(' {
            self.pos += 1;
            self.state = State::Dict(StateSt {
                inner_list: true,
                op: Op::Before,
            });

            return Ok(Value::InnerList);
        }

        let v = self.parse_bare_item()?;

        self.state = State::Dict(StateSt {
            inner_list: false,
            op: Op::BeforeParams,
        });

        Ok(v)
    }

    fn parse_bare_item(&mut self) -> Result<Value, Error> {
        match self.data[self.pos] {
            b'"' => self.parse_string(),
            b'-' | b'0'..=b'9' => self.parse_number(),
            b'@' => self.parse_date(),
            b':' => self.parse_byteseq(),
            b'?' => self.parse_boolean(),
            b'*' | b'a'..=b'z' | b'A'..=b'Z' => self.parse_token(),
            b'%' => self.parse_dispstring(),
            _ => Err(Error::ParseError { index: self.pos }),
        }
    }

    fn parse_string(&mut self) -> Result<Value, Error> {
        self.pos += 1;
        let base = self.pos;
        let mut escape = false;

        while !self.eof() {
            match self.data[self.pos] {
                0x20..=0x21 | 0x23..=0x5b | 0x5d..=0x7e => (),
                b'\\' => {
                    self.pos += 1;

                    if self.eof() {
                        return Err(Error::ParseError { index: self.pos });
                    }

                    match self.data[self.pos] {
                        b'"' | b'\\' => escape = true,
                        _ => return Err(Error::ParseError { index: self.pos }),
                    };
                }
                b'"' => {
                    let end = self.pos;
                    self.pos += 1;

                    return Ok(Value::String {
                        range: Range {
                            start: base,
                            end: end,
                        },
                        escape: escape,
                    });
                }
                _ => return Err(Error::ParseError { index: self.pos }),
            }

            self.pos += 1;
        }

        Err(Error::ParseError { index: self.pos })
    }

    fn parse_number(&mut self) -> Result<Value, Error> {
        let mut sign = 1;
        let mut value: i64 = 0;
        let mut len = 0;

        if self.data[self.pos] == b'-' {
            self.pos += 1;

            if self.eof() {
                return Err(Error::ParseError { index: self.pos });
            }

            sign = -1;
        }

        for c in &self.data[self.pos..] {
            match c {
                b'0'..=b'9' => {
                    len += 1;
                    if len > 15 {
                        return Err(Error::ParseError { index: self.pos });
                    }

                    value *= 10;
                    value += (c - b'0') as i64;
                }
                _ => break,
            }

            self.pos += 1;
        }

        if len == 0 {
            return Err(Error::ParseError { index: self.pos });
        }

        if self.eof() || self.data[self.pos] != b'.' {
            return Ok(Value::Integer(value * sign));
        }

        // decimal

        if len > 12 {
            return Err(Error::ParseError { index: self.pos });
        }

        let fpos = len;
        self.pos += 1;

        for c in &self.data[self.pos..] {
            match c {
                b'0'..=b'9' => {
                    len += 1;
                    if len > 15 || len - fpos > 3 {
                        return Err(Error::ParseError { index: self.pos });
                    }

                    value *= 10;
                    value += (c - b'0') as i64;
                }
                _ => break,
            }

            self.pos += 1;
        }

        if fpos == len {
            return Err(Error::ParseError { index: self.pos });
        }

        Ok(Value::Decimal {
            numer: value * sign,
            denom: 10i64.pow(len - fpos),
        })
    }

    fn parse_date(&mut self) -> Result<Value, Error> {
        self.pos += 1;

        if self.eof() {
            return Err(Error::ParseError { index: self.pos });
        }

        let v = self.parse_number()?;
        if let Value::Integer(n) = v {
            return Ok(Value::Date(n));
        }

        Err(Error::ParseError { index: self.pos })
    }

    fn parse_byteseq(&mut self) -> Result<Value, Error> {
        self.pos += 1;
        let base = self.pos;

        for b in &self.data[self.pos..] {
            match b {
                b'+' | b'/' | b'0'..=b'9' | b'A'..=b'Z' | b'a'..=b'z' => (),
                b'=' => {
                    match (self.pos - base) & 0x3 {
                        0 | 1 => return Err(Error::ParseError { index: self.pos }),
                        2 => {
                            self.pos += 1;

                            if self.eof() {
                                return Err(Error::ParseError { index: self.pos });
                            }

                            if self.data[self.pos] == b'=' {
                                self.pos += 1;
                            }
                        }
                        3 => self.pos += 1,
                        _ => panic!("unreachable"),
                    }

                    if self.eof() || self.data[self.pos] != b':' {
                        return Err(Error::ParseError { index: self.pos });
                    }

                    let end = self.pos;
                    self.pos += 1;

                    return Ok(Value::ByteSeq(Range {
                        start: base,
                        end: end,
                    }));
                }
                b':' => {
                    if (self.pos - base) & 0x3 == 1 {
                        return Err(Error::ParseError { index: self.pos });
                    }

                    let end = self.pos;
                    self.pos += 1;

                    return Ok(Value::ByteSeq(Range {
                        start: base,
                        end: end,
                    }));
                }
                _ => return Err(Error::ParseError { index: self.pos }),
            };

            self.pos += 1;
        }

        Err(Error::ParseError { index: self.pos })
    }

    fn parse_boolean(&mut self) -> Result<Value, Error> {
        self.pos += 1;

        if self.eof() {
            return Err(Error::ParseError { index: self.pos });
        }

        let b = match self.data[self.pos] {
            b'0' => Ok(false),
            b'1' => Ok(true),
            _ => Err(Error::ParseError { index: self.pos }),
        }?;

        self.pos += 1;

        Ok(Value::Bool(b))
    }

    fn parse_token(&mut self) -> Result<Value, Error> {
        let base = self.pos;

        self.pos += 1;

        match self.data[self.pos..].iter().position(|&x| match x {
            b'!'
            | b'#'
            | b'$'
            | b'%'
            | b'&'
            | b'\''
            | b'*'
            | b'+'
            | b'-'
            | b'.'
            | b'/'
            | b'0'..=b'9'
            | b':'
            | b'A'..=b'Z'
            | b'^'
            | b'_'
            | b'`'
            | b'a'..=b'z'
            | b'|'
            | b'~' => false,
            _ => true,
        }) {
            Some(pos) => self.pos += pos,
            None => self.pos = self.data.len(),
        }

        Ok(Value::Token(Range {
            start: base,
            end: self.pos,
        }))
    }

    fn parse_dispstring(&mut self) -> Result<Value, Error> {
        self.pos += 1;

        if self.eof() || self.data[self.pos] != b'"' {
            return Err(Error::ParseError { index: self.pos });
        }

        self.pos += 1;
        let base = self.pos;
        let mut utf8_state: u32 = utf8::ACCEPT;

        while !self.eof() {
            match self.data[self.pos] {
                0x00..=0x1f | 0x7f..=0xff => return Err(Error::ParseError { index: self.pos }),
                b'%' => {
                    self.pos += 1;

                    if self.pos + 2 > self.data.len() {
                        return Err(Error::ParseError { index: self.pos });
                    }

                    let d = match pctdecode(&self.data[self.pos..]) {
                        Err(PCTDecodeError { index }) => Err(Error::ParseError {
                            index: self.pos + index,
                        }),
                        Ok(x) => Ok(x),
                    }?;

                    utf8_state = utf8::decode(utf8_state, d);
                    if utf8_state == utf8::REJECT {
                        return Err(Error::ParseError { index: self.pos });
                    }

                    self.pos += 2;
                }
                b'"' => {
                    if utf8_state != utf8::ACCEPT {
                        return Err(Error::ParseError { index: self.pos });
                    }

                    let end = self.pos;
                    self.pos += 1;

                    return Ok(Value::DispString(Range {
                        start: base,
                        end: end,
                    }));
                }
                _ => {
                    if utf8_state != utf8::ACCEPT {
                        return Err(Error::ParseError { index: self.pos });
                    }

                    self.pos += 1;
                }
            }
        }

        Err(Error::ParseError { index: self.pos })
    }

    fn parse_inner_list_after(&mut self) -> Result<(), Error> {
        if self.eof() {
            return Err(Error::ParseError { index: self.pos });
        }

        match self.data[self.pos] {
            b' ' => {
                self.discard_sp();
                if self.eof() {
                    return Err(Error::ParseError { index: self.pos });
                }
            }
            b')' => (),
            _ => return Err(Error::ParseError { index: self.pos }),
        }

        Ok(())
    }
}

struct PCTDecodeError {
    index: usize,
}

fn pctdecode(data: &[u8]) -> Result<u8, PCTDecodeError> {
    let mut c = 0;

    for i in 0..2 {
        c <<= 4;

        let x = data[i];
        c |= match x {
            b'0'..=b'9' => Ok(x - b'0'),
            b'a'..=b'f' => Ok(x - b'a' + 10),
            _ => Err(PCTDecodeError { index: i }),
        }?;
    }

    Ok(c)
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestCase<'a> {
        name: &'a str,
        input: &'a str,
        expect: Result<Option<Value>, Error>,
    }

    impl TestCase<'_> {
        fn verify(&self) {
            let mut p = Parser::new(self.input.as_bytes());

            assert_eq!(self.expect, p.parse_item(), "{}", self.name);

            if let Err(_) = self.expect {
                return;
            }

            assert_eq!(Ok(None), p.parse_item(), "{}", self.name);
        }
    }

    #[test]
    fn parse_byteseq() {
        [
            TestCase {
                name: "basic binary",
                input: ":aGVsbG8=:",
                expect: Ok(Some(Value::ByteSeq(1..9))),
            },
            TestCase {
                name: "empty binary",
                input: "::",
                expect: Ok(Some(Value::ByteSeq(1..1))),
            },
            TestCase {
                name: "bad paddding",
                input: ":aGVsbG8:",
                expect: Ok(Some(Value::ByteSeq(1..8))),
            },
            TestCase {
                name: "bad end delimiter",
                input: ":aGVsbG8=",
                expect: Err(Error::ParseError { index: 9 }),
            },
            TestCase {
                name: "extra whitespace",
                input: ":aGVsb G8=:",
                expect: Err(Error::ParseError { index: 6 }),
            },
            TestCase {
                name: "extra chars",
                input: ":aGVsbG!8=:",
                expect: Err(Error::ParseError { index: 7 }),
            },
            TestCase {
                name: "suffix chars",
                input: ":aGVsbG8=!:",
                expect: Err(Error::ParseError { index: 9 }),
            },
            TestCase {
                name: "non-zero pad bits",
                input: ":iZ==:",
                expect: Ok(Some(Value::ByteSeq(1..5))),
            },
            TestCase {
                name: "non-ASCII binary",
                input: ":/+Ah:",
                expect: Ok(Some(Value::ByteSeq(1..5))),
            },
            TestCase {
                name: "base64url binary",
                input: ":_-Ah:",
                expect: Err(Error::ParseError { index: 1 }),
            },
            // Additional tests
            TestCase {
                name: "missing closing colon",
                input: ":1jk=",
                expect: Err(Error::ParseError { index: 5 }),
            },
            TestCase {
                name: "just ':'",
                input: ":",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "single '='",
                input: ":=:",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "two '='",
                input: ":==:",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "three '='",
                input: ":===:",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "four '='",
                input: ":====:",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "single letter never be a base64 encoded string",
                input: ":K:",
                expect: Err(Error::ParseError { index: 2 }),
            },
            TestCase {
                name: "omitting all padding and non-zero pad bits",
                input: ":K7:",
                expect: Ok(Some(Value::ByteSeq(1..3))),
            },
            TestCase {
                name: "omitting a single padding and non-zero pad bits",
                input: ":K7=:",
                expect: Ok(Some(Value::ByteSeq(1..4))),
            },
            TestCase {
                name: "omitting a padding and non-zero pad bits",
                input: ":K73:",
                expect: Ok(Some(Value::ByteSeq(1..4))),
            },
            TestCase {
                name: "not omitting a padding but non-zero pad bits",
                input: ":K73=:",
                expect: Ok(Some(Value::ByteSeq(1..5))),
            },
            TestCase {
                name: "padding in the middle of encoded string",
                input: ":ab=a:",
                expect: Err(Error::ParseError { index: 4 }),
            },
        ]
        .iter()
        .for_each(|t| t.verify());
    }

    #[test]
    fn parse_token() {
        [
            TestCase {
                name: "basic token - item",
                input: "a_b-c.d3:f%00/*",
                expect: Ok(Some(Value::Token(Range { start: 0, end: 15 }))),
            },
            TestCase {
                name: "token with capitals - item",
                input: "fooBar",
                expect: Ok(Some(Value::Token(Range { start: 0, end: 6 }))),
            },
            TestCase {
                name: "token starting with capitals - item",
                input: "FooBar",
                expect: Ok(Some(Value::Token(Range { start: 0, end: 6 }))),
            },
        ]
        .iter()
        .for_each(|t| t.verify())
    }

    #[test]
    fn parse_dispstring() {
        [
            TestCase {
                name: "basic display string (ascii content)",
                input: r#"%"foo bar""#,
                expect: Ok(Some(Value::DispString(2..9))),
            },
            TestCase {
                name: "all printable ascii",
                input: "%\" !%22#$%25&'()*+,-./0123456789:;<=>?@\
                        ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`\
                        abcdefghijklmnopqrstuvwxyz{|}~\"",
                expect: Ok(Some(Value::DispString(2..101))),
            },
            TestCase {
                name: "non-ascii display string (uppercase escaping)",
                input: r#"%"f%C3%BC%C3%BC""#,
                expect: Err(Error::ParseError { index: 4 }),
            },
            TestCase {
                name: "non-ascii display string (lowercase escaping)",
                input: r#"%"f%c3%bc%c3%bc""#,
                expect: Ok(Some(Value::DispString(2..15))),
            },
            TestCase {
                name: "tab in display string",
                input: "%\"\t\"",
                expect: Err(Error::ParseError { index: 2 }),
            },
            TestCase {
                name: "newline in display string",
                input: "%\"\n\"",
                expect: Err(Error::ParseError { index: 2 }),
            },
            TestCase {
                name: "single quoted display string",
                input: "%'foo'",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "unquoted display string",
                input: "%foo",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "display string missing initial quote",
                input: r#"%foo""#,
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "unbalanced display string",
                input: r#"%"foo"#,
                expect: Err(Error::ParseError { index: 5 }),
            },
            TestCase {
                name: "display string quoting",
                input: r#"%"foo %22bar%22 \ baz""#,
                expect: Ok(Some(Value::DispString(2..21))),
            },
            TestCase {
                name: "bad display string escaping",
                input: r#"%"foo %a"#,
                expect: Err(Error::ParseError { index: 7 }),
            },
            TestCase {
                name: "bad display string utf-8 (invalid 2-byte seq)",
                input: r#"%"%c3%28""#,
                expect: Err(Error::ParseError { index: 6 }),
            },
            TestCase {
                name: "bad display string utf-8 (invalid sequence id)",
                input: r#"%"%a0%a1""#,
                expect: Err(Error::ParseError { index: 3 }),
            },
            TestCase {
                name: "bad display string utf-8 (invalid hex)",
                input: r#"%"%g0%1w""#,
                expect: Err(Error::ParseError { index: 3 }),
            },
            TestCase {
                name: "bad display string utf-8 (invalid 3-byte seq)",
                input: r#"%"%e2%28%a1""#,
                expect: Err(Error::ParseError { index: 6 }),
            },
            TestCase {
                name: "bad display string utf-8 (invalid 4-byte seq)",
                input: r#"%"%f0%28%8c%28""#,
                expect: Err(Error::ParseError { index: 6 }),
            },
            TestCase {
                name: "BOM in display string",
                input: r#"%"BOM: %ef%bb%bf""#,
                expect: Ok(Some(Value::DispString(2..16))),
            },
        ]
        .iter()
        .for_each(|t| t.verify());
    }

    #[test]
    fn parse_boolean() {
        [
            TestCase {
                name: "basic true boolean",
                input: "?1",
                expect: Ok(Some(Value::Bool(true))),
            },
            TestCase {
                name: "basic false boolean",
                input: "?0",
                expect: Ok(Some(Value::Bool(false))),
            },
            TestCase {
                name: "unknown boolean",
                input: "?Q",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "whitespace boolean",
                input: "? 1",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "negative zero boolean",
                input: "?-0",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "T boolean",
                input: "?T",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "F boolean",
                input: "?F",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "t boolean",
                input: "?t",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "f boolean",
                input: "?f",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "spelled-out True boolean",
                input: "?True",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "spelled-out False boolean",
                input: "?False",
                expect: Err(Error::ParseError { index: 1 }),
            },
            // Additional tests
            TestCase {
                name: "Just '?'",
                input: "?",
                expect: Err(Error::ParseError { index: 1 }),
            },
        ]
        .iter()
        .for_each(|t| t.verify());
    }

    #[test]
    fn parse_string() {
        [
            TestCase {
                name: "basic string",
                input: r#""foo bar""#,
                expect: Ok(Some(Value::String {
                    range: 1..8,
                    escape: false,
                })),
            },
            TestCase {
                name: "empty string",
                input: r#""""#,
                expect: Ok(Some(Value::String {
                    range: 1..1,
                    escape: false,
                })),
            },
            TestCase {
                name: "long string",
                input: "\"foo foo foo foo foo foo foo foo foo foo foo foo foo \
                        foo foo foo foo foo foo foo foo foo foo foo foo foo \
                        foo foo foo foo foo foo foo foo foo foo foo foo foo \
                        foo foo foo foo foo foo foo foo foo foo foo foo foo \
                        foo foo foo foo foo foo foo foo foo foo foo foo foo \"",
                expect: Ok(Some(Value::String {
                    range: 1..261,
                    escape: false,
                })),
            },
            TestCase {
                name: "whitespace string",
                input: r#""   ""#,
                expect: Ok(Some(Value::String {
                    range: 1..4,
                    escape: false,
                })),
            },
            TestCase {
                name: "non-ascii string",
                input: r#""füü""#,
                expect: Err(Error::ParseError { index: 2 }),
            },
            TestCase {
                name: "tab in string",
                input: "\"\\t\"",
                expect: Err(Error::ParseError { index: 2 }),
            },
            TestCase {
                name: "newline in string",
                input: "\" \\n \"",
                expect: Err(Error::ParseError { index: 3 }),
            },
            TestCase {
                name: "single quoted string",
                input: "'foo'",
                expect: Err(Error::ParseError { index: 0 }),
            },
            TestCase {
                name: "unbalanced string",
                input: r#""foo"#,
                expect: Err(Error::ParseError { index: 4 }),
            },
            TestCase {
                name: "string quoting",
                input: r#""foo \"bar\" \\ baz""#,
                expect: Ok(Some(Value::String {
                    range: 1..19,
                    escape: true,
                })),
            },
            TestCase {
                name: "bad string quoting",
                input: r#""foo \,""#,
                expect: Err(Error::ParseError { index: 6 }),
            },
            TestCase {
                name: "ending string quote",
                input: r#""foo \""#,
                expect: Err(Error::ParseError { index: 7 }),
            },
            TestCase {
                name: "abruptly ending string quote",
                input: r#""foo \"#,
                expect: Err(Error::ParseError { index: 6 }),
            },
            // Additional tests
            TestCase {
                name: r#"Just '"'"#,
                input: r#"""#,
                expect: Err(Error::ParseError { index: 1 }),
            },
        ]
        .iter()
        .for_each(|t| t.verify());
    }

    #[test]
    fn parse_number() {
        [
            TestCase {
                name: "basic integer",
                input: "42",
                expect: Ok(Some(Value::Integer(42))),
            },
            TestCase {
                name: "zero integer",
                input: "0",
                expect: Ok(Some(Value::Integer(0))),
            },
            TestCase {
                name: "negative zero",
                input: "-0",
                expect: Ok(Some(Value::Integer(0))),
            },
            TestCase {
                name: "double negative zero",
                input: "--0",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "negative integer",
                input: "-42",
                expect: Ok(Some(Value::Integer(-42))),
            },
            TestCase {
                name: "leading 0 integer",
                input: "042",
                expect: Ok(Some(Value::Integer(42))),
            },
            TestCase {
                name: "leading 0 negative integer",
                input: "-042",
                expect: Ok(Some(Value::Integer(-42))),
            },
            TestCase {
                name: "leading 0 zero",
                input: "00",
                expect: Ok(Some(Value::Integer(0))),
            },
            // Skip "comma" because this test case cannot handle it.
            TestCase {
                name: "negative non-DIGIT first character",
                input: "-a23",
                expect: Err(Error::ParseError { index: 1 }),
            },
            // Skip "sign out of place" because this test case cannot
            // handle it.
            TestCase {
                name: "whitespace after sign",
                input: "- 42",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "long integer",
                input: "123456789012345",
                expect: Ok(Some(Value::Integer(123456789012345))),
            },
            TestCase {
                name: "long negative integer",
                input: "-123456789012345",
                expect: Ok(Some(Value::Integer(-123456789012345))),
            },
            TestCase {
                name: "too long integer",
                input: "1234567890123456",
                expect: Err(Error::ParseError { index: 15 }),
            },
            TestCase {
                name: "negative too long integer",
                input: "-1234567890123456",
                expect: Err(Error::ParseError { index: 16 }),
            },
            TestCase {
                name: "simple decimal",
                input: "1.23",
                expect: Ok(Some(Value::Decimal {
                    numer: 123,
                    denom: 100,
                })),
            },
            TestCase {
                name: "negative decimal",
                input: "-1.23",
                expect: Ok(Some(Value::Decimal {
                    numer: -123,
                    denom: 100,
                })),
            },
            TestCase {
                name: "decimal, whitespace after decimal",
                input: "1. 23",
                expect: Err(Error::ParseError { index: 2 }),
            },
            // Skip "decimal, whitespace before decimal" because this
            // test case cannot handle it.
            TestCase {
                name: "negative decimal, whitespace after sign",
                input: "- 1.23",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "tricky precision decimal",
                input: "123456789012.1",
                expect: Ok(Some(Value::Decimal {
                    numer: 1234567890121,
                    denom: 10,
                })),
            },
            // Skip "double decimal decimal" because this test case
            // cannot handle it.
            TestCase {
                name: "adjacent double decimal decimal",
                input: "1..4",
                expect: Err(Error::ParseError { index: 2 }),
            },
            TestCase {
                name: "decimal with three fractional digits",
                input: "1.123",
                expect: Ok(Some(Value::Decimal {
                    numer: 1123,
                    denom: 1000,
                })),
            },
            TestCase {
                name: "negative decimal with three fractional digits",
                input: "-1.123",
                expect: Ok(Some(Value::Decimal {
                    numer: -1123,
                    denom: 1000,
                })),
            },
            TestCase {
                name: "decimal with four fractional digits",
                input: "1.1234",
                expect: Err(Error::ParseError { index: 5 }),
            },
            TestCase {
                name: "negative decimal with four fractional digits",
                input: "-1.1234",
                expect: Err(Error::ParseError { index: 6 }),
            },
            TestCase {
                name: "decimal with thirteen integer digits",
                input: "1234567890123.0",
                expect: Err(Error::ParseError { index: 13 }),
            },
            TestCase {
                name: "negative decimal with thirteen integer digits",
                input: "-1234567890123.0",
                expect: Err(Error::ParseError { index: 14 }),
            },
            // generated
            TestCase {
                name: "too many digit 0 decimal",
                input: "000000000000000.0",
                expect: Err(Error::ParseError { index: 15 }),
            },
            TestCase {
                name: "too many fractional digits 0 decimal",
                input: "000000000000.0000",
                expect: Err(Error::ParseError { index: 16 }),
            },
            TestCase {
                name: "too many digit 9 decimal",
                input: "999999999999999.9",
                expect: Err(Error::ParseError { index: 15 }),
            },
            TestCase {
                name: "too many fractional digits 9 decimal",
                input: "999999999999.9999",
                expect: Err(Error::ParseError { index: 16 }),
            },
            // Additional tests
            TestCase {
                name: "no digits",
                input: "-a",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "no digits before '.'",
                input: "-.1",
                expect: Err(Error::ParseError { index: 1 }),
            },
        ]
        .iter()
        .for_each(|t| t.verify());
    }

    #[test]
    fn parse_date() {
        [
            TestCase {
                name: "date - 1970-01-01 00:00:00",
                input: "@0",
                expect: Ok(Some(Value::Date(0))),
            },
            TestCase {
                name: "date - 2022-08-04 01:57:13",
                input: "@1659578233",
                expect: Ok(Some(Value::Date(1659578233))),
            },
            TestCase {
                name: "date - 1917-05-30 22:02:47",
                input: "@-1659578233",
                expect: Ok(Some(Value::Date(-1659578233))),
            },
            TestCase {
                name: "date - 2^31",
                input: "@2147483648",
                expect: Ok(Some(Value::Date(2147483648))),
            },
            TestCase {
                name: "date - 2^32",
                input: "@4294967296",
                expect: Ok(Some(Value::Date(4294967296))),
            },
            TestCase {
                name: "date - decimal",
                input: "@1659578233.12",
                expect: Err(Error::ParseError { index: 14 }),
            },
            // Additional tests
            TestCase {
                name: "just '@'",
                input: "@",
                expect: Err(Error::ParseError { index: 1 }),
            },
        ]
        .iter()
        .for_each(|t| t.verify());
    }

    #[derive(Debug, PartialEq)]
    pub enum TValue<'a> {
        InnerList(Vec<(TValue<'a>, Vec<(String, TValue<'a>)>)>),
        String { str: &'a str, escape: bool },
        Token(&'a str),
        Integer(i64),
        Decimal { numer: i64, denom: i64 },
        Date(i64),
        ByteSeq(&'a str),
        Bool(bool),
        DispString(&'a str),
    }

    impl TValue<'_> {
        fn from_value(v: Value, s: &str) -> TValue {
            match v {
                Value::String { range, escape } => TValue::String {
                    str: &s[range],
                    escape: escape,
                },
                Value::Token(range) => TValue::Token(&s[range]),
                Value::Integer(n) => TValue::Integer(n),
                Value::Decimal { numer, denom } => TValue::Decimal {
                    numer: numer,
                    denom: denom,
                },
                Value::Date(n) => TValue::Date(n),
                Value::ByteSeq(range) => TValue::ByteSeq(&s[range]),
                Value::Bool(v) => TValue::Bool(v),
                Value::DispString(range) => TValue::DispString(&s[range]),
                _ => panic!(""),
            }
        }
    }

    fn parse_params<'a>(p: &mut Parser, data: &'a str) -> Result<Vec<(String, TValue<'a>)>, Error> {
        let mut params = Vec::new();

        loop {
            match p.parse_param() {
                Ok(None) => break,
                Ok(Some((k, v))) => {
                    let k = String::from(k);
                    params.push((k, TValue::from_value(v, data)));
                }
                Err(err) => return Err(err),
            }
        }

        Ok(params)
    }

    fn parse_inner_list<'a>(p: &mut Parser, data: &'a str) -> Result<TValue<'a>, Error> {
        let mut l = Vec::new();

        loop {
            match p.parse_inner_list() {
                Ok(None) => break,
                Ok(Some(v)) => {
                    let params = parse_params(p, data)?;

                    l.push((TValue::from_value(v, data), params))
                }
                Err(err) => return Err(err),
            }
        }

        Ok(TValue::InnerList(l))
    }

    #[test]
    fn parse_dict() {
        struct TestCase<'a> {
            name: &'a str,
            input: &'a str,
            expect: Result<Vec<(String, TValue<'a>, Vec<(String, TValue<'a>)>)>, Error>,
        }

        [
            TestCase {
                name: "basic dictionary",
                input: r#"en="Applepie", da=:w4ZibGV0w6ZydGUK:"#,
                expect: Ok(vec![
                    (
                        String::from("en"),
                        TValue::String {
                            str: "Applepie",
                            escape: false,
                        },
                        vec![],
                    ),
                    (
                        String::from("da"),
                        TValue::ByteSeq("w4ZibGV0w6ZydGUK"),
                        vec![],
                    ),
                ]),
            },
            TestCase {
                name: "empty dictionary",
                input: "",
                expect: Ok(vec![]),
            },
            TestCase {
                name: "single item dictionary",
                input: "a=1",
                expect: Ok(vec![(String::from("a"), TValue::Integer(1), vec![])]),
            },
            TestCase {
                name: "list item dictionary",
                input: "a=(1 2)",
                expect: Ok(vec![(
                    String::from("a"),
                    TValue::InnerList(vec![
                        (TValue::Integer(1), vec![]),
                        (TValue::Integer(2), vec![]),
                    ]),
                    vec![],
                )]),
            },
            TestCase {
                name: "single list item dictionary",
                input: "a=(1)",
                expect: Ok(vec![(
                    String::from("a"),
                    TValue::InnerList(vec![(TValue::Integer(1), vec![])]),
                    vec![],
                )]),
            },
            TestCase {
                name: "empty list item dictionary",
                input: "a=()",
                expect: Ok(vec![(String::from("a"), TValue::InnerList(vec![]), vec![])]),
            },
            TestCase {
                name: "no whitespace dictionary",
                input: "a=1,b=2",
                expect: Ok(vec![
                    (String::from("a"), TValue::Integer(1), vec![]),
                    (String::from("b"), TValue::Integer(2), vec![]),
                ]),
            },
            TestCase {
                name: "extra whitespace dictionary",
                input: "a=1 ,  b=2",
                expect: Ok(vec![
                    (String::from("a"), TValue::Integer(1), vec![]),
                    (String::from("b"), TValue::Integer(2), vec![]),
                ]),
            },
            TestCase {
                name: "tab separated dictionary",
                input: "a=1\t,\tb=2",
                expect: Ok(vec![
                    (String::from("a"), TValue::Integer(1), vec![]),
                    (String::from("b"), TValue::Integer(2), vec![]),
                ]),
            },
            TestCase {
                name: "leading whitespace dictionary",
                input: "     a=1 ,  b=2",
                expect: Ok(vec![
                    (String::from("a"), TValue::Integer(1), vec![]),
                    (String::from("b"), TValue::Integer(2), vec![]),
                ]),
            },
            TestCase {
                name: "whitespace before = dictionary",
                input: "a =1, b=2",
                expect: Err(Error::ParseError { index: 2 }),
            },
            TestCase {
                name: "whitespace after = dictionary",
                input: "a=1, b= 2",
                expect: Err(Error::ParseError { index: 7 }),
            },
            // two lines dictionary
            // This crate does not support merging 2 lines
            TestCase {
                name: "missing value dictionary",
                input: "a=1, b, c=3",
                expect: Ok(vec![
                    (String::from("a"), TValue::Integer(1), vec![]),
                    (String::from("b"), TValue::Bool(true), vec![]),
                    (String::from("c"), TValue::Integer(3), vec![]),
                ]),
            },
            TestCase {
                name: "all missing value dictionary",
                input: "a, b, c",
                expect: Ok(vec![
                    (String::from("a"), TValue::Bool(true), vec![]),
                    (String::from("b"), TValue::Bool(true), vec![]),
                    (String::from("c"), TValue::Bool(true), vec![]),
                ]),
            },
            TestCase {
                name: "start missing value dictionary",
                input: "a, b=2",
                expect: Ok(vec![
                    (String::from("a"), TValue::Bool(true), vec![]),
                    (String::from("b"), TValue::Integer(2), vec![]),
                ]),
            },
            TestCase {
                name: "end missing value dictionary",
                input: "a=1, b",
                expect: Ok(vec![
                    (String::from("a"), TValue::Integer(1), vec![]),
                    (String::from("b"), TValue::Bool(true), vec![]),
                ]),
            },
            TestCase {
                name: "missing value with params dictionary",
                input: "a=1, b;foo=9, c=3",
                expect: Ok(vec![
                    (String::from("a"), TValue::Integer(1), vec![]),
                    (
                        String::from("b"),
                        TValue::Bool(true),
                        vec![(String::from("foo"), TValue::Integer(9))],
                    ),
                    (String::from("c"), TValue::Integer(3), vec![]),
                ]),
            },
            TestCase {
                name: "explicit true value with params dictionary",
                input: "a=1, b=?1;foo=9, c=3",
                expect: Ok(vec![
                    (String::from("a"), TValue::Integer(1), vec![]),
                    (
                        String::from("b"),
                        TValue::Bool(true),
                        vec![(String::from("foo"), TValue::Integer(9))],
                    ),
                    (String::from("c"), TValue::Integer(3), vec![]),
                ]),
            },
            TestCase {
                name: "trailing comma dictionary",
                input: "a=1, b=2,",
                expect: Err(Error::ParseError { index: 9 }),
            },
            TestCase {
                name: "empty item dictionary",
                input: "a=1,,b=2,",
                expect: Err(Error::ParseError { index: 4 }),
            },
            TestCase {
                name: "duplicate key dictionary",
                // This crate does no effort to find duplicates.
                input: "a=1,b=2,a=3",
                expect: Ok(vec![
                    (String::from("a"), TValue::Integer(1), vec![]),
                    (String::from("b"), TValue::Integer(2), vec![]),
                    (String::from("a"), TValue::Integer(3), vec![]),
                ]),
            },
            TestCase {
                name: "numeric key dictionary",
                input: "a=1,1b=2,a=1",
                expect: Err(Error::ParseError { index: 4 }),
            },
            TestCase {
                name: "uppercase key dictionary",
                input: "a=1,B=2,a=1",
                expect: Err(Error::ParseError { index: 4 }),
            },
            TestCase {
                name: "bad key dictionary",
                input: "a=1,b!=2,a=1",
                expect: Err(Error::ParseError { index: 5 }),
            },
            TestCase {
                name: "basic parameterised dict",
                input: r#"abc=123;a=1;b=2, def=456, ghi=789;q=9;r="+w""#,
                expect: Ok(vec![
                    (
                        String::from("abc"),
                        TValue::Integer(123),
                        vec![
                            (String::from("a"), TValue::Integer(1)),
                            (String::from("b"), TValue::Integer(2)),
                        ],
                    ),
                    (String::from("def"), TValue::Integer(456), vec![]),
                    (
                        String::from("ghi"),
                        TValue::Integer(789),
                        vec![
                            (String::from("q"), TValue::Integer(9)),
                            (
                                String::from("r"),
                                TValue::String {
                                    str: "+w",
                                    escape: false,
                                },
                            ),
                        ],
                    ),
                ]),
            },
            TestCase {
                name: "single item parameterised dict",
                input: "a=b; q=1.0",
                expect: Ok(vec![(
                    String::from("a"),
                    TValue::Token("b"),
                    vec![(
                        String::from("q"),
                        TValue::Decimal {
                            numer: 10,
                            denom: 10,
                        },
                    )],
                )]),
            },
            TestCase {
                name: "list item parameterised dictionary",
                input: "a=(1 2); q=1.0",
                expect: Ok(vec![(
                    String::from("a"),
                    TValue::InnerList(vec![
                        (TValue::Integer(1), vec![]),
                        (TValue::Integer(2), vec![]),
                    ]),
                    vec![(
                        String::from("q"),
                        TValue::Decimal {
                            numer: 10,
                            denom: 10,
                        },
                    )],
                )]),
            },
            TestCase {
                name: "missing parameter value parameterised dict",
                input: "a=3;c;d=5",
                expect: Ok(vec![(
                    String::from("a"),
                    TValue::Integer(3),
                    vec![
                        (String::from("c"), TValue::Bool(true)),
                        (String::from("d"), TValue::Integer(5)),
                    ],
                )]),
            },
            TestCase {
                name: "terminal missing parameter value parameterised dict",
                input: "a=3;c=5;d",
                expect: Ok(vec![(
                    String::from("a"),
                    TValue::Integer(3),
                    vec![
                        (String::from("c"), TValue::Integer(5)),
                        (String::from("d"), TValue::Bool(true)),
                    ],
                )]),
            },
            TestCase {
                name: "no whitespace parameterised dict",
                input: "a=b;c=1,d=e;f=2",
                expect: Ok(vec![
                    (
                        String::from("a"),
                        TValue::Token("b"),
                        vec![(String::from("c"), TValue::Integer(1))],
                    ),
                    (
                        String::from("d"),
                        TValue::Token("e"),
                        vec![(String::from("f"), TValue::Integer(2))],
                    ),
                ]),
            },
            TestCase {
                name: "whitespace before = parameterised dict",
                input: "a=b;q =0.5",
                expect: Err(Error::ParseError { index: 6 }),
            },
            TestCase {
                name: "whitespace after = parameterised dict",
                input: "a=b;q= 0.5",
                expect: Err(Error::ParseError { index: 6 }),
            },
            TestCase {
                name: "whitespace before ; parameterised dict",
                input: "a=b ;q=0.5",
                expect: Err(Error::ParseError { index: 4 }),
            },
            TestCase {
                name: "whitespace after ; parameterised dict",
                input: "a=b; q=0.5",
                expect: Ok(vec![(
                    String::from("a"),
                    TValue::Token("b"),
                    vec![(
                        String::from("q"),
                        TValue::Decimal {
                            numer: 5,
                            denom: 10,
                        },
                    )],
                )]),
            },
            TestCase {
                name: "extra whitespace parameterised dict",
                input: "a=b;  c=1  ,  d=e; f=2; g=3",
                expect: Ok(vec![
                    (
                        String::from("a"),
                        TValue::Token("b"),
                        vec![(String::from("c"), TValue::Integer(1))],
                    ),
                    (
                        String::from("d"),
                        TValue::Token("e"),
                        vec![
                            (String::from("f"), TValue::Integer(2)),
                            (String::from("g"), TValue::Integer(3)),
                        ],
                    ),
                ]),
            },
            // two lines parameterised list
            // This crate does not support merging 2 lines
            TestCase {
                name: "trailing comma parameterised list",
                input: "a=b; q=1.0,",
                expect: Err(Error::ParseError { index: 11 }),
            },
            TestCase {
                name: "empty item parameterised list",
                input: "a=b; q=1.0,,c=d",
                expect: Err(Error::ParseError { index: 11 }),
            },
            // Additional tests
            TestCase {
                name: "empty value",
                input: "a=",
                expect: Err(Error::ParseError { index: 2 }),
            },
            TestCase {
                name: "empty parameter value",
                input: "a=b;c=",
                expect: Err(Error::ParseError { index: 6 }),
            },
        ]
        .iter()
        .for_each(|t| {
            let mut p = Parser::new(t.input.as_bytes());

            let res = || -> Result<Vec<(String, TValue, Vec<(String, TValue)>)>, Error> {
                let mut vec = Vec::new();

                loop {
                    match p.parse_dict() {
                        Ok(None) => return Ok(vec),
                        Ok(Some((k, v))) => {
                            let k = String::from(k);

                            let v = match v {
                                Value::InnerList => parse_inner_list(&mut p, t.input)?,
                                _ => TValue::from_value(v, t.input),
                            };

                            let params = parse_params(&mut p, t.input)?;

                            vec.push((k, v, params));
                        }
                        Err(err) => return Err(err),
                    };
                }
            }();

            assert_eq!(t.expect, res, "{}", t.name);
        });
    }

    #[test]
    fn parse_list() {
        struct TestCase<'a> {
            name: &'a str,
            input: &'a str,
            expect: Result<Vec<(TValue<'a>, Vec<(String, TValue<'a>)>)>, Error>,
        }

        [
            TestCase {
                name: "basic list",
                input: "1, 42",
                expect: Ok(vec![
                    (TValue::Integer(1), vec![]),
                    (TValue::Integer(42), vec![]),
                ]),
            },
            TestCase {
                name: "empty list",
                input: "",
                expect: Ok(vec![]),
            },
            TestCase {
                name: "leading SP list",
                input: "  42, 43",
                expect: Ok(vec![
                    (TValue::Integer(42), vec![]),
                    (TValue::Integer(43), vec![]),
                ]),
            },
            TestCase {
                name: "single item list",
                input: "42",
                expect: Ok(vec![(TValue::Integer(42), vec![])]),
            },
            TestCase {
                name: "no whitespace list",
                input: "1,42",
                expect: Ok(vec![
                    (TValue::Integer(1), vec![]),
                    (TValue::Integer(42), vec![]),
                ]),
            },
            TestCase {
                name: "extra whitespace list",
                input: "1 , 42",
                expect: Ok(vec![
                    (TValue::Integer(1), vec![]),
                    (TValue::Integer(42), vec![]),
                ]),
            },
            TestCase {
                name: "tab separated list",
                input: "1\t,\t42",
                expect: Ok(vec![
                    (TValue::Integer(1), vec![]),
                    (TValue::Integer(42), vec![]),
                ]),
            },
            // two line list
            // This crate does not support merging 2 lines
            TestCase {
                name: "trailing comma list",
                input: "1, 42,",
                expect: Err(Error::ParseError { index: 6 }),
            },
            TestCase {
                name: "empty item list",
                input: "1,,42",
                expect: Err(Error::ParseError { index: 2 }),
            },
            // empty item list (multiple field lines)
            // This crate does not support merging 2 lines
            TestCase {
                name: "basic list of lists",
                input: "(1 2), (42 43)",
                expect: Ok(vec![
                    (
                        TValue::InnerList(vec![
                            (TValue::Integer(1), vec![]),
                            (TValue::Integer(2), vec![]),
                        ]),
                        vec![],
                    ),
                    (
                        TValue::InnerList(vec![
                            (TValue::Integer(42), vec![]),
                            (TValue::Integer(43), vec![]),
                        ]),
                        vec![],
                    ),
                ]),
            },
            TestCase {
                name: "single item list of lists",
                input: "(42)",
                expect: Ok(vec![(
                    TValue::InnerList(vec![(TValue::Integer(42), vec![])]),
                    vec![],
                )]),
            },
            TestCase {
                name: "empty item list of lists",
                input: "()",
                expect: Ok(vec![(TValue::InnerList(vec![]), vec![])]),
            },
            TestCase {
                name: "empty middle item list of lists",
                input: "(1),(),(42)",
                expect: Ok(vec![
                    (
                        TValue::InnerList(vec![(TValue::Integer(1), vec![])]),
                        vec![],
                    ),
                    (TValue::InnerList(vec![]), vec![]),
                    (
                        TValue::InnerList(vec![(TValue::Integer(42), vec![])]),
                        vec![],
                    ),
                ]),
            },
            TestCase {
                name: "extra whitespace list of lists",
                input: "(  1  42  )",
                expect: Ok(vec![(
                    TValue::InnerList(vec![
                        (TValue::Integer(1), vec![]),
                        (TValue::Integer(42), vec![]),
                    ]),
                    vec![],
                )]),
            },
            TestCase {
                name: "wrong whitespace list of lists",
                input: "(1\t 42)",
                expect: Err(Error::ParseError { index: 2 }),
            },
            TestCase {
                name: "no trailing parenthesis list of lists",
                input: "(1 42",
                expect: Err(Error::ParseError { index: 5 }),
            },
            TestCase {
                name: "no trailing parenthesis middle list of lists",
                input: "(1 2, (42 43)",
                expect: Err(Error::ParseError { index: 4 }),
            },
            TestCase {
                name: "no spaces in inner-list",
                input: "(abc\"def\"?0123*dXZ3*xyz)",
                expect: Err(Error::ParseError { index: 4 }),
            },
            TestCase {
                name: "no closing parenthesis",
                input: "(",
                expect: Err(Error::ParseError { index: 1 }),
            },
            TestCase {
                name: "basic parameterised list",
                input: r#"abc_123;a=1;b=2; cdef_456, ghi;q=9;r="+w""#,
                expect: Ok(vec![
                    (
                        TValue::Token("abc_123"),
                        vec![
                            (String::from("a"), TValue::Integer(1)),
                            (String::from("b"), TValue::Integer(2)),
                            (String::from("cdef_456"), TValue::Bool(true)),
                        ],
                    ),
                    (
                        TValue::Token("ghi"),
                        vec![
                            (String::from("q"), TValue::Integer(9)),
                            (
                                String::from("r"),
                                TValue::String {
                                    str: "+w",
                                    escape: false,
                                },
                            ),
                        ],
                    ),
                ]),
            },
            TestCase {
                name: "single item parameterised list",
                input: "text/html;q=1.0",
                expect: Ok(vec![(
                    TValue::Token("text/html"),
                    vec![(
                        String::from("q"),
                        TValue::Decimal {
                            numer: 10,
                            denom: 10,
                        },
                    )],
                )]),
            },
            TestCase {
                name: "missing parameter value parameterised list",
                input: "text/html;a;q=1.0",
                expect: Ok(vec![(
                    TValue::Token("text/html"),
                    vec![
                        (String::from("a"), TValue::Bool(true)),
                        (
                            String::from("q"),
                            TValue::Decimal {
                                numer: 10,
                                denom: 10,
                            },
                        ),
                    ],
                )]),
            },
            TestCase {
                name: "missing terminal parameter value parameterised list",
                input: "text/html;q=1.0;a",
                expect: Ok(vec![(
                    TValue::Token("text/html"),
                    vec![
                        (
                            String::from("q"),
                            TValue::Decimal {
                                numer: 10,
                                denom: 10,
                            },
                        ),
                        (String::from("a"), TValue::Bool(true)),
                    ],
                )]),
            },
            TestCase {
                name: "no whitespace parameterised list",
                input: "text/html,text/plain;q=0.5",
                expect: Ok(vec![
                    (TValue::Token("text/html"), vec![]),
                    (
                        TValue::Token("text/plain"),
                        vec![(
                            String::from("q"),
                            TValue::Decimal {
                                numer: 5,
                                denom: 10,
                            },
                        )],
                    ),
                ]),
            },
            TestCase {
                name: "whitespace before = parameterised list",
                input: "text/html, text/plain;q =0.5",
                expect: Err(Error::ParseError { index: 24 }),
            },
            TestCase {
                name: "whitespace after = parameterised list",
                input: "text/html, text/plain;q= 0.5",
                expect: Err(Error::ParseError { index: 24 }),
            },
            TestCase {
                name: "whitespace before ; parameterised list",
                input: "text/html, text/plain ;q=0.5",
                expect: Err(Error::ParseError { index: 22 }),
            },
            TestCase {
                name: "whitespace after ; parameterised list",
                input: "text/html, text/plain; q=0.5",
                expect: Ok(vec![
                    (TValue::Token("text/html"), vec![]),
                    (
                        TValue::Token("text/plain"),
                        vec![(
                            String::from("q"),
                            TValue::Decimal {
                                numer: 5,
                                denom: 10,
                            },
                        )],
                    ),
                ]),
            },
            TestCase {
                name: "extra whitespace parameterised list",
                input: "text/html  ,  text/plain;  q=0.5;  charset=utf-8",
                expect: Ok(vec![
                    (TValue::Token("text/html"), vec![]),
                    (
                        TValue::Token("text/plain"),
                        vec![
                            (
                                String::from("q"),
                                TValue::Decimal {
                                    numer: 5,
                                    denom: 10,
                                },
                            ),
                            (String::from("charset"), TValue::Token("utf-8")),
                        ],
                    ),
                ]),
            },
            // two lines parameterised list
            // sfparse_parser does not support merging 2 lines
            TestCase {
                name: "trailing comma parameterised list",
                input: "text/html,text/plain;q=0.5,",
                expect: Err(Error::ParseError { index: 27 }),
            },
            TestCase {
                name: "empty item parameterised list",
                input: "text/html,,text/plain;q=0.5,",
                expect: Err(Error::ParseError { index: 10 }),
            },
            TestCase {
                name: "parameterised inner list",
                input: "(abc_123);a=1;b=2, cdef_456",
                expect: Ok(vec![
                    (
                        TValue::InnerList(vec![(TValue::Token("abc_123"), vec![])]),
                        vec![
                            (String::from("a"), TValue::Integer(1)),
                            (String::from("b"), TValue::Integer(2)),
                        ],
                    ),
                    (TValue::Token("cdef_456"), vec![]),
                ]),
            },
            TestCase {
                name: "parameterised inner list item",
                input: "(abc_123;a=1;b=2;cdef_456)",
                expect: Ok(vec![(
                    TValue::InnerList(vec![(
                        TValue::Token("abc_123"),
                        vec![
                            (String::from("a"), TValue::Integer(1)),
                            (String::from("b"), TValue::Integer(2)),
                            (String::from("cdef_456"), TValue::Bool(true)),
                        ],
                    )]),
                    vec![],
                )]),
            },
            TestCase {
                name: "parameterised inner list with parameterised item",
                input: "(abc_123;a=1;b=2);cdef_456",
                expect: Ok(vec![(
                    TValue::InnerList(vec![(
                        TValue::Token("abc_123"),
                        vec![
                            (String::from("a"), TValue::Integer(1)),
                            (String::from("b"), TValue::Integer(2)),
                        ],
                    )]),
                    vec![(String::from("cdef_456"), TValue::Bool(true))],
                )]),
            },
            // Additional tests
            TestCase {
                name: "no opening parenthesis",
                input: ")",
                expect: Err(Error::ParseError { index: 0 }),
            },
            TestCase {
                name: "empty parameter value",
                input: "a;b=",
                expect: Err(Error::ParseError { index: 4 }),
            },
            TestCase {
                name: "empty parameter value",
                input: "(a;b= 1)",
                expect: Err(Error::ParseError { index: 5 }),
            },
        ]
        .iter()
        .for_each(|t| {
            let mut p = Parser::new(t.input.as_bytes());

            let res = || -> Result<Vec<(TValue, Vec<(String, TValue)>)>, Error> {
                let mut l = Vec::new();

                loop {
                    match p.parse_list() {
                        Ok(None) => return Ok(l),
                        Ok(Some(v)) => {
                            let v = match v {
                                Value::InnerList => parse_inner_list(&mut p, t.input)?,
                                _ => TValue::from_value(v, t.input),
                            };

                            let params = parse_params(&mut p, t.input)?;

                            l.push((v, params));
                        }
                        Err(err) => return Err(err),
                    };
                }
            }();

            assert_eq!(t.expect, res, "{}", t.name);
        });
    }

    #[test]
    fn parse_number_generated() {
        for len in 1..=15 {
            for c in [b'0', b'1', b'9'] {
                let input = vec![c; len];
                let s = std::str::from_utf8(input.as_slice()).unwrap();
                let n: i64 = s.parse().unwrap();
                let mut p = Parser::new(input.as_slice());

                assert_eq!(Ok(Some(Value::Integer(n))), p.parse_item(), "{}", s);
                assert_eq!(Ok(None), p.parse_item());
            }
        }

        for len in 1..=12 {
            for plen in 1..=3 {
                for (a, b) in [(b'0', b'1'), (b'1', b'0'), (b'1', b'1'), (b'9', b'9')] {
                    let mut input = vec![a; len + plen];
                    input[len..].fill(b);

                    let numer: i64 = std::str::from_utf8(input.as_slice())
                        .unwrap()
                        .parse()
                        .unwrap();
                    let denom: i64 = 10i64.pow(plen as u32);

                    let mut input = vec![a; len + 1 + plen];
                    input[len] = b'.';
                    input[len + 1..].fill(b);

                    let mut p = Parser::new(input.as_slice());

                    assert_eq!(
                        Ok(Some(Value::Decimal {
                            numer: numer,
                            denom: denom
                        })),
                        p.parse_item()
                    );
                    assert_eq!(Ok(None), p.parse_item());
                }
            }
        }
    }

    #[test]
    fn parse_string_generated() {
        for i in 0..=255 {
            let a = [b'"', b' ', i, b' ', b'"'];
            let mut p = Parser::new(&a);

            match i {
                0x20 | 0x21 | 0x23..=0x5b | 0x5d..=0x7e => {
                    assert_eq!(
                        Ok(Some(Value::String {
                            range: 1..4,
                            escape: false
                        })),
                        p.parse_item()
                    );
                    assert_eq!(Ok(None), p.parse_item());
                }
                0x22 => {
                    assert_eq!(
                        Ok(Some(Value::String {
                            range: 1..2,
                            escape: false
                        })),
                        p.parse_item()
                    );
                    assert_eq!(Err(Error::ParseError { index: 4 }), p.parse_item());
                }
                _ => assert_eq!(
                    Err(Error::ParseError {
                        index: if i == 0x5c { 3 } else { 2 }
                    }),
                    p.parse_item()
                ),
            }
        }

        for i in 0..=255 {
            let a = [b'"', b'\\', i, b'"'];
            let mut p = Parser::new(&a);

            match i {
                0x5c | 0x22 => {
                    assert_eq!(
                        Ok(Some(Value::String {
                            range: 1..3,
                            escape: true
                        })),
                        p.parse_item(),
                    );
                    assert_eq!(Ok(None), p.parse_item());
                }
                _ => assert_eq!(Err(Error::ParseError { index: 2 }), p.parse_item()),
            }
        }
    }

    #[test]
    fn parse_token_generated() {
        for i in 0..=255 {
            let a = [b'a', i, b'a'];
            let mut p = Parser::new(&a);

            match i {
                b'A'..=b'Z'
                | b'a'..=b'z'
                | b'0'..=b'9'
                | b'!'
                | b'#'
                | b'$'
                | b'%'
                | b'&'
                | b'\''
                | b'*'
                | b'+'
                | b'-'
                | b'.'
                | b'^'
                | b'_'
                | b'`'
                | b'|'
                | b'~'
                | b':'
                | b'/' => {
                    assert_eq!(Ok(Some(Value::Token(0..3))), p.parse_item());
                    assert_eq!(Ok(None), p.parse_item());
                }
                b';' => {
                    assert_eq!(Ok(Some(Value::Token(0..1))), p.parse_item());
                    assert_eq!(
                        Ok(vec![(String::from("a"), TValue::Bool(true))]),
                        parse_params(&mut p, std::str::from_utf8(&a).unwrap())
                    );
                }
                b' ' => {
                    assert_eq!(Ok(Some(Value::Token(0..1))), p.parse_item());
                    assert_eq!(Err(Error::ParseError { index: 2 }), p.parse_item());
                }
                _ => {
                    assert_eq!(Ok(Some(Value::Token(0..1))), p.parse_item());
                    assert_eq!(Err(Error::ParseError { index: 1 }), p.parse_item());
                }
            }
        }

        for i in 0..=255 {
            let a = [i, b'a'];
            let mut p = Parser::new(&a);

            match i {
                b'A'..=b'Z' | b'a'..=b'z' | b'*' => {
                    assert_eq!(Ok(Some(Value::Token(0..2))), p.parse_item());
                    assert_eq!(Ok(None), p.parse_item());
                }
                b' ' => {
                    assert_eq!(Ok(Some(Value::Token(1..2))), p.parse_item());
                    assert_eq!(Ok(None), p.parse_item());
                }
                b'0'..=b'9' => {
                    assert_eq!(Ok(Some(Value::Integer((i - b'0') as i64))), p.parse_item());
                    assert_eq!(Err(Error::ParseError { index: 1 }), p.parse_item());
                }
                b'(' => {
                    assert_eq!(Ok(Some(Value::InnerList)), p.parse_item());
                    assert_eq!(Ok(Some(Value::Token(1..2))), p.parse_inner_list());
                    assert_eq!(Err(Error::ParseError { index: 2 }), p.parse_inner_list());
                }
                b'"' | b':' => {
                    assert_eq!(Err(Error::ParseError { index: 2 }), p.parse_item());
                }
                b'%' | b'@' | b'-' | b'?' => {
                    assert_eq!(Err(Error::ParseError { index: 1 }), p.parse_item());
                }
                _ => {
                    assert_eq!(Err(Error::ParseError { index: 0 }), p.parse_item());
                }
            }
        }
    }

    #[test]
    fn parse_key_generated() {
        for i in 0..=255 {
            let a = [i, b'=', b'1'];
            let mut p = Parser::new(&a);

            match i {
                b'a'..=b'z' | b'*' => {
                    assert_eq!(
                        Ok(Some((
                            std::str::from_utf8(&a[..1]).unwrap(),
                            Value::Integer(1)
                        ))),
                        p.parse_dict()
                    );
                    assert_eq!(Ok(None), p.parse_dict());
                }
                b' ' => assert_eq!(Err(Error::ParseError { index: 1 }), p.parse_dict()),
                _ => {
                    assert_eq!(Err(Error::ParseError { index: 0 }), p.parse_dict());
                }
            }
        }

        for i in 0..=255 {
            let a = [b'a', i, b'a', b'=', b'1'];
            let mut p = Parser::new(&a);

            match i {
                b'a'..=b'z' | b'0'..=b'9' | b'_' | b'-' | b'.' | b'*' => {
                    assert_eq!(
                        Ok(Some((
                            std::str::from_utf8(&a[..3]).unwrap(),
                            Value::Integer(1)
                        ))),
                        p.parse_dict()
                    );
                    assert_eq!(Ok(None), p.parse_dict());
                }
                b'=' => {
                    assert_eq!(Ok(Some(("a", Value::Token(2..3)))), p.parse_dict());
                    assert_eq!(Err(Error::ParseError { index: 3 }), p.parse_dict());
                }
                b',' => {
                    assert_eq!(Ok(Some(("a", Value::Bool(true)))), p.parse_dict());
                    assert_eq!(Ok(Some(("a", Value::Integer(1)))), p.parse_dict());
                    assert_eq!(Ok(None), p.parse_dict());
                }
                b';' => {
                    assert_eq!(Ok(Some(("a", Value::Bool(true)))), p.parse_dict());
                    assert_eq!(Ok(Some(("a", Value::Integer(1)))), p.parse_param());
                    assert_eq!(Ok(None), p.parse_param());
                    assert_eq!(Ok(None), p.parse_dict());
                }
                b'\t' | b' ' => {
                    assert_eq!(Ok(Some(("a", Value::Bool(true)))), p.parse_dict());
                    assert_eq!(Err(Error::ParseError { index: 2 }), p.parse_dict());
                }
                _ => {
                    assert_eq!(Ok(Some(("a", Value::Bool(true)))), p.parse_dict());
                    assert_eq!(Err(Error::ParseError { index: 1 }), p.parse_dict());
                }
            }
        }

        for i in 0..=255 {
            let a = [i, b'a', b'=', b'1'];
            let mut p = Parser::new(&a);

            match i {
                b'a'..=b'z' | b'*' => {
                    assert_eq!(
                        Ok(Some((
                            std::str::from_utf8(&a[..2]).unwrap(),
                            Value::Integer(1)
                        ))),
                        p.parse_dict()
                    );
                    assert_eq!(Ok(None), p.parse_dict());
                }
                b' ' => {
                    assert_eq!(
                        Ok(Some((
                            std::str::from_utf8(&a[1..2]).unwrap(),
                            Value::Integer(1)
                        ))),
                        p.parse_dict()
                    );
                    assert_eq!(Ok(None), p.parse_dict());
                }
                _ => assert_eq!(Err(Error::ParseError { index: 0 }), p.parse_dict()),
            }
        }

        for i in 0..=255 {
            let s = format!("foo; a{}a=1", char::from(i));
            let a = s.as_bytes();
            let mut p = Parser::new(a);

            assert_eq!(Ok(Some(Value::Token(0..3))), p.parse_list());

            match i {
                b'a'..=b'z' | b'0'..=b'9' | b'_' | b'-' | b'.' | b'*' => {
                    assert_eq!(
                        Ok(Some((
                            std::str::from_utf8(&a[5..8]).unwrap(),
                            Value::Integer(1)
                        ))),
                        p.parse_param()
                    );
                    assert_eq!(Ok(None), p.parse_param());
                    assert_eq!(Ok(None), p.parse_list());
                }
                b'=' => {
                    assert_eq!(Ok(Some(("a", Value::Token(7..8)))), p.parse_param());
                    assert_eq!(Ok(None), p.parse_param());
                    assert_eq!(Err(Error::ParseError { index: 8 }), p.parse_list());
                }
                b';' => {
                    assert_eq!(Ok(Some(("a", Value::Bool(true)))), p.parse_param());
                    assert_eq!(Ok(Some(("a", Value::Integer(1)))), p.parse_param());
                    assert_eq!(Ok(None), p.parse_param());
                    assert_eq!(Ok(None), p.parse_list());
                }
                b',' => {
                    assert_eq!(Ok(Some(("a", Value::Bool(true)))), p.parse_param());
                    assert_eq!(Ok(None), p.parse_param());
                    assert_eq!(Ok(Some(Value::Token(7..8))), p.parse_list());
                    assert_eq!(Err(Error::ParseError { index: 8 }), p.parse_list());
                }
                b'\t' | b' ' => {
                    assert_eq!(Ok(Some(("a", Value::Bool(true)))), p.parse_param());
                    assert_eq!(Ok(None), p.parse_param());
                    assert_eq!(Err(Error::ParseError { index: 7 }), p.parse_list());
                }
                _ => {
                    assert_eq!(Ok(Some(("a", Value::Bool(true)))), p.parse_param());
                    assert_eq!(Ok(None), p.parse_param());
                    assert_eq!(Err(Error::ParseError { index: 6 }), p.parse_list());
                }
            }
        }

        for i in 0..=255 {
            let s = format!("foo; {}a=1", char::from(i));
            let a = s.as_bytes();
            let mut p = Parser::new(a);

            assert_eq!(Ok(Some(Value::Token(0..3))), p.parse_list());

            match i {
                b'a'..=b'z' | b'*' => {
                    assert_eq!(
                        Ok(Some((
                            std::str::from_utf8(&a[5..7]).unwrap(),
                            Value::Integer(1)
                        ))),
                        p.parse_param()
                    );
                    assert_eq!(Ok(None), p.parse_param());
                    assert_eq!(Ok(None), p.parse_list());
                }
                b' ' => {
                    assert_eq!(Ok(Some(("a", Value::Integer(1)))), p.parse_param());
                    assert_eq!(Ok(None), p.parse_param());
                    assert_eq!(Ok(None), p.parse_list());
                }
                _ => assert_eq!(Err(Error::ParseError { index: 5 }), p.parse_param()),
            }
        }
    }

    #[test]
    fn parse_byteseq_generated() {
        for i in 0..=255 {
            let s = format!(":/{}Ah:", char::from(i));
            let a = s.as_bytes();
            let mut p = Parser::new(a);

            match i {
                b'+' | b'/' | b'0'..=b'9' | b'A'..=b'Z' | b'a'..=b'z' => {
                    assert_eq!(Ok(Some(Value::ByteSeq(1..5))), p.parse_item());
                    assert_eq!(Ok(None), p.parse_item());
                }
                _ => assert_eq!(Err(Error::ParseError { index: 2 }), p.parse_item()),
            }
        }
    }

    #[test]
    fn parse_large_generated() {
        // large dictionary
        {
            let s = (0..1024)
                .map(|i| format!("a{i}=1, "))
                .reduce(|c, n| c + &n)
                .unwrap();
            let a = &s.as_bytes()[..s.len() - 2];
            let mut p = Parser::new(a);

            for i in 0..1024 {
                assert_eq!(
                    Ok(Some((format!("a{i}").as_str(), Value::Integer(1)))),
                    p.parse_dict()
                );
            }

            assert_eq!(Ok(None), p.parse_dict());
        }

        // large dictionary key
        {
            let mut p = Parser::new(
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa=1".as_bytes(),
            );

            assert_eq!(
                Ok(Some((
                    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                    Value::Integer(1)
                ))),
                p.parse_dict()
            );
            assert_eq!(Ok(None), p.parse_dict());
        }

        // large list
        {
            let s = (0..1024)
                .map(|i| format!("a{i}, "))
                .reduce(|c, n| c + &n)
                .unwrap();
            let a = &s.as_bytes()[..s.len() - 2];
            let mut p = Parser::new(a);
            let mut index = 0;

            for i in 0..1024 {
                let len = match i {
                    ..10 => 2,
                    ..100 => 3,
                    ..1000 => 4,
                    _ => 5,
                };

                assert_eq!(Ok(Some(Value::Token(index..index + len))), p.parse_list());
                index += len + 2;
            }

            assert_eq!(Ok(None), p.parse_list());
        }

        // large parameterised list
        {
            let s = (0..1024)
                .map(|i| format!("foo;a{i}=1, "))
                .reduce(|c, n| c + &n)
                .unwrap();
            let a = &s.as_bytes()[..s.len() - 2];
            let mut p = Parser::new(a);
            let mut index = 0;

            for i in 0..1024 {
                assert_eq!(Ok(Some(Value::Token(index..index + 3))), p.parse_list());

                let k = format!("a{i}");

                assert_eq!(Ok(Some((k.as_str(), Value::Integer(1)))), p.parse_param());
                assert_eq!(Ok(None), p.parse_param());

                index += 4 + k.len() + 4;
            }

            assert_eq!(Ok(None), p.parse_list());
        }

        // large params
        {
            let s = (0..1024)
                .map(|i| format!(";a{i}=1"))
                .fold(String::from("foo"), |c, n| c + n.as_str());
            let a = s.as_bytes();
            let mut p = Parser::new(a);

            assert_eq!(Ok(Some(Value::Token(0..3))), p.parse_list());

            for i in 0..1024 {
                assert_eq!(
                    Ok(Some((format!("a{i}").as_str(), Value::Integer(1)))),
                    p.parse_param()
                );
            }

            assert_eq!(Ok(None), p.parse_param());
            assert_eq!(Ok(None), p.parse_list());
        }

        // large param key
        {
            let mut p = Parser::new(
                "foo;aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa=1".as_bytes(),
            );

            assert_eq!(Ok(Some(Value::Token(0..3))), p.parse_list());
            assert_eq!(
                Ok(Some((
                    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                    Value::Integer(1)
                ))),
                p.parse_param()
            );
            assert_eq!(Ok(None), p.parse_param());
            assert_eq!(Ok(None), p.parse_list());
        }

        // large string
        {
            let s = format!(r#""{}""#, "=".repeat(1024));
            let mut p = Parser::new(s.as_bytes());

            assert_eq!(
                Ok(Some(Value::String {
                    range: 1..1025,
                    escape: false
                })),
                p.parse_item()
            );
            assert_eq!(Ok(None), p.parse_item());
        }

        // large escaped string
        {
            let s = format!(r#""{}""#, r#"\""#.repeat(1024));
            let mut p = Parser::new(s.as_bytes());

            assert_eq!(
                Ok(Some(Value::String {
                    range: 1..2049,
                    escape: true
                })),
                p.parse_item()
            );
            assert_eq!(Ok(None), p.parse_item());
        }

        // large token
        {
            let s = "a".repeat(1024);
            let mut p = Parser::new(s.as_bytes());

            assert_eq!(Ok(Some(Value::Token(0..1024))), p.parse_item());
            assert_eq!(Ok(None), p.parse_item());
        }
    }

    #[test]
    fn parse_item_skip() {
        // skip empty parameter
        {
            let mut p = Parser::new("a".as_bytes());

            assert_eq!(Ok(Some(Value::Token(0..1))), p.parse_item());
            assert_eq!(Ok(None), p.parse_item());
        }

        // skip non-empty parameter
        {
            let mut p = Parser::new("a;f=1000000009;g=1000000007".as_bytes());

            assert_eq!(Ok(Some(Value::Token(0..1))), p.parse_item());
            assert_eq!(Ok(None), p.parse_item());
        }

        // skip boolean parameter
        {
            let mut p = Parser::new("a;f".as_bytes());

            assert_eq!(Ok(Some(Value::Token(0..1))), p.parse_item());
            assert_eq!(Ok(None), p.parse_item());
        }

        // skip inner list with empty parameter
        {
            let mut p = Parser::new("(a)".as_bytes());

            assert_eq!(Ok(Some(Value::InnerList)), p.parse_item());
            assert_eq!(Ok(None), p.parse_item());
        }

        [
            TestCase {
                name: "skip empty parameter",
                input: "a",
                expect: Ok(Some(Value::Token(0..1))),
            },
            TestCase {
                name: "skip non-empty parameter",
                input: "a;f=1000000009;g=1000000007",
                expect: Ok(Some(Value::Token(0..1))),
            },
            TestCase {
                name: "skip boolean parameter",
                input: "a;f",
                expect: Ok(Some(Value::Token(0..1))),
            },
            TestCase {
                name: "skip inner list with empty parameter",
                input: "(a)",
                expect: Ok(Some(Value::InnerList)),
            },
            TestCase {
                name: "skip inner list with non-empty parameter",
                input: "(a);f=1000000009;g=1000000007",
                expect: Ok(Some(Value::InnerList)),
            },
            TestCase {
                name: "skip inner list with boolean parameter",
                input: "(a);f",
                expect: Ok(Some(Value::InnerList)),
            },
        ]
        .iter()
        .for_each(|t| {
            let mut p = Parser::new(t.input.as_bytes());

            assert_eq!(t.expect, p.parse_item());
            assert_eq!(Ok(None), p.parse_item());
        });

        // skip inner list but read parameter
        {
            let mut p = Parser::new("(a);f".as_bytes());

            assert_eq!(Ok(Some(Value::InnerList)), p.parse_item());
            assert_eq!(Ok(Some(("f", Value::Bool(true)))), p.parse_param());
            assert_eq!(Ok(None), p.parse_param());
            assert_eq!(Ok(None), p.parse_item());
        }

        // skip inner list item parameter
        {
            let mut p = Parser::new("(1;foo=100 2;bar)".as_bytes());

            assert_eq!(Ok(Some(Value::InnerList)), p.parse_item());
            assert_eq!(Ok(Some(Value::Integer(1))), p.parse_inner_list());
            assert_eq!(Ok(Some(Value::Integer(2))), p.parse_inner_list());
            assert_eq!(Ok(None), p.parse_inner_list());
            assert_eq!(Ok(None), p.parse_item());
        }
    }

    #[test]
    fn parse_dict_skip() {
        // skip empty parameter
        {
            let mut p = Parser::new("a=3".as_bytes());

            assert_eq!(Ok(Some(("a", Value::Integer(3)))), p.parse_dict());
            assert_eq!(Ok(None), p.parse_dict());
        }

        // skip non-empty parameter
        {
            let mut p = Parser::new("a=3;f=999;g=1.23".as_bytes());

            assert_eq!(Ok(Some(("a", Value::Integer(3)))), p.parse_dict());
            assert_eq!(Ok(None), p.parse_dict());
        }

        // skip boolean parameter
        {
            let mut p = Parser::new("a=3;f".as_bytes());

            assert_eq!(Ok(Some(("a", Value::Integer(3)))), p.parse_dict());
            assert_eq!(Ok(None), p.parse_dict());
        }

        // skip inner list
        {
            let mut p = Parser::new("a=(1 2 3) , b=3".as_bytes());

            assert_eq!(Ok(Some(("a", Value::InnerList))), p.parse_dict());
            assert_eq!(Ok(Some(("b", Value::Integer(3)))), p.parse_dict());
            assert_eq!(Ok(None), p.parse_dict());
        }

        // skip inner list with parameter
        {
            let mut p = Parser::new("a=(1 2 3);f=a;g=b , b=3".as_bytes());

            assert_eq!(Ok(Some(("a", Value::InnerList))), p.parse_dict());
            assert_eq!(Ok(Some(("b", Value::Integer(3)))), p.parse_dict());
            assert_eq!(Ok(None), p.parse_dict());
        }

        // skip inner list with boolean parameter
        {
            let mut p = Parser::new("a=(1 2 3);f;g , b=3".as_bytes());

            assert_eq!(Ok(Some(("a", Value::InnerList))), p.parse_dict());
            assert_eq!(Ok(Some(("b", Value::Integer(3)))), p.parse_dict());
            assert_eq!(Ok(None), p.parse_dict());
        }

        // skip inner list but read parameter
        {
            let mut p = Parser::new("a=(1 2 3);f;g , b=3".as_bytes());

            assert_eq!(Ok(Some(("a", Value::InnerList))), p.parse_dict());
            assert_eq!(Ok(Some(("f", Value::Bool(true)))), p.parse_param());
            assert_eq!(Ok(Some(("g", Value::Bool(true)))), p.parse_param());
            assert_eq!(Ok(None), p.parse_param());
            assert_eq!(Ok(Some(("b", Value::Integer(3)))), p.parse_dict());
            assert_eq!(Ok(None), p.parse_dict());
        }

        // skip inner list item parameter
        {
            let mut p = Parser::new("a=(1;foo=100 2;bar)".as_bytes());

            assert_eq!(Ok(Some(("a", Value::InnerList))), p.parse_dict());
            assert_eq!(Ok(Some(Value::Integer(1))), p.parse_inner_list());
            assert_eq!(Ok(Some(Value::Integer(2))), p.parse_inner_list());
            assert_eq!(Ok(None), p.parse_inner_list());
            assert_eq!(Ok(None), p.parse_dict());
        }
    }

    #[test]
    fn parse_list_skip() {
        // skip empty parameter
        {
            let mut p = Parser::new("a".as_bytes());

            assert_eq!(Ok(Some(Value::Token(0..1))), p.parse_list());
            assert_eq!(Ok(None), p.parse_list());
        }

        // skip non-empty parameter
        {
            let mut p = Parser::new("a;fff=1;ggg=9".as_bytes());

            assert_eq!(Ok(Some(Value::Token(0..1))), p.parse_list());
            assert_eq!(Ok(None), p.parse_list());
        }

        // skip inner list
        {
            let mut p = Parser::new("(1 2 3) , 333".as_bytes());

            assert_eq!(Ok(Some(Value::InnerList)), p.parse_list());
            assert_eq!(Ok(Some(Value::Integer(333))), p.parse_list());
            assert_eq!(Ok(None), p.parse_list());
        }

        // skip inner list with parameter
        {
            let mut p = Parser::new("(1 2 3);f=a;g=b , 333".as_bytes());

            assert_eq!(Ok(Some(Value::InnerList)), p.parse_list());
            assert_eq!(Ok(Some(Value::Integer(333))), p.parse_list());
            assert_eq!(Ok(None), p.parse_list());
        }

        // skip inner list with boolean parameter
        {
            let mut p = Parser::new("(1 2 3);f;g , 333".as_bytes());

            assert_eq!(Ok(Some(Value::InnerList)), p.parse_list());
            assert_eq!(Ok(Some(Value::Integer(333))), p.parse_list());
            assert_eq!(Ok(None), p.parse_list());
        }

        // skip inner list but read parameter
        {
            let mut p = Parser::new("(1 2 3);f;g , 333".as_bytes());

            assert_eq!(Ok(Some(Value::InnerList)), p.parse_list());
            assert_eq!(Ok(Some(("f", Value::Bool(true)))), p.parse_param());
            assert_eq!(Ok(Some(("g", Value::Bool(true)))), p.parse_param());
            assert_eq!(Ok(None), p.parse_param());
            assert_eq!(Ok(Some(Value::Integer(333))), p.parse_list());
            assert_eq!(Ok(None), p.parse_list());
        }

        // skip inner list item parameter
        {
            let mut p = Parser::new("(1;foo=100 2;bar)".as_bytes());

            assert_eq!(Ok(Some(Value::InnerList)), p.parse_list());
            assert_eq!(Ok(Some(Value::Integer(1))), p.parse_inner_list());
            assert_eq!(Ok(Some(Value::Integer(2))), p.parse_inner_list());
            assert_eq!(Ok(None), p.parse_inner_list());
            assert_eq!(Ok(None), p.parse_list());
        }
    }
}
