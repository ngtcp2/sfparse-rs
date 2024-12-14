# sfparse-rs

sfparse-rs is [RFC
9651](https://datatracker.ietf.org/doc/html/rfc9651) Structured Field
Values parser written in Rust.  It is the port of
[sfparse](https://github.com/ngtcp2/sfparse) written in C.

It is designed not to do any extra allocation, like allocating maps,
lists, and Strings, and do the minimal stuff to parse the input data.

```rust
use sfparse::{Parser, Value};

let mut urgency :i32 = 3;
let mut incremental = false;
let mut p = Parser::new("u=2, i".as_bytes());

loop {
    match p.parse_dict().unwrap() {
        None => break,
        Some(("u", Value::Integer(v))) if (0i64..=7i64).contains(&v) => urgency = v as i32,
        Some(("i", Value::Bool(v))) => incremental = v,
        _ => (),
    }
}

println!("urgency={urgency} incremental={incremental}");
```

## License

The MIT License

Copyright (c) 2024 sfparse-rs contributors
