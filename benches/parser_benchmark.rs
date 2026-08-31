use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};

use sfparse::{Error, Parser, Value};

fn parser(data: &[u8]) {
    let mut p = Parser::new(data);

    loop {
        let Some((_, v)) = p.parse_dict().expect("not fail") else {
            break;
        };

        match v {
            Value::InnerList => loop {
                let Some(_) = p.parse_inner_list().expect("not fail") else {
                    break;
                };

                loop {
                    let Some(_) = p.parse_param().expect("not fail") else {
                        break;
                    };
                }
            },
            _ => (),
        };

        loop {
            let Some(_) = p.parse_param().expect("not fail") else {
                break;
            };
        }
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    let fixture = "bool_key, dict_key1=cakecafedeadbeefcafecake, dict_key2=123456785686457, dict_key3=(\"sfparse string\" :c2ZwYXJzZSBzdHJpbmc=:);param-key=rnfeaefpafmawefweafwea;param-key2=9999839, dict_key4=%\"abcdefghijklmn%20%20%20zzz\"";

    c.bench_with_input(
        BenchmarkId::new("parsing_dictionary", fixture),
        &fixture,
        move |bench, &input| {
            bench.iter(|| parser(input.as_bytes()));
        },
    );
}

#[derive(Debug)]
pub struct Priority {
    urgency: u8,
    incremental: bool,
}

impl Priority {
    pub const fn new(urgency: u8, incremental: bool) -> Self {
        Priority {
            urgency,
            incremental,
        }
    }
}

impl TryFrom<&[u8]> for Priority {
    type Error = Error;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        let mut p = Parser::new(value);
        let mut urgency: u8 = 0;
        let mut incremental: bool = false;

        loop {
            match p.parse_dict() {
                Ok(Some(("u", Value::Integer(n)))) => {
                    if !((0i64..=7i64).contains(&n)) {
                        return Err(Error::ParseError { index: 0 });
                    }

                    urgency = n as u8;
                }
                Ok(Some(("i", Value::Bool(v)))) => {
                    incremental = v;
                }
                Ok(None) => break,
                Ok(_) => (),
                Err(e) => return Err(e),
            }
        }

        Ok(Priority::new(urgency, incremental))
    }
}

fn priority_benchmark(c: &mut Criterion) {
    let fixture = "u=7,i";

    c.bench_with_input(
        BenchmarkId::new("parsing_priority", fixture),
        &fixture,
        move |bench, &input| {
            bench.iter(|| Priority::try_from(input.as_bytes()).expect("not fail"));
        },
    );
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
