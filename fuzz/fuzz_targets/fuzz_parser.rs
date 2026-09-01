#![no_main]

use arbitrary::Unstructured;
use libfuzzer_sys::fuzz_target;
use sfparse::{Error, Parser, Value};

fuzz_target!(|data: &[u8]| {
    let _ = parse_dict(data);
    let _ = parse_list(data);
});

fn parse_dict(data: &[u8]) -> Result<(), Error> {
    let mut p = Parser::new(data);
    let mut u = Unstructured::new(data);

    loop {
        match p.parse_dict()? {
            Some((_, Value::InnerList)) => {
                if u.arbitrary::<bool>().ok().unwrap_or(false) {
                    parse_inner_list(&mut p, &mut u)?;
                }

                if u.arbitrary::<bool>().ok().unwrap_or(false) {
                    parse_params(&mut p)?;
                }
            }
            Some(_) => {
                if u.arbitrary::<bool>().ok().unwrap_or(false) {
                    parse_params(&mut p)?;
                }
            }
            None => break Ok(()),
        }
    }
}

fn parse_list(data: &[u8]) -> Result<(), Error> {
    let mut p = Parser::new(data);
    let mut u = Unstructured::new(data);

    loop {
        match p.parse_list()? {
            Some(Value::InnerList) => {
                if u.arbitrary::<bool>().ok().unwrap_or(false) {
                    parse_inner_list(&mut p, &mut u)?;
                }

                if u.arbitrary::<bool>().ok().unwrap_or(false) {
                    parse_params(&mut p)?;
                }
            }
            Some(_) => {
                if u.arbitrary::<bool>().ok().unwrap_or(false) {
                    parse_params(&mut p)?;
                }
            }
            None => break Ok(()),
        }
    }
}

fn parse_params(p: &mut Parser) -> Result<(), Error> {
    loop {
        match p.parse_param()? {
            Some(_) => {}
            None => break Ok(()),
        }
    }
}

fn parse_inner_list(p: &mut Parser, u: &mut Unstructured) -> Result<(), Error> {
    loop {
        match p.parse_inner_list()? {
            Some(_) => {
                if u.arbitrary::<bool>().ok().unwrap_or(false) {
                    parse_params(p)?;
                }
            }
            None => break Ok(()),
        }
    }
}
