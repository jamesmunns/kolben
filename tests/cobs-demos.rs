use insta;
use kolben::{cobs, rcobs, rlercobs};

#[test]
fn standard_cobs_vec() {
    let data = zeroes_every_n_with_val(0x20, 15, 200);
    let ser = cobs::encode_vec(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt);

    let data = oops_all_zeros(200);
    let ser = cobs::encode_vec(&data);
    let cobs_ser_fmt_zeroes = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt_zeroes);
}

#[test]
fn reverse_cobs_vec() {
    let data = zeroes_every_n_with_val(0x20, 15, 200);
    let ser = rcobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt);

    let data = oops_all_zeros(200);
    let ser = rcobs::encode(&data);
    let cobs_ser_fmt_zeroes = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt_zeroes);
}

#[test]
fn reverse_zcobs_vec() {
    let data = zeroes_every_n_with_val(0x20, 15, 200);
    let ser = rzcobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt);

    let data = oops_all_zeros(200);
    let ser = rzcobs::encode(&data);
    let cobs_ser_fmt_zeroes = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt_zeroes);

    let data = zeroes_every_n_with_val(0x20, 4, 200);
    let ser = rzcobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt);

    let data = zeroes_every_n_with_val(0x20, 31, 200);
    let ser = rzcobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt);
}

#[test]
fn rler_cobs_vec() {
    // 1
    let data = zeroes_every_n_with_val(0x20, 15, 200);
    let ser = rlercobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt);

    // 2
    let data = oops_all_zeros(200);
    let ser = rlercobs::encode(&data);
    let cobs_ser_fmt_zeroes = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt_zeroes);

    // 3
    let data = zeroes_every_n_with_val(0x20, 4, 200);
    let ser = rlercobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt);

    // 4
    let data = zeroes_every_n_with_val(0x20, 31, 200);
    let ser = rlercobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt);

    // 5
    let data = zeroes_every_n_with_val(0x20, 2, 200);
    let ser = rlercobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt);

    // 6
    let data = zeroes_every_n_with_val(0x20, 3, 200);
    let ser = rlercobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt);
}

#[test]
fn rler_cobs_roundtrip() {
    // 1
    let data = zeroes_every_n_with_val(0x20, 15, 200);
    let ser = rlercobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt);
    let data_out = rlercobs::decode(&ser).unwrap();
    assert_eq!(data, data_out);

    // 2
    let data = oops_all_zeros(200);
    let ser = rlercobs::encode(&data);
    let cobs_ser_fmt_zeroes = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt_zeroes);
    let data_out = rlercobs::decode(&ser).unwrap();
    assert_eq!(data, data_out);

    // 3
    let data = zeroes_every_n_with_val(0x20, 4, 200);
    let ser = rlercobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt);
    let data_out = rlercobs::decode(&ser).unwrap();
    assert_eq!(data, data_out);

    // 4
    let data = zeroes_every_n_with_val(0x20, 31, 200);
    let ser = rlercobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt);
    let data_out = rlercobs::decode(&ser).unwrap();
    assert_eq!(data, data_out);

    // 5
    let data = zeroes_every_n_with_val(0x20, 2, 200);
    let ser = rlercobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt);
    let data_out = rlercobs::decode(&ser).unwrap();
    assert_eq!(data, data_out);

    // 6
    let data = zeroes_every_n_with_val(0x20, 3, 200);
    let ser = rlercobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(cobs_ser_fmt);
    let data_out = rlercobs::decode(&ser).unwrap();
    assert_eq!(data, data_out);
}

#[test]
fn rler_baskervilles() {
    use std::io::Read;
    let mut buf = String::new();
    let mut file = std::fs::File::open("./tests/hound-of-the-baskervilles.txt").unwrap();
    file.read_to_string(&mut buf).unwrap();

    let ser = rlercobs::encode(buf.as_bytes());
    let cobs_ser_fmt = &format_byte_array(&ser);
    insta::assert_display_snapshot!(cobs_ser_fmt);
}

#[test]
fn rler_baskervilles_nulls() {
    use std::io::Read;
    let mut buf = String::new();
    let mut file = std::fs::File::open("./tests/hound-of-the-baskervilles.txt").unwrap();
    file.read_to_string(&mut buf).unwrap();

    let mut dbuf = buf.into_bytes();
    dbuf.iter_mut().for_each(|i| {
        if *i == b' ' {
            *i = 0;
        }
    });
    let ser = rlercobs::encode(&dbuf);
    let cobs_ser_fmt = &format_byte_array(&ser);
    insta::assert_display_snapshot!(cobs_ser_fmt);
}

//////////////////////////////////////////
// Helper functions for creating data
//////////////////////////////////////////

fn format_byte_array(data: &[u8]) -> String {
    let lines = data
        .chunks(16)
        .map(|iter| {
            let x = iter
                .iter()
                .map(|b| format!("0x{:02X}", b))
                .collect::<Vec<_>>();
            x.join(", ")
        })
        .collect::<Vec<_>>();
    let mut all = lines.join("\n");
    all += &format!("\nBytes: {}", data.len());
    all
}

// Test data function generators
fn oops_all_zeros(ct: usize) -> Vec<u8> {
    all_same_value(0x00, ct)
}

fn all_same_value(val: u8, ct: usize) -> Vec<u8> {
    let mut vec = Vec::with_capacity(ct);
    for _ in 0..ct {
        vec.push(val);
    }
    vec
}

fn zeroes_every_n_with_val(val: u8, interval: usize, ct: usize) -> Vec<u8> {
    let mut starting = all_same_value(val, ct);
    starting.iter_mut().enumerate().for_each(|(i, b)| {
        if ((i + 1) % interval) == 0 {
            *b = 0;
        }
    });
    starting
}
