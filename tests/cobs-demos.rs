use kolben::{
    cobs,
    rcobs,
    rlercobs,
};
use insta;

#[test]
fn standard_cobs_vec() {
    let data = zeroes_every_n_with_val(0x20, 15, 200);
    let ser = cobs::encode_vec(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(
        cobs_ser_fmt
    );

    let data = oops_all_zeros(200);
    let ser = cobs::encode_vec(&data);
    let cobs_ser_fmt_zeroes = &format_byte_array(&ser);

    insta::assert_display_snapshot!(
        cobs_ser_fmt_zeroes
    );
}

#[test]
fn reverse_cobs_vec() {
    let data = zeroes_every_n_with_val(0x20, 15, 200);
    let ser = rcobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(
        cobs_ser_fmt
    );

    let data = oops_all_zeros(200);
    let ser = rcobs::encode(&data);
    let cobs_ser_fmt_zeroes = &format_byte_array(&ser);

    insta::assert_display_snapshot!(
        cobs_ser_fmt_zeroes
    );
}

#[test]
fn reverse_zcobs_vec() {
    let data = zeroes_every_n_with_val(0x20, 15, 200);
    let ser = rzcobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(
        cobs_ser_fmt
    );

    let data = oops_all_zeros(200);
    let ser = rzcobs::encode(&data);
    let cobs_ser_fmt_zeroes = &format_byte_array(&ser);

    insta::assert_display_snapshot!(
        cobs_ser_fmt_zeroes
    );

    let data = zeroes_every_n_with_val(0x20, 4, 200);
    let ser = rzcobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(
        cobs_ser_fmt
    );

    let data = zeroes_every_n_with_val(0x20, 31, 200);
    let ser = rzcobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(
        cobs_ser_fmt
    );
}

#[test]
fn rler_cobs_vec() {
    let data = zeroes_every_n_with_val(0x20, 15, 200);
    let ser = rlercobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(
        cobs_ser_fmt
    );

    let data = oops_all_zeros(200);
    let ser = rlercobs::encode(&data);
    let cobs_ser_fmt_zeroes = &format_byte_array(&ser);

    insta::assert_display_snapshot!(
        cobs_ser_fmt_zeroes
    );

    let data = zeroes_every_n_with_val(0x20, 4, 200);
    let ser = rlercobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(
        cobs_ser_fmt
    );

    let data = zeroes_every_n_with_val(0x20, 31, 200);
    let ser = rlercobs::encode(&data);
    let cobs_ser_fmt = &format_byte_array(&ser);

    insta::assert_display_snapshot!(
        cobs_ser_fmt
    );
}

// 0x87
// 0b1000_0111

//////////////////////////////////////////
// Helper functions for creating data
//////////////////////////////////////////


fn format_byte_array(data: &[u8]) -> String {
    let lines = data.chunks(16).map(|iter| {
        let x = iter.iter().map(|b| format!("0x{:02X}", b)).collect::<Vec<_>>();
        x.join(", ")
    }).collect::<Vec<_>>();
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
