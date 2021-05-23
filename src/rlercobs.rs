//! Run Length Encoded Reverse Cobs
//!
//! This works very similarly to `rcobs`, however the behavior of sigil bytes are
//! slightly changed.
//!
//! ## Sigils
//!
//! There are now four different kind of sigil bytes, defined by their two msbits:
//!
//! * `0b00` - **NOP sigil**.
//!     * This does not represent data in the stream, and only serves to keep the reverse chain linked
//!     * The remaining six bits encode the distance back to the previous sigil (1 <= n <= 63)
//! * `0b01` - **Zero sigil**.
//!     * This sigil represents a zero in the data stream, and has been replaced to preserve framing
//!     * The remaining six bits encode the distance back to the previous sigil (1 <= n <= 63)
//! * `0b10` - **Exponential Repeat sigil**.
//!     * This sigil is a directive to repeat the previous non-sigil character (or Zero sigil representing a data-zero) `2 ** n` times, where `3 <= n <= 10`.
//!     * If multiple repeats (exponential or linear) appear in a row, their repeating counts should be added together.
//!     * The remaining three bits encode the distance back to the previous sigil (1 <= n <= 7)
//! * `0b11` - **Linear Repeat sigil**.
//!     * This sigil is a directive to repeat the previous non-sigil character (or Zero sigil representing a data-zero) `n` times, where `1 <= n <= 7`.
//!     * If multiple repeats (exponential or linear) appear in a row, their repeating counts should be added together.
//!     * The remaining three bits encode the distance back to the previous sigil (1 <= n <= 7)
//!
//! All sigil types encode the number of bytes back until the next sigil, and all messages must end with a sigil.
//! This allows for decoding by walking the data stream backwards, which is done to preserve encoder simplicity.

#![cfg_attr(not(feature = "use-std"), no_std)]

/// Write trait to use with Encoder
pub trait Write {
    type Error;

    /// Write a single byte.
    fn write(&mut self, byte: u8) -> Result<(), Self::Error>;
}

/// Streaming encoder
#[derive(Debug)]
pub struct Encoder<W: Write + core::fmt::Debug> {
    w: W,
    run: u8,
    repeat_run: u16,
    last_char: u8,
}

impl<W: Write + core::fmt::Debug> Encoder<W> {
    /// Create a new encoder with the given writer.
    pub fn new(w: W) -> Self {
        Self {
            w,
            run: 1,
            repeat_run: 0,
            last_char: 0,
        }
    }

    /// Mutably borrow the inner writer.
    pub fn writer(&mut self) -> &mut W {
        &mut self.w
    }

    fn write_zero_sigil(&mut self, emit: bool) -> Result<(), W::Error> {
        let emit = if emit { 0b0_1_000000 } else { 0b0_0_000000 };
        self.w.write(self.run | emit)?;
        self.run = 1;
        Ok(())
    }

    fn write_repeat_sigil(&mut self, repeats: u16) -> Result<u16, W::Error> {
        // If we have a run longer than 7, we can't encode it in the
        // repeat sigil. Emit a nop sigil to fill the gap
        if self.run > 7 {
            self.write_zero_sigil(false)?;
        }

        let (rpt_val, removed, flag) = if repeats < 8 {
            (repeats as u8, repeats, true)
        } else {
            let repeats_pow = 15 - 3 - repeats.leading_zeros();
            let removed = 1 << (repeats_pow + 3);
            (repeats_pow as u8, removed, false)
        };

        let flag = if flag { 0b0_1_000_000 } else { 0b0_0_000_000 };

        let data = 0b1_000_0_000 | (rpt_val << 3) | flag | self.run;

        self.w.write(data)?;
        self.run = 1;
        Ok(removed)
    }

    fn write_data_byte(&mut self, byte: u8) -> Result<(), W::Error> {
        match (byte == 0, self.run) {
            (true, _) => {
                self.write_zero_sigil(true)?;
            }
            (false, n) if n >= 63 => {
                self.write_zero_sigil(false)?;
                self.w.write(byte)?;
                self.run = 2;
            }
            (false, _) => {
                self.w.write(byte)?;
                self.run += 1;
            }
        }
        Ok(())
    }

    /// Write a message byte.
    pub fn write(&mut self, byte: u8) -> Result<(), W::Error> {
        let set_repeat = match (self.repeat_run, self.last_char == byte) {
            // Nothing in the buffer, store the repeat char
            (0, _) => true,

            // Unrepeated byte in buffer, flush it and take the new repeat
            (1, false) => {
                self.write_data_byte(self.last_char)?;
                true
            }

            // Repeated byte in the buffer, flush it and take the new repeat
            (_, false) => {
                self.drain_repeat_char()?;
                true
            }

            // Max repeated condition, flush the repeat char
            (u16::MAX, true) => {
                self.drain_repeat_char()?;
                // Note: last char is retained, drain will reduce repeat_run to 0.
                // TODO: Optimization: this will "completely reset" the stored run, which
                // we don't technically need to do if we already flushed the real character.
                //
                // e.g. right now we do:
                // [data][repeat u16::MAX][data][repeat 5]
                //
                // when we could be doing:
                // [data][repeat u16::MAX][repeat 5]
                false
            }
            (_, true) => {
                self.repeat_run += 1;
                false
            }
        };

        if set_repeat {
            self.last_char = byte;
            self.repeat_run = 1;
        }

        Ok(())
    }

    fn drain_repeat_char(&mut self) -> Result<(), W::Error> {
        debug_assert!(self.repeat_run >= 2);

        self.write_data_byte(self.last_char)?;

        while self.repeat_run > 1 {
            let taken = self.write_repeat_sigil(self.repeat_run)?;
            self.repeat_run -= taken;
        }

        Ok(())
    }

    /// Finish encoding a message.
    ///
    /// This does NOT write a `0x00` separator byte, you must write it yourself
    /// if you so desire.
    pub fn end(&mut self) -> Result<(), W::Error> {
        let needs_term = match self.repeat_run {
            0 => self.run > 0,
            1 => {
                self.write_data_byte(self.last_char)?;
                self.last_char != 0
            }
            _ => {
                self.drain_repeat_char()?;
                false
            }
        };

        if needs_term {
            self.write_zero_sigil(false)?;
        }

        Ok(())
    }
}

/// Encode a full message.
///
/// Encodes a single message and returns it as a `Vec`. The returned data does
/// not include any `0x00` separator byte, you have to add it yourself.
///
/// This is a convenience function using [Encoder] internally. For streaming encoding, use [Encoder].
#[cfg(feature = "use-std")]
pub fn encode(data: &[u8]) -> Vec<u8> {
    #[derive(Debug)]
    struct VecWriter<'a>(&'a mut Vec<u8>);

    impl<'a> Write for VecWriter<'a> {
        type Error = std::convert::Infallible;
        fn write(&mut self, byte: u8) -> Result<(), Self::Error> {
            self.0.push(byte);
            Ok(())
        }
    }

    let mut res = Vec::new();
    let mut enc = Encoder::new(VecWriter(&mut res));
    for &b in data {
        enc.write(b).unwrap();
    }
    enc.end().unwrap();
    res
}

/// Error indicating the decoded data was malformed reverse-COBS.
#[cfg(feature = "use-std")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MalformedError;

#[derive(Debug, Clone, Copy)]
enum Node {
    Data(u8),
    Repeated((u8, u16)),
    Nop,
}

/// Decode a full message.
///
/// `data` must be a full rler-COBS encoded message. Decoding partial
/// messages is not possible. `data` must NOT include any `0x00` separator byte.
#[cfg(feature = "use-std")]
pub fn decode(data: &[u8]) -> Result<Vec<u8>, MalformedError> {
    let mut repeat: Option<u16> = None;
    let mut sig_dist = 0u8;
    let mut bytes_seen = 0usize;

    let noded = data
        .iter()
        .copied()
        .rev()
        .map(|b| {
            let node = {
                if sig_dist == 0 {
                    // look for sigil in this byte
                    match b & 0b1100_0000 {
                        0b0000_0000 => {
                            // Nop sigil
                            sig_dist = b & 0b0011_1111;
                            Node::Nop
                        }
                        0b0100_0000 => {
                            // Zero sigil
                            let (seen, out) = if let Some(rpt) = repeat.take() {
                                (rpt, Node::Repeated((0, rpt)))
                            } else {
                                (1, Node::Data(0))
                            };

                            bytes_seen += usize::from(seen);
                            sig_dist = b & 0b0011_1111;

                            out
                        }
                        0b1000_0000 => {
                            // Exponential repeat sigil
                            let rpt_pow = (b & 0b00_111_000) >> 3;
                            let new_rpt = 8 << rpt_pow;

                            if let Some(rpt) = repeat.take() {
                                repeat = Some(rpt + new_rpt);
                            } else {
                                repeat = Some(u16::from(new_rpt));
                            }

                            bytes_seen += usize::from(new_rpt);
                            sig_dist = b & 0b0000_0111;
                            Node::Nop
                        }
                        _filler_val => {
                            // Linear repeat sigil
                            let new_rpt = (b & 0b00_111_000) >> 3;

                            if let Some(rpt) = repeat.take() {
                                repeat = Some(rpt + u16::from(new_rpt));
                            } else {
                                repeat = Some(u16::from(new_rpt));
                            }

                            bytes_seen += usize::from(new_rpt);
                            sig_dist = b & 0b0000_0111;
                            Node::Nop
                        }
                    }
                } else {
                    bytes_seen += 1;
                    if let Some(rpt) = repeat.take() {
                        Node::Repeated((b, rpt))
                    } else {
                        Node::Data(b)
                    }
                }
            };
            sig_dist = sig_dist.checked_sub(1).unwrap();
            node
        })
        .collect::<Vec<Node>>();

    let mut out = Vec::with_capacity(bytes_seen);

    noded.into_iter().rev().for_each(|i| match i {
        Node::Data(b) => out.push(b),
        Node::Repeated((b, n)) => {
            for _ in 0..n {
                out.push(b);
            }
        }
        Node::Nop => {}
    });

    out.shrink_to_fit();

    Ok(out)
}
