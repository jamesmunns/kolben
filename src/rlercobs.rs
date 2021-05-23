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
        Self { w, run: 1, repeat_run: 0, last_char: 0 }
    }

    /// Mutably borrow the inner writer.
    pub fn writer(&mut self) -> &mut W {
        &mut self.w
    }

    fn write_zero_sigil(&mut self, emit: bool) -> Result<(), W::Error> {
        assert!(self.run < 64);
        assert!(self.run != 0);

        let emit = if emit { 0b0_1_000000 } else { 0b0_0_000000 };
        self.w.write(self.run | emit)?;
        self.run = 1;
        Ok(())
    }

    fn write_repeat_sigil(&mut self, repeats: u16) -> Result<u16, W::Error> {
        assert!(repeats >= 2);

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

        let flag = if flag {
            0b0_000_1_000
        } else {
            0b0_000_0_000
        };

        let data = 0b1_000_0_000 | (rpt_val << 4) | flag | self.run;

        println!("{}, {}, {:08b}", repeats, removed, data);

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
        match (self.repeat_run, self.last_char == byte) {
            (0, _) => {
                // Store the byte in case there are duplicates, don't push
                // anything yet
                self.last_char = byte;
                self.repeat_run = 1;
                Ok(())
            }
            (1, false) => {
                self.write_data_byte(self.last_char)?;
                self.last_char = byte;
                self.repeat_run = 1;

                Ok(())
            }
            (_, false) => {
                self.write_data_byte(self.last_char)?;
                while self.repeat_run > 1 {
                    let taken = self.write_repeat_sigil(self.repeat_run)?;
                    println!("{}, {}", self.repeat_run, taken);
                    assert!(self.repeat_run >= taken);
                    self.repeat_run -= taken;
                }
                if self.repeat_run != 0 {
                    self.write_data_byte(self.last_char)?;
                }

                self.last_char = byte;
                self.repeat_run = 1;
                Ok(())

            }
            (u16::MAX, true) => {
                self.write_data_byte(self.last_char)?;
                self.write_repeat_sigil(u16::MAX)?;
                self.repeat_run = 0;
                Ok(())
            }
            (_, true) => {
                self.repeat_run += 1;
                Ok(())
            }
        }
    }

    /// Finish encoding a message.
    ///
    /// This does NOT write a `0x00` separator byte, you must write it yourself
    /// if you so desire.
    pub fn end(&mut self) -> Result<(), W::Error> {
        println!("End! {:?}", self);
        let needs_term = match self.repeat_run {
            0 => {
                self.run > 0
            }
            1 => {
                self.write_data_byte(self.last_char)?;
                self.last_char != 0
            }
            _ => {
                self.write_data_byte(self.last_char)?;

                while self.repeat_run > 1 {
                    let taken = self.write_repeat_sigil(self.repeat_run)?;
                    println!("Yanking {}", taken);
                    self.repeat_run -= taken;
                }

                assert!(self.repeat_run <= 1);

                if self.repeat_run != 0 {
                    println!("emitting one for the road");
                    self.write_data_byte(self.last_char)?;
                    self.last_char != 0
                } else {
                    false
                }
            }
        };

        if needs_term {
            println!("brrt term");
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
            println!("[{}]", byte);
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

/// Decode a full message.
///
/// `data` must be a full reverse-COBS encoded message. Decoding partial
/// messages is not possible. `data` must NOT include any `0x00` separator byte.
#[cfg(feature = "use-std")]
pub fn decode(data: &[u8]) -> Result<Vec<u8>, MalformedError> {
    let mut res = vec![0; data.len()];
    let mut dp = res.len();
    let mut rp = res.len();

    while dp != 0 {
        let n = data[dp - 1] as usize;
        if n == 0 {
            return Err(MalformedError);
        }

        if n != 255 {
            // push a 0
            rp -= 1;
        }

        if dp < n {
            return Err(MalformedError);
        }
        res[rp + 1 - n..rp].copy_from_slice(&data[dp - n..dp - 1]);
        rp -= n - 1;
        dp -= n;
    }

    // Remove extra zero
    res.pop();

    // Remove unused space at the beginning
    res.drain(0..rp);

    Ok(res)
}
