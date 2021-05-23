#![cfg_attr(not(feature = "use-std"), no_std)]

/// Write trait to use with Encoder
pub trait Write {
    type Error;

    /// Write a single byte.
    fn write(&mut self, byte: u8) -> Result<(), Self::Error>;
}

/// Streaming encoder
pub struct Encoder<W: Write> {
    w: W,
    run: u8,
    repeat_run: u8,
    last_char: u8,
}

impl<W: Write> Encoder<W> {
    /// Create a new encoder with the given writer.
    pub fn new(w: W) -> Self {
        Self { w, run: 1, repeat_run: 0, last_char: 0 }
    }

    /// Mutably borrow the inner writer.
    pub fn writer(&mut self) -> &mut W {
        &mut self.w
    }

    fn write_fixing_zeroes(&mut self, byte: u8) -> Result<(), W::Error> {
        match (byte == 0, self.run) {
            (true, run) => {
                self.w.write(run)?;
                self.run = 1;
            }
            (false, 126) => {
                self.w.write(126)?;
                self.w.write(byte)?;
                self.run = 2;
            }
            (false, n) => {
                assert!(n < 126);
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
                self.write_fixing_zeroes(self.last_char)?;
                self.last_char = byte;

                // I'm not sure if this is possible, maybe when next char is a zero and we just wrote it?
                // Assert for now just to see if I hit this in testing
                self.repeat_run = 1;

                Ok(())
            }
            (n, false) => {
                self.write_fixing_zeroes(self.last_char)?;
                self.write_fixing_zeroes(0x80 | self.repeat_run)?;

                self.last_char = byte;
                self.repeat_run = 1;
                Ok(())

            }
            (127, true) => {
                self.write_fixing_zeroes(self.last_char)?;
                self.write_fixing_zeroes(0x80 | 0x7F)?;
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
        let mut needs_term = if self.repeat_run > 0 {
            self.write_fixing_zeroes(self.last_char)?;
            self.last_char != 0x00
        } else {
            true
        };

        if self.repeat_run > 1 {
            self.write_fixing_zeroes(0x80 | self.repeat_run)?;
            needs_term = true;
        }

        if needs_term {
            self.w.write(self.run)?;
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
