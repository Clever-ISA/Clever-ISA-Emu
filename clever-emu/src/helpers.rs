pub trait SplitOnceOwned: Sized {
    fn split_once_take(&mut self, pat: &str) -> Option<Self>;
    fn split_once_owned(mut self, pat: &str) -> Result<(Self, Self), Self> {
        match self.split_once_take(pat) {
            Some(val) => Ok((self, val)),
            None => Err(self),
        }
    }
}

impl SplitOnceOwned for String {
    fn split_once_take(&mut self, pat: &str) -> Option<Self> {
        if let Some(pos) = self.find(pat) {
            let mut new_str = Vec::new();

            let off = pos + pat.len();

            new_str.extend_from_slice(&self.as_bytes()[off..]);

            self.truncate(pos);

            Some(unsafe { String::from_utf8_unchecked(new_str) })
        } else {
            None
        }
    }
}
