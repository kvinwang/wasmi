use std::cell::RefCell;
use std::slice;

/// A byte buffer implementation.
///
/// # Note
///
/// This is less efficient than the byte buffer implementation that is
/// based on actual OS provided virtual memory but it is a safe fallback
/// solution fitting any platform.
#[derive(Debug)]
pub struct ByteBuffer {
    /// The pointer to the underlying byte buffer.
    ptr: *mut u8,
    /// The current length of the byte buffer.
    ///
    /// # Note
    ///
    /// - **Vec:** `vec.len()`
    /// - **Static:** The accessible subslice of the entire underlying static byte buffer.
    len: usize,
    /// The capacity of the current allocation.
    ///
    /// # Note
    ///
    /// - **Vec**: `vec.capacity()`
    /// - **Static:** The total length of the underlying static byte buffer.
    capacity: usize,
    /// The underlying JS array buffer.
    buffer: Option<js::JsArrayBuffer>,
}

// # Safety
//
// `ByteBuffer` is essentially an `enum`` of `Vec<u8>` or `&'static mut [u8]`.
// Both of them are `Send` so this is sound.
unsafe impl Send for ByteBuffer {}

std::thread_local! {
    static CURRENT_JS_CONTEXT: RefCell<Option<js::Context>> = RefCell::new(None);
}

pub fn with_js_context<T>(js_ctx: &js::Context, f: impl FnOnce() -> T) -> T {
    CURRENT_JS_CONTEXT.with(|ctx| {
        *ctx.borrow_mut() = Some(js_ctx.clone());
    });
    let v = f();
    CURRENT_JS_CONTEXT.with(|ctx| {
        *ctx.borrow_mut() = None;
    });
    v
}

fn current_js_context() -> js::Context {
    CURRENT_JS_CONTEXT.with(|ctx| ctx.borrow().clone().expect("no current JS context"))
}

impl ByteBuffer {
    /// Creates a new byte buffer with the given initial length.
    ///
    /// # Panics
    ///
    /// If there is not enough memory to initialize `initial_len` bytes.
    pub fn new(initial_len: usize) -> Self {
        log::debug!(target: "js::wasm", "allocating byte buffer with initial length {}", initial_len);
        let buffer = js::JsArrayBuffer::new(&current_js_context(), initial_len)
            .expect("failed to allocate memory");
        let ptr = buffer.as_ptr() as _;
        let len = initial_len;
        let capacity = len;
        Self {
            ptr,
            len,
            capacity,
            buffer: Some(buffer),
        }
    }

    /// Creates a new byte buffer with the given initial length.
    ///
    /// This will zero all the bytes in `buffer[0..initial_len`].
    ///
    /// # Panics
    ///
    /// If `initial_len` is greater than the length of `buffer`.
    pub fn new_static(buffer: &'static mut [u8], initial_len: usize) -> Self {
        assert!(initial_len <= buffer.len());
        buffer[..initial_len].fill(0x00_u8);
        Self {
            ptr: buffer.as_mut_ptr(),
            len: initial_len,
            capacity: buffer.len(),
            buffer: None,
        }
    }

    /// Grows the byte buffer to the given `new_size`.
    ///
    /// The newly added bytes will be zero initialized.
    ///
    /// # Panics
    ///
    /// - If the current size of the [`ByteBuffer`] is larger than `new_size`.
    /// - If backed by static buffer and `new_size` is larger than it's capacity.
    pub fn grow(&mut self, new_size: usize) {
        log::debug!(target: "js::wasm", "growing byte buffer from {} to {}", self.len(), new_size);
        assert!(new_size >= self.len());
        match &self.buffer {
            Some(buffer) => {
                let new_buffer = buffer.transfer(new_size).expect("failed to resize buffer");
                self.ptr = new_buffer.as_ptr() as _;
                self.len = new_size;
                self.capacity = new_size;
                self.buffer = Some(new_buffer);
            }
            None => {
                // Case: the byte buffer is backed by a `&'static [u8]`.
                if self.capacity < new_size {
                    panic!("cannot grow a byte buffer backed by `&'static mut [u8]` beyond its capacity")
                }
                let len = self.len();
                self.len = new_size;
                self.data_mut()[len..new_size].fill(0x00_u8);
            }
        }
    }

    /// Returns the length of the byte buffer in bytes.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns a shared slice to the bytes underlying to the byte buffer.
    pub fn data(&self) -> &[u8] {
        // # Safety
        //
        // The byte buffer is either backed by a `Vec<u8>` or a &'static [u8]`
        // which are both valid byte slices in the range `self.ptr[0..self.len]`.
        unsafe { slice::from_raw_parts(self.ptr, self.len) }
    }

    /// Returns an exclusive slice to the bytes underlying to the byte buffer.
    pub fn data_mut(&mut self) -> &mut [u8] {
        // # Safety
        //
        // The byte buffer is either backed by a `Vec<u8>` or a &'static [u8]`
        // which are both valid byte slices in the range `self.ptr[0..self.len]`.
        unsafe { slice::from_raw_parts_mut(self.ptr, self.len) }
    }

    pub fn js_buffer(&self) -> Option<&js::JsArrayBuffer> {
        self.buffer.as_ref()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_basic_allocation_deallocation() {
        let buffer = ByteBuffer::new(10);
        assert_eq!(buffer.len(), 10);
        // Dropping the buffer should not cause UB.
    }

    #[test]
    fn test_basic_data_manipulation() {
        let mut buffer = ByteBuffer::new(10);
        assert_eq!(buffer.len(), 10);
        let data = buffer.data(); // test we can read the data
        assert_eq!(data, &[0; 10]);
        let data = buffer.data_mut(); // test we can take a mutable reference to the data
        data[4] = 4; // test we can write to the data and it is not UB
        let data = buffer.data(); // test we can take a new reference to the data
        assert_eq!(data, &[0, 0, 0, 0, 4, 0, 0, 0, 0, 0]); // test we can read the data
                                                           // test drop is okay
    }

    #[test]
    fn test_static_buffer_initialization() {
        static mut BUF: [u8; 10] = [7; 10];
        let buf = unsafe { &mut *core::ptr::addr_of_mut!(BUF) };
        let mut buffer = ByteBuffer::new_static(buf, 5);
        assert_eq!(buffer.len(), 5);
        // Modifying the static buffer through ByteBuffer and checking its content.
        let data = buffer.data_mut();
        data[0] = 1;
        unsafe {
            assert_eq!(BUF[0], 1);
        }
    }

    #[test]
    fn test_growing_buffer() {
        let mut buffer = ByteBuffer::new(5);
        buffer.grow(10);
        assert_eq!(buffer.len(), 10);
        assert_eq!(buffer.data(), &[0; 10]);
    }

    #[test]
    fn test_growing_static() {
        static mut BUF: [u8; 10] = [7; 10];
        let buf = unsafe { &mut *core::ptr::addr_of_mut!(BUF) };
        let mut buffer = ByteBuffer::new_static(buf, 5);
        assert_eq!(buffer.len(), 5);
        assert_eq!(buffer.data(), &[0; 5]);
        buffer.grow(8);
        assert_eq!(buffer.len(), 8);
        assert_eq!(buffer.data(), &[0; 8]);
        buffer.grow(10);
        assert_eq!(buffer.len(), 10);
        assert_eq!(buffer.data(), &[0; 10]);
    }

    #[test]
    #[should_panic]
    fn test_static_buffer_overflow() {
        static mut BUF: [u8; 5] = [7; 5];
        let buf = unsafe { &mut *core::ptr::addr_of_mut!(BUF) };
        let mut buffer = ByteBuffer::new_static(buf, 5);
        buffer.grow(10); // This should panic.
    }
}
