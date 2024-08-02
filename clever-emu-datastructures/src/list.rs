use allocator_api2::alloc::{Allocator, Global};

use core::alloc::Layout;
use core::ptr::NonNull;

pub struct Node<T> {
    val: T,
    next: Option<NonNull<Self>>,
    prev: Option<NonNull<Self>>,
}

pub struct RawHandle<T>(NonNull<Node<T>>);

impl<T> Copy for RawHandle<T> {}

impl<T> Clone for RawHandle<T> {
    fn clone(&self) -> Self {
        *self
    }
}

pub struct LinkedList<T, A: Allocator = Global> {
    first: Option<NonNull<Node<T>>>,
    last: Option<NonNull<Node<T>>>,
    len: usize,
    alloc: A,
}

impl<T, A: Allocator> Drop for LinkedList<T, A> {
    fn drop(&mut self) {
        let mut elems = self.first;

        while let Some(node) = elems {
            let ptr = node.as_ptr();
            let val = unsafe { core::ptr::addr_of_mut!((*ptr).val) };
            unsafe {
                core::ptr::drop_in_place(val);
            }
            elems = unsafe { (*ptr).next };
            let layout = Layout::new::<Node<T>>();
            unsafe {
                self.alloc.deallocate(node.cast(), layout);
            }
        }
    }
}

impl<T> LinkedList<T> {
    pub const fn new() -> Self {
        Self::new_in(Global)
    }
}

impl<T, A: Allocator> LinkedList<T, A> {
    pub const fn new_in(alloc: A) -> Self {
        Self {
            first: None,
            last: None,
            len: 0,
            alloc,
        }
    }

    pub fn first(&self) -> Option<&T> {
        self.first.map(|s| unsafe { s.as_ref() }).map(|n| &n.val)
    }
    pub fn last(&self) -> Option<&T> {
        self.last.map(|s| unsafe { s.as_ref() }).map(|n| &n.val)
    }

    pub fn first_mut(&mut self) -> Option<&mut T> {
        self.first
            .map(|mut s| unsafe { s.as_mut() })
            .map(|n| &mut n.val)
    }
    pub fn last_mut(&mut self) -> Option<&mut T> {
        self.last
            .map(|mut s| unsafe { s.as_mut() })
            .map(|n| &mut n.val)
    }

    pub fn push_back_handle(&mut self, x: T) -> RawHandle<T> {
        let layout = Layout::new::<Node<T>>();
        let mut node = self
            .alloc
            .allocate(layout)
            .unwrap_or_else(|_| std::alloc::handle_alloc_error(layout))
            .cast::<Node<T>>();

        self.len = self
            .len
            .checked_add(1)
            .expect("Cannot exceed usize::MAX elements");
        unsafe {
            core::ptr::addr_of_mut!((*node.as_ptr()).val).write(x);
        }
        if let Some(mut back) = self.last {
            unsafe {
                node.as_mut().prev = Some(back);
            }
            unsafe {
                back.as_mut().next = Some(node);
            }
        } else {
            self.first = Some(node);
            self.last = Some(node);
        }

        RawHandle(node)
    }

    pub fn push_front_handle(&mut self, x: T) -> RawHandle<T> {
        let layout = Layout::new::<Node<T>>();
        let mut node = self
            .alloc
            .allocate(layout)
            .unwrap_or_else(|_| std::alloc::handle_alloc_error(layout))
            .cast::<Node<T>>();

        self.len = self
            .len
            .checked_add(1)
            .expect("Cannot exceed usize::MAX elements");
        unsafe {
            core::ptr::addr_of_mut!((*node.as_ptr()).val).write(x);
        }
        if let Some(mut front) = self.first {
            unsafe {
                node.as_mut().next = Some(front);
            }
            unsafe {
                front.as_mut().prev = Some(node);
            }
        } else {
            self.first = Some(node);
            self.last = Some(node);
        }

        RawHandle(node)
    }

    pub fn push_back(&mut self, x: T) {
        self.push_back_handle(x);
    }

    pub fn push_front(&mut self, x: T) {
        self.push_front_handle(x);
    }

    pub fn pop_back(&mut self) -> Option<T> {
        if let Some(back) = self.last {
            self.len -= 1;
            let val = unsafe { core::ptr::read(core::ptr::addr_of!((*back.as_ptr()).val)) };

            let prev = unsafe { (*back.as_ptr()).prev };
            unsafe {
                self.alloc.deallocate(back.cast(), Layout::new::<Node<T>>());
            }

            self.last = prev;
            if let Some(mut prev) = prev {
                unsafe {
                    prev.as_mut().next = None;
                }
            } else {
                self.first = None;
            }
            Some(val)
        } else {
            None
        }
    }

    pub fn pop_front(&mut self) -> Option<T> {
        if let Some(back) = self.first {
            self.len -= 1;
            let val = unsafe { core::ptr::read(core::ptr::addr_of!((*back.as_ptr()).val)) };

            let prev = unsafe { (*back.as_ptr()).prev };
            unsafe {
                self.alloc.deallocate(back.cast(), Layout::new::<Node<T>>());
            }

            self.first = prev;
            if let Some(mut prev) = prev {
                unsafe {
                    prev.as_mut().prev = None;
                }
            } else {
                self.last = None;
            }
            Some(val)
        } else {
            None
        }
    }

    unsafe fn unlink(&mut self, hdl: RawHandle<T>) {
        let node = hdl.0;
        let prev = unsafe { (*node.as_ptr()).prev };
        let next = unsafe { (*node.as_ptr()).next };
        if let Some(mut prev) = prev {
            unsafe {
                prev.as_mut().next = next;
            }
        } else {
            self.first = next;
        }

        if let Some(mut next) = next {
            unsafe {
                next.as_mut().prev = prev;
            }
        } else {
            self.last = prev;
        }
    }

    pub unsafe fn remove(&mut self, hdl: RawHandle<T>) -> T {
        self.unlink(hdl);
        let node = hdl.0;
        let val = unsafe { core::ptr::read(core::ptr::addr_of!((*node.as_ptr()).val)) };

        self.len -= 1;

        unsafe {
            self.alloc.deallocate(node.cast(), Layout::new::<Node<T>>());
        }
        val
    }

    /// Moves the node IDed by `hdl` to the back of the container.
    /// This does not invalidate `hdl` or any other handle.
    pub unsafe fn move_to_back(&mut self, hdl: RawHandle<T>) {
        self.unlink(hdl);

        let node = hdl.0;

        if let Some(mut last) = self.last.replace(node) {
            unsafe { last.as_mut().next = Some(node) }
        } else {
            self.first = Some(node);
        }
    }

    /// Moves the node IDed by `hdl` to the back of the container.
    /// This does not invalidate `hdl` or any other handle.
    pub unsafe fn move_to_front(&mut self, hdl: RawHandle<T>) {
        self.unlink(hdl);

        let node = hdl.0;

        if let Some(mut first) = self.first.replace(node) {
            unsafe { first.as_mut().prev = Some(node) }
        } else {
            self.last = Some(node);
        }
    }

    pub unsafe fn get(&self, hdl: RawHandle<T>) -> &T {
        unsafe { &hdl.0.as_ref().val }
    }

    pub unsafe fn get_mut(&mut self, mut hdl: RawHandle<T>) -> &mut T {
        unsafe { &mut hdl.0.as_mut().val }
    }
}
