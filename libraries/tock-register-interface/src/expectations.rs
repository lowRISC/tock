extern crate std;
use std::collections::HashMap;
use std::ptr;
use std::string::String;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::vec::Vec;

use crate::fields::FieldValue;
use crate::{RegisterLongName, UIntLike};

/// The `Expectable` trait supplies all of the functions needed for
/// configuring and checking register read/write expectations during
/// tests.
///
/// The implementor need only supply `get_inner` and `get_inner_mut`.
pub trait Expectable {
    type T: UIntLike;
    type R: RegisterLongName;

    /// Returns a reference to the `RegisterInner` for tracking expectations.
    fn get_inner(&self) -> &RegisterInner;

    /// Returns a reference to the `RegisterInner` for tracking expectations.
    fn get_inner_mut(&mut self) -> &mut RegisterInner;

    /// Adds a read expectation to the sequencer.
    fn expect_read(&self, field: FieldValue<Self::T, Self::R>) {
        let inner = self.get_inner();
        let reg = ptr::addr_of!(inner.name) as usize;
        Sequencer::expect_read(inner.sequencer, reg, inner.name, field.value.as_u64());
    }

    /// Checks a register read against the current position in the sequencer.
    fn check_read(&self) -> Self::T {
        let inner = self.get_inner();
        let reg = ptr::addr_of!(inner.name) as usize;
        let mut s = Sequencer::get(inner.sequencer);
        match s.sequence.get(s.position) {
            Some(Operation::Modify(r, n, _)) => {
                assert!(
                    *r == reg,
                    "{}",
                    s.error(&std::format!(
                        "Expected to modify {:?}, but read from {:?} instead",
                        n,
                        inner.name
                    ))
                );
                // Keep the sequencer at this position as we expect a write to follow.
                Self::T::zero()
            }
            Some(Operation::Read(r, n, v)) => {
                assert!(
                    *r == reg,
                    "{}",
                    s.error(&std::format!(
                        "Expected to read from {:?}, but read from {:?} instead",
                        n,
                        inner.name
                    ))
                );
                s.position += 1;
                Self::T::from_u64(*v)
            }
            Some(Operation::Write(_, n, v)) => {
                assert!(
                    false,
                    "{}",
                    s.error(&std::format!(
                        "Expected to write {:#x} to {:?}, but read from {:?} instead",
                        v,
                        n,
                        inner.name
                    ))
                );
                unreachable!();
            }
            _ => {
                assert!(
                    false,
                    "{}",
                    s.error(&std::format!("No expectation at position {}", s.position))
                );
                unreachable!();
            }
        }
    }

    /// Adds a write expectation to the sequencer.
    fn expect_write(&self, field: FieldValue<Self::T, Self::R>) {
        let inner = self.get_inner();
        let reg = ptr::addr_of!(inner.name) as usize;
        Sequencer::expect_write(inner.sequencer, reg, inner.name, field.value.as_u64());
    }

    /// Checks a register write against the current position in the sequencer.
    fn check_write(&self, val: Self::T) {
        let val = val.as_u64();
        let inner = self.get_inner();
        let reg = ptr::addr_of!(inner.name) as usize;
        let mut s = Sequencer::get(inner.sequencer);
        match s.sequence.get(s.position) {
            Some(Operation::Modify(r, n, v)) => {
                assert!(
                    *r == reg,
                    "{}",
                    s.error(&std::format!(
                        "Expected to modify {:?}, but wrote {:?} instead",
                        n,
                        inner.name
                    ))
                );
                assert!(
                    *v == val,
                    "{}",
                    s.error(&std::format!(
                        "Expected to modify {:?} with {:#x}, but wrote {:#x} instead",
                        n,
                        val,
                        *v
                    ))
                );
                s.position += 1;
            }
            Some(Operation::Write(r, n, v)) => {
                assert!(
                    *r == reg,
                    "{}",
                    s.error(&std::format!(
                        "Expected to write {:?}, but wrote {:?} instead",
                        n,
                        inner.name
                    ))
                );
                assert!(
                    *v == val,
                    "{}",
                    s.error(&std::format!(
                        "Expected to write {:#x} to {:?}, but wrote {:#x} instead",
                        val,
                        n,
                        *v
                    ))
                );
                s.position += 1;
            }
            Some(Operation::Read(_, n, _)) => {
                assert!(
                    false,
                    "{}",
                    s.error(&std::format!(
                        "Expected to read from {:?}, but wrote {:?} instead",
                        n,
                        inner.name
                    ))
                );
            }
            _ => {
                assert!(
                    false,
                    "{}",
                    s.error(&std::format!("No expectation at position {}", s.position))
                );
            }
        }
    }

    /// Adds a modify expectation to the sequencer.
    fn expect_modify(&self, field: FieldValue<Self::T, Self::R>) {
        let inner = self.get_inner();
        let reg = ptr::addr_of!(inner.name) as usize;
        Sequencer::expect_modify(inner.sequencer, reg, inner.name, field.value.as_u64());
    }
}

/// The `ExpectableInit` trait assists with initializing the macro-generated registers struct.
pub trait ExpectableInit {
    fn init(&mut self, sequencer: usize, name: &'static str);
}

impl<T: Expectable> ExpectableInit for T {
    // Initialize a single `Expectable` struct.
    fn init(&mut self, sequencer: usize, name: &'static str) {
        Sequencer::inc_ref(sequencer);
        let inner = self.get_inner_mut();
        inner.sequencer = sequencer;
        inner.name = name;
    }
}

impl<T: Expectable, const N: usize> ExpectableInit for [T; N] {
    // Initialize an array of `Expectable` structs.
    fn init(&mut self, sequencer: usize, name: &'static str) {
        for i in 0..N {
            self[i].init(sequencer, name);
        }
    }
}

impl<const N: usize> ExpectableInit for [u8; N] {
    // Initialize an array of u8.  This do-nothing implementation
    // is needed to accomodate padding used by some register definitions.
    fn init(&mut self, _sequencer: usize, _name: &'static str) {}
}

/// The `Operation` enum represents a register operation in the sequencer.
/// Each operation encodes an opaque idenfier for the register, the name
/// of the register and the value to be read or written.
#[derive(Debug)]
enum Operation {
    Read(usize, &'static str, u64),
    Modify(usize, &'static str, u64),
    Write(usize, &'static str, u64),
}

/// The `Sequencer` holds a list of expected operations to be performed
/// on a set of registers.
#[derive(Default, Debug)]
pub struct Sequencer {
    sequence: Vec<Operation>,
    position: usize,
    refcount: isize,
}

// We keep a global list of sequencers so we don't have to track references,
// mutabiltiy or lifetimes within the register structures.
#[thread_local]
static mut SEQUENCERS: Option<HashMap<usize, Sequencer>> = None;
// We use an atomic integer to give every sequencer a unique ID.
static ID: AtomicUsize = AtomicUsize::new(1);

impl Sequencer {
    fn _get() -> &'static mut HashMap<usize, Sequencer> {
        unsafe { SEQUENCERS.get_or_insert_with(|| HashMap::new()) }
    }
    fn get(n: usize) -> &'static mut Sequencer {
        let s = Self::_get();
        s.get_mut(&n).unwrap()
    }

    /// Creates a new sequencer and returns its ID.
    pub fn new() -> usize {
        let s = Self::_get();
        let id = ID.fetch_add(1, Ordering::SeqCst);
        s.insert(id, Sequencer::default());
        id
    }

    fn expect_read(n: usize, reg: usize, name: &'static str, value: u64) {
        let inst = Self::get(n);
        inst.sequence.push(Operation::Read(reg, name, value));
    }

    fn expect_modify(n: usize, reg: usize, name: &'static str, value: u64) {
        let inst = Self::get(n);
        inst.sequence.push(Operation::Modify(reg, name, value));
    }

    fn expect_write(n: usize, reg: usize, name: &'static str, value: u64) {
        let inst = Self::get(n);
        inst.sequence.push(Operation::Write(reg, name, value));
    }

    fn inc_ref(n: usize) {
        let inst = Self::get(n);
        inst.refcount += 1;
    }

    fn dec_ref(n: usize) {
        let s = Self::_get();
        let mut delete = false;
        if let Some(inst) = s.get_mut(&n) {
            inst.refcount -= 1;
            if inst.refcount <= 0 {
                delete = true;
                if inst.position != inst.sequence.len() {
                    assert!(false, "{}", inst.error("Sequence incomplete"));
                }
            }
        }
        if delete {
            s.remove(&n);
        }
    }

    // Prints the entire sequence and notates the current position with
    // the supplied `msg`.
    fn error(&self, msg: &str) -> String {
        let mut error = Vec::new();
        error.push(String::from("Sequence:"));
        for (i, op) in self.sequence.iter().enumerate() {
            if i == self.position {
                error.push(std::format!("{:>3} >>>>> {:x?} {}", i, op, msg));
            } else {
                error.push(std::format!("{:>3}       {:x?}", i, op));
            }
        }
        error.join("\n")
    }
}

/// The `RegisterInner` struct provides the sequencer information used
/// to track expectations for that register.  Since we don't want to
/// carry a reference or worry about the mutability of the sequencer,
/// we carry an integer identifier of the sequencer.
pub struct RegisterInner {
    pub sequencer: usize,
    pub name: &'static str,
}

impl Default for RegisterInner {
    fn default() -> Self {
        Self {
            sequencer: 0,
            name: "Unknown Register",
        }
    }
}

impl Drop for RegisterInner {
    fn drop(&mut self) {
        Sequencer::dec_ref(self.sequencer);
    }
}
