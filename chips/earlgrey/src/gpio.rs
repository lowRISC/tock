//! GPIO instantiation.

use core::ops::{Index, IndexMut};

use kernel::utilities::StaticRef;
pub use lowrisc::gpio::GpioPin;
pub use lowrisc::gpio::Pin;
use lowrisc::registers::gpio_regs::GpioRegisters;
use lowrisc::registers::pinmux_regs::PinmuxRegisters;

pub const PADCTRL_BASE: StaticRef<PinmuxRegisters> =
    unsafe { StaticRef::new(0x4047_0000 as *const PinmuxRegisters) };

pub const GPIO0_BASE: StaticRef<GpioRegisters> =
    unsafe { StaticRef::new(0x4004_0000 as *const GpioRegisters) };

pub struct Port<'a> {
    pins: [GpioPin<'a>; 32],
}

impl<'a> Port<'a> {
    pub const fn new() -> Self {
        Self {
            pins: [
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin0),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin1),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin2),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin3),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin4),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin5),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin6),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin7),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin8),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin9),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin10),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin11),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin12),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin13),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin14),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin15),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin16),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin17),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin18),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin19),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin20),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin21),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin22),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin23),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin24),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin25),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin26),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin27),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin28),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin29),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin30),
                GpioPin::new(GPIO0_BASE, PADCTRL_BASE, Pin::Pin31),
            ],
        }
    }
}

impl<'a> Index<usize> for Port<'a> {
    type Output = GpioPin<'a>;

    fn index(&self, index: usize) -> &GpioPin<'a> {
        &self.pins[index]
    }
}

impl<'a> IndexMut<usize> for Port<'a> {
    fn index_mut(&mut self, index: usize) -> &mut GpioPin<'a> {
        &mut self.pins[index]
    }
}
