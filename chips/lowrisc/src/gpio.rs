//! General Purpose Input/Output driver.

use crate::registers::gpio_regs::{
    GpioRegisters, MASKED_OE_LOWER, MASKED_OE_UPPER, MASKED_OUT_LOWER, MASKED_OUT_UPPER,
};
use crate::registers::pinmux_regs::{PinmuxRegisters, DIO_PAD_ATTR};
use kernel::hil::gpio;
use kernel::utilities::cells::OptionalCell;
use kernel::utilities::registers::interfaces::{Readable, Writeable};
use kernel::utilities::registers::ReadWrite;
use kernel::utilities::StaticRef;

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum Pin {
    Pin0 = 0,
    Pin1,
    Pin2,
    Pin3,
    Pin4,
    Pin5,
    Pin6,
    Pin7,
    Pin8,
    Pin9,
    Pin10,
    Pin11,
    Pin12,
    Pin13,
    Pin14,
    Pin15,
    Pin16,
    Pin17,
    Pin18,
    Pin19,
    Pin20,
    Pin21,
    Pin22,
    Pin23,
    Pin24,
    Pin25,
    Pin26,
    Pin27,
    Pin28,
    Pin29,
    Pin30,
    Pin31,
}

impl Pin {
    pub const fn mask(&self) -> u32 {
        1 << *self as u8
    }

    pub const fn shift(&self) -> u32 {
        *self as u32
    }
}

// TODO Important fact about GPIO implementation quality.
// The current implementation contains a fundamental error regarding the number and method
// of connecting the GPIO pins. For correct setting of floating state and value on padring GPIO pin
// should contain information about its type (MIO/DIO) and muxing matrix configurations.
// Please implement GPIO multiplexing according to following documentation:
// https://docs.opentitan.org/hw/top_earlgrey/ip/pinmux/doc/autogen/pinout_cw310/index.html
// https://docs.opentitan.org/hw/top_earlgrey/ip/pinmux/doc/autogen/pinout_asic/index.html
pub struct GpioPin<'a> {
    gpio_registers: StaticRef<GpioRegisters>,
    pinmux_registers: StaticRef<PinmuxRegisters>,
    client: OptionalCell<&'a dyn gpio::Client>,
    pin: Pin,
}

impl<'a> GpioPin<'a> {
    pub const fn new(
        gpio_base: StaticRef<GpioRegisters>,
        pinmux_base: StaticRef<PinmuxRegisters>,
        pin: Pin,
    ) -> GpioPin<'a> {
        GpioPin {
            gpio_registers: gpio_base,
            pinmux_registers: pinmux_base,
            client: OptionalCell::empty(),
            pin: pin,
        }
    }

    #[inline(always)]
    fn is_set<TReg: kernel::utilities::registers::RegisterLongName>(
        &self,
        reg: &ReadWrite<u32, TReg>,
    ) -> bool {
        (reg.get() & self.pin.mask()) != 0
    }

    #[inline(always)]
    fn modify<TReg: kernel::utilities::registers::RegisterLongName>(
        &self,
        reg: &ReadWrite<u32, TReg>,
        val: bool,
    ) {
        let bit = if val { 1u32 } else { 0u32 };
        reg.set((reg.get() & !self.pin.mask()) | (bit << self.pin.shift()));
    }

    #[inline(always)]
    fn set_masked_out(&self, val: bool, pin: Pin) {
        let reg = self.gpio_registers;
        let shift = pin.shift();
        let bit = if val { 1u32 } else { 0u32 };
        if shift < 16 {
            reg.masked_out_lower.write(
                MASKED_OUT_LOWER::DATA.val(bit << shift)
                    + MASKED_OUT_LOWER::MASK.val(1u32 << shift),
            );
        } else {
            let upper_shift = shift - 16;
            reg.masked_out_upper.write(
                MASKED_OUT_UPPER::DATA.val(bit << upper_shift)
                    + MASKED_OUT_UPPER::MASK.val(1u32 << upper_shift),
            );
        }
    }

    #[inline(always)]
    fn set_masked_oe(&self, val: bool, pin: Pin) {
        let reg = self.gpio_registers;
        let shift = pin.shift();
        let bit = if val { 1u32 } else { 0u32 };
        if shift < 16 {
            reg.masked_oe_lower.write(
                MASKED_OE_LOWER::DATA.val(bit << shift) + MASKED_OE_LOWER::MASK.val(1u32 << shift),
            );
        } else {
            let upper_shift = shift - 16;
            reg.masked_oe_upper.write(
                MASKED_OE_UPPER::DATA.val(bit << upper_shift)
                    + MASKED_OE_UPPER::MASK.val(1u32 << upper_shift),
            );
        }
    }

    pub fn handle_interrupt(&self) {
        if self.is_set(&self.gpio_registers.intr_state) {
            // Clear interupt (INTR_STATE has type rwi1c) by setting 1 in corect register bit.
            self.gpio_registers.intr_state.set(self.pin.mask());
            self.client.map(|client| {
                client.fired();
            });
        }
    }
}

impl gpio::Configure for GpioPin<'_> {
    fn configuration(&self) -> gpio::Configuration {
        match self.is_set(&self.gpio_registers.direct_oe) {
            true => gpio::Configuration::InputOutput,
            false => gpio::Configuration::Input,
        }
    }

    fn set_floating_state(&self, mode: gpio::FloatingState) {
        // TODO Add checks for all WARL registers.
        // TODO Please fix incorrect pad indexing.
        match mode {
            gpio::FloatingState::PullUp => {
                self.pinmux_registers.dio_pad_attr[self.pin as usize]
                    .write(DIO_PAD_ATTR::PULL_EN_0::SET + DIO_PAD_ATTR::PULL_SELECT_0::PULL_UP);
            }
            gpio::FloatingState::PullDown => {
                self.pinmux_registers.dio_pad_attr[self.pin as usize]
                    .write(DIO_PAD_ATTR::PULL_EN_0::SET + DIO_PAD_ATTR::PULL_SELECT_0::PULL_DOWN);
            }
            gpio::FloatingState::PullNone => {
                self.pinmux_registers.dio_pad_attr[self.pin as usize]
                    .write(DIO_PAD_ATTR::PULL_EN_0::CLEAR);
            }
        }
    }

    fn floating_state(&self) -> gpio::FloatingState {
        // TODO Please fix incorrect pad indexing.
        if self.pinmux_registers.dio_pad_attr[self.pin as usize].is_set(DIO_PAD_ATTR::PULL_EN_0) {
            return match self.pinmux_registers.dio_pad_attr[self.pin as usize]
                .read_as_enum(DIO_PAD_ATTR::PULL_SELECT_0)
            {
                Some(DIO_PAD_ATTR::PULL_SELECT_0::Value::PULL_UP) => gpio::FloatingState::PullUp,
                Some(DIO_PAD_ATTR::PULL_SELECT_0::Value::PULL_DOWN) => {
                    gpio::FloatingState::PullDown
                }
                None => gpio::FloatingState::PullNone,
            };
        }
        gpio::FloatingState::PullNone
    }

    fn deactivate_to_low_power(&self) {
        self.disable_input();
        self.disable_output();
    }

    fn make_output(&self) -> gpio::Configuration {
        self.set_masked_oe(true, self.pin);
        gpio::Configuration::InputOutput
    }

    fn disable_output(&self) -> gpio::Configuration {
        self.set_masked_oe(false, self.pin);
        gpio::Configuration::Input
    }

    fn make_input(&self) -> gpio::Configuration {
        self.configuration()
    }

    fn disable_input(&self) -> gpio::Configuration {
        self.configuration()
    }
}

impl gpio::Input for GpioPin<'_> {
    fn read(&self) -> bool {
        self.is_set(&self.gpio_registers.data_in)
    }
}

impl gpio::Output for GpioPin<'_> {
    fn toggle(&self) -> bool {
        let new_state = !self.is_set(&self.gpio_registers.direct_out);

        self.set_masked_out(new_state, self.pin);
        new_state
    }

    fn set(&self) {
        self.set_masked_out(true, self.pin);
    }

    fn clear(&self) {
        self.set_masked_out(false, self.pin);
    }
}

impl<'a> gpio::Interrupt<'a> for GpioPin<'a> {
    fn set_client(&self, client: &'a dyn gpio::Client) {
        self.client.set(client);
    }

    fn enable_interrupts(&self, mode: gpio::InterruptEdge) {
        match mode {
            gpio::InterruptEdge::RisingEdge => {
                self.modify(&self.gpio_registers.intr_ctrl_en_rising, true);
                self.modify(&self.gpio_registers.intr_ctrl_en_falling, false);
            }
            gpio::InterruptEdge::FallingEdge => {
                self.modify(&self.gpio_registers.intr_ctrl_en_rising, false);
                self.modify(&self.gpio_registers.intr_ctrl_en_falling, true);
            }
            gpio::InterruptEdge::EitherEdge => {
                self.modify(&self.gpio_registers.intr_ctrl_en_rising, true);
                self.modify(&self.gpio_registers.intr_ctrl_en_falling, true);
            }
        }
        self.gpio_registers.intr_state.set(self.pin.mask());
        self.modify(&self.gpio_registers.intr_enable, true);
    }

    fn disable_interrupts(&self) {
        self.modify(&self.gpio_registers.intr_enable, false);
        // Clear any pending interrupt
        self.gpio_registers.intr_state.set(self.pin.mask())
    }

    fn is_pending(&self) -> bool {
        self.is_set(&self.gpio_registers.intr_state)
    }
}
