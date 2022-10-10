//! General Purpose Input/Output driver.

use crate::registers::gpio_regs::{
    GpioRegisters, INTR, MASKED_OE_LOWER, MASKED_OE_UPPER, MASKED_OUT_LOWER, MASKED_OUT_UPPER,
};
use crate::registers::pinmux_regs::{PinmuxRegisters, DIO_PAD_ATTR};
use kernel::hil::gpio;
use kernel::utilities::cells::OptionalCell;
use kernel::utilities::registers::interfaces::{ReadWriteable, Readable, Writeable};
use kernel::utilities::registers::{Field, ReadWrite};
use kernel::utilities::StaticRef;

pub enum Pin {
    Pin0,
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
    pub const fn pin_to_filed(&self) -> Field<u32, INTR::Register> {
        match *self {
            Pin::Pin0 => INTR::GPIO_0,
            Pin::Pin1 => INTR::GPIO_1,
            Pin::Pin2 => INTR::GPIO_2,
            Pin::Pin3 => INTR::GPIO_3,
            Pin::Pin4 => INTR::GPIO_4,
            Pin::Pin5 => INTR::GPIO_5,
            Pin::Pin6 => INTR::GPIO_6,
            Pin::Pin7 => INTR::GPIO_7,
            Pin::Pin8 => INTR::GPIO_8,
            Pin::Pin9 => INTR::GPIO_9,
            Pin::Pin10 => INTR::GPIO_10,
            Pin::Pin11 => INTR::GPIO_11,
            Pin::Pin12 => INTR::GPIO_12,
            Pin::Pin13 => INTR::GPIO_13,
            Pin::Pin14 => INTR::GPIO_14,
            Pin::Pin15 => INTR::GPIO_15,
            Pin::Pin16 => INTR::GPIO_16,
            Pin::Pin17 => INTR::GPIO_17,
            Pin::Pin18 => INTR::GPIO_18,
            Pin::Pin19 => INTR::GPIO_19,
            Pin::Pin20 => INTR::GPIO_20,
            Pin::Pin21 => INTR::GPIO_21,
            Pin::Pin22 => INTR::GPIO_22,
            Pin::Pin23 => INTR::GPIO_23,
            Pin::Pin24 => INTR::GPIO_24,
            Pin::Pin25 => INTR::GPIO_25,
            Pin::Pin26 => INTR::GPIO_26,
            Pin::Pin27 => INTR::GPIO_27,
            Pin::Pin28 => INTR::GPIO_28,
            Pin::Pin29 => INTR::GPIO_29,
            Pin::Pin30 => INTR::GPIO_20,
            Pin::Pin31 => INTR::GPIO_31,
        }
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
    pin: Field<u32, INTR::Register>,
    client: OptionalCell<&'a dyn gpio::Client>,
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
            pin: pin.pin_to_filed(),
            client: OptionalCell::empty(),
        }
    }

    fn is_set<TReg: kernel::utilities::registers::RegisterLongName>(
        &self,
        reg: &ReadWrite<u32, TReg>,
    ) -> bool {
        self.pin.is_set(reg.get())
    }

    #[inline(always)]
    fn set_masked_out(&self, val: bool, pin: Field<u32, INTR::Register>) {
        let reg = self.gpio_registers;
        let shift = pin.shift;
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
    fn set_masked_oe(&self, val: bool, pin: Field<u32, INTR::Register>) {
        let reg = self.gpio_registers;
        let shift = pin.shift;
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
        if self.gpio_registers.intr_state.is_set(self.pin) {
            // Clear interupt (INTR_STATE has type rwi1c)
            self.gpio_registers.intr_state.write(self.pin.val(1));
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
        // TODO Add checks for all WRAL registers
        // TODO Please fix incorrect pad indexing.
        match mode {
            gpio::FloatingState::PullUp => {
                self.pinmux_registers.dio_pad_attr[self.pin.shift]
                    .write(DIO_PAD_ATTR::PULL_EN_0::SET + DIO_PAD_ATTR::PULL_SELECT_0::PULL_UP);
            }
            gpio::FloatingState::PullDown => {
                self.pinmux_registers.dio_pad_attr[self.pin.shift]
                    .write(DIO_PAD_ATTR::PULL_EN_0::SET + DIO_PAD_ATTR::PULL_SELECT_0::PULL_DOWN);
            }
            gpio::FloatingState::PullNone => {
                self.pinmux_registers.dio_pad_attr[self.pin.shift]
                    .write(DIO_PAD_ATTR::PULL_EN_0::CLEAR);
            }
        }
    }

    fn floating_state(&self) -> gpio::FloatingState {
        // TODO Please fix incorrect pad indexing.
        if self.pinmux_registers.dio_pad_attr[self.pin.shift].is_set(DIO_PAD_ATTR::PULL_EN_0) {
            return match self.pinmux_registers.dio_pad_attr[self.pin.shift]
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
                self.gpio_registers
                    .intr_ctrl_en_rising
                    .modify(self.pin.val(1));
                self.gpio_registers
                    .intr_ctrl_en_falling
                    .modify(self.pin.val(0));
            }
            gpio::InterruptEdge::FallingEdge => {
                self.gpio_registers
                    .intr_ctrl_en_rising
                    .modify(self.pin.val(0));
                self.gpio_registers
                    .intr_ctrl_en_falling
                    .modify(self.pin.val(1));
            }
            gpio::InterruptEdge::EitherEdge => {
                self.gpio_registers
                    .intr_ctrl_en_rising
                    .modify(self.pin.val(1));
                self.gpio_registers
                    .intr_ctrl_en_falling
                    .modify(self.pin.val(1));
            }
        }
        self.gpio_registers.intr_state.modify(self.pin.val(1));
        self.gpio_registers.intr_enable.modify(self.pin.val(1));
    }

    fn disable_interrupts(&self) {
        self.gpio_registers.intr_enable.modify(self.pin.val(0));
        // Clear any pending interrupt
        self.gpio_registers.intr_state.modify(self.pin.val(1))
    }

    fn is_pending(&self) -> bool {
        self.gpio_registers.intr_state.is_set(self.pin)
    }
}
