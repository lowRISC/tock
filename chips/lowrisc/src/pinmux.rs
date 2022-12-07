//! Pinmux OpenTitan driver.

use core::convert::TryFrom;
use crate::registers::pinmux_regs::*;
use kernel::utilities::registers::interfaces::{Readable, Writeable, ReadWriteable};
use kernel::utilities::registers::ReadWrite;
use kernel::utilities::StaticRef;
use kernel::errorcode::ErrorCode;
use kernel::hil::gpio::FloatingState;

// Genral infomrmation about Pinmux Layout for cw310
// +----------+------------+-----------+-----------+----------+
// | IO_BANKS | Muxed Pads | DirectPad | ManulaPad | TotalPad |
// +----------+------------+-----------+-----------+----------+
// |    4     |      47    |     14    |     15    |     76   |
// +----------+------------+-----------+-----------+----------+

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum MioPeripheralInput {
  GpioGpio0 = 0,
  GpioGpio1 = 1,
  GpioGpio2 = 2,
  GpioGpio3 = 3,
  GpioGpio4 = 4,
  GpioGpio5 = 5,
  GpioGpio6 = 6,
  GpioGpio7 = 7,
  GpioGpio8 = 8,
  GpioGpio9 = 9,
  GpioGpio10 = 10,
  GpioGpio11 = 11,
  GpioGpio12 = 12,
  GpioGpio13 = 13,
  GpioGpio14 = 14,
  GpioGpio15 = 15,
  GpioGpio16 = 16,
  GpioGpio17 = 17,
  GpioGpio18 = 18,
  GpioGpio19 = 19,
  GpioGpio20 = 20,
  GpioGpio21 = 21,
  GpioGpio22 = 22,
  GpioGpio23 = 23,
  GpioGpio24 = 24,
  GpioGpio25 = 25,
  GpioGpio26 = 26,
  GpioGpio27 = 27,
  GpioGpio28 = 28,
  GpioGpio29 = 29,
  GpioGpio30 = 30,
  GpioGpio31 = 31,
  I2c0Sda = 32,
  I2c0Scl = 33,
  I2c1Sda = 34,
  I2c1Scl = 35,
  I2c2Sda = 36,
  I2c2Scl = 37,
  SpiHost1Sd0 = 38,
  SpiHost1Sd1 = 39,
  SpiHost1Sd2 = 40,
  SpiHost1Sd3 = 41,
  Uart0Rx = 42,
  Uart1Rx = 43,
  Uart2Rx = 44,
  Uart3Rx = 45,
  SpiDeviceTpmCsb = 46,
  FlashCtrlTck = 47,
  FlashCtrlTms = 48,
  FlashCtrlTdi = 49,
  SysrstCtrlAonAcPresent = 50,
  SysrstCtrlAonKey0In = 51,
  SysrstCtrlAonKey1In = 52,
  SysrstCtrlAonKey2In = 53,
  SysrstCtrlAonPwrbIn = 54,
  SysrstCtrlAonLidOpen = 55,
  UsbdevSense = 56,
}

#[derive(Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum MioPadInput {
  ConstantZero = 0,
  ConstantOne = 1,
  Ioa0 = 2,
  Ioa1 = 3,
  Ioa2 = 4,
  Ioa3 = 5,
  Ioa4 = 6,
  Ioa5 = 7,
  Ioa6 = 8,
  Ioa7 = 9,
  Ioa8 = 10,
  Iob0 = 11,
  Iob1 = 12,
  Iob2 = 13,
  Iob3 = 14,
  Iob4 = 15,
  Iob5 = 16,
  Iob6 = 17,
  Iob7 = 18,
  Iob8 = 19,
  Iob9 = 20,
  Iob10 = 21,
  Iob11 = 22,
  Iob12 = 23,
  Ioc0 = 24,
  Ioc1 = 25,
  Ioc2 = 26,
  Ioc3 = 27,
  Ioc4 = 28,
  Ioc5 = 29,
  Ioc6 = 30,
  Ioc7 = 31,
  Ioc8 = 32,
  Ioc9 = 33,
  Ioc10 = 34,
  Ioc11 = 35,
  Ioc12 = 36,
  Ior0 = 37,
  Ior1 = 38,
  Ior2 = 39,
  Ior3 = 40,
  Ior4 = 41,
  Ior5 = 42,
  Ior6 = 43,
  Ior7 = 44,
  //Ior8
  //Ior9
  Ior10 = 45,
  Ior11 = 46,
  Ior12 = 47,
  Ior13 = 48,
}

impl TryFrom<u8> for MioPadInput
{
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(MioPadInput::ConstantZero),
            1 => Ok(MioPadInput::ConstantOne),
            2 => Ok(MioPadInput::Ioa0),
            3 => Ok(MioPadInput::Ioa1),
            4 => Ok(MioPadInput::Ioa2),
            5 => Ok(MioPadInput::Ioa3),
            6 => Ok(MioPadInput::Ioa4),
            7 => Ok(MioPadInput::Ioa5),
            8 => Ok(MioPadInput::Ioa6),
            9 => Ok(MioPadInput::Ioa7),
            10 => Ok(MioPadInput::Ioa8),
            11 => Ok(MioPadInput::Iob0),
            12 => Ok(MioPadInput::Iob1),
            13 => Ok(MioPadInput::Iob2),
            14 => Ok(MioPadInput::Iob3),
            15 => Ok(MioPadInput::Iob4),
            16 => Ok(MioPadInput::Iob5),
            17 => Ok(MioPadInput::Iob6),
            18 => Ok(MioPadInput::Iob7),
            19 => Ok(MioPadInput::Iob8),
            20 => Ok(MioPadInput::Iob9),
            21 => Ok(MioPadInput::Iob10),
            22 => Ok(MioPadInput::Iob11),
            23 => Ok(MioPadInput::Iob12),
            24 => Ok(MioPadInput::Ioc0),
            25 => Ok(MioPadInput::Ioc1),
            26 => Ok(MioPadInput::Ioc2),
            27 => Ok(MioPadInput::Ioc3),
            28 => Ok(MioPadInput::Ioc4),
            29 => Ok(MioPadInput::Ioc5),
            30 => Ok(MioPadInput::Ioc6),
            31 => Ok(MioPadInput::Ioc7),
            32 => Ok(MioPadInput::Ioc8),
            33 => Ok(MioPadInput::Ioc9),
            34 => Ok(MioPadInput::Ioc10),
            35 => Ok(MioPadInput::Ioc11),
            36 => Ok(MioPadInput::Ioc12),
            37 => Ok(MioPadInput::Ior0),
            38 => Ok(MioPadInput::Ior1),
            39 => Ok(MioPadInput::Ior2),
            40 => Ok(MioPadInput::Ior3),
            41 => Ok(MioPadInput::Ior4),
            42 => Ok(MioPadInput::Ior5),
            43 => Ok(MioPadInput::Ior6),
            44 => Ok(MioPadInput::Ior7),
            //Ior8
            //Ior9
            //Ior10
            //Ior11
            45 => Ok(MioPadInput::Ior12),
            46 => Ok(MioPadInput::Ior11),
            47 => Ok(MioPadInput::Ior12),
            48 => Ok(MioPadInput::Ior13),
            _ => Err(()),
        }
    }
}

impl MioPeripheralInput {
    pub fn is_lock(&self, reg: &StaticRef<PinmuxRegisters>) -> bool
    {
        !reg.mio_periph_insel_regwen[*self as usize].is_set(MIO_PERIPH_INSEL_REGWEN::EN_0)
    }

    pub fn lock(&self, reg: &StaticRef<PinmuxRegisters>)
    {
        reg.mio_periph_insel_regwen[*self as usize].write(MIO_PERIPH_INSEL_REGWEN::EN_0::SET);
    }

    pub fn connect(&self, reg: &StaticRef<PinmuxRegisters>, pad: MioPadInput) -> Result<(), ErrorCode>
    {
        if self.is_lock(reg) {
            return Err(ErrorCode::FAIL);
        }
        reg.mio_periph_insel[*self as usize].write(MIO_PERIPH_INSEL::IN_0.val(pad as u32));
        Ok(())
    }

    pub fn connect_zero(&self, reg: &StaticRef<PinmuxRegisters>) -> Result<(), ErrorCode>
    {
        Self::connect(self, reg, MioPadInput::ConstantZero)
    }

    pub fn connect_one(&self, reg: &StaticRef<PinmuxRegisters>) -> Result<(), ErrorCode>
    {
        Self::connect(self, reg, MioPadInput::ConstantOne)
    }

    pub fn get_conection(&self, reg: &StaticRef<PinmuxRegisters>) -> Result<MioPadInput, ()>
    {
        MioPadInput::try_from(reg.mio_periph_insel[*self as usize].read(MIO_PERIPH_INSEL::IN_0) as u8)
    }
}

/**
 * Pinmux MIO Output.
 */
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum MioPadOutput {
  Ioa0 = 0,
  Ioa1 = 1,
  Ioa2 = 2,
  Ioa3 = 3,
  Ioa4 = 4,
  Ioa5 = 5,
  Ioa6 = 6,
  Ioa7 = 7,
  Ioa8 = 8,
  Iob0 = 9,
  Iob1 = 10,
  Iob2 = 11,
  Iob3 = 12,
  Iob4 = 13,
  Iob5 = 14,
  Iob6 = 15,
  Iob7 = 16,
  Iob8 = 17,
  Iob9 = 18,
  Iob10 = 19,
  Iob11 = 20,
  Iob12 = 21,
  Ioc0 = 22,
  Ioc1 = 23,
  Ioc2 = 24,
  Ioc3 = 25,
  Ioc4 = 26,
  Ioc5 = 27,
  Ioc6 = 28,
  Ioc7 = 29,
  Ioc8 = 30,
  Ioc9 = 31,
  Ioc10 = 32,
  Ioc11 = 33,
  Ioc12 = 34,
  Ior0 = 35,
  Ior1 = 36,
  Ior2 = 37,
  Ior3 = 38,
  Ior4 = 39,
  Ior5 = 40,
  Ior6 = 41,
  Ior7 = 42,
  //Ior8
  //Ior9
  Ior10 = 43,
  Ior11 = 44,
  Ior12 = 45,
  Ior13 = 46,
}

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum MioPeripheralOutput {
  ConstantZero = 0,
  ConstantOne = 1,
  ConstantHighZ = 2,
  GpioGpio0 = 3,
  GpioGpio1 = 4,
  GpioGpio2 = 5,
  GpioGpio3 = 6,
  GpioGpio4 = 7,
  GpioGpio5 = 8,
  GpioGpio6 = 9,
  GpioGpio7 = 10,
  GpioGpio8 = 11,
  GpioGpio9 = 12,
  GpioGpio10 = 13,
  GpioGpio11 = 14,
  GpioGpio12 = 15,
  GpioGpio13 = 16,
  GpioGpio14 = 17,
  GpioGpio15 = 18,
  GpioGpio16 = 19,
  GpioGpio17 = 20,
  GpioGpio18 = 21,
  GpioGpio19 = 22,
  GpioGpio20 = 23,
  GpioGpio21 = 24,
  GpioGpio22 = 25,
  GpioGpio23 = 26,
  GpioGpio24 = 27,
  GpioGpio25 = 28,
  GpioGpio26 = 29,
  GpioGpio27 = 30,
  GpioGpio28 = 31,
  GpioGpio29 = 32,
  GpioGpio30 = 33,
  GpioGpio31 = 34,
  I2c0Sda = 35,
  I2c0Scl = 36,
  I2c1Sda = 37,
  I2c1Scl = 38,
  I2c2Sda = 39,
  I2c2Scl = 40,
  SpiHost1Sd0 = 41,
  SpiHost1Sd1 = 42,
  SpiHost1Sd2 = 43,
  SpiHost1Sd3 = 44,
  Uart0Tx = 45,
  Uart1Tx = 46,
  Uart2Tx = 47,
  Uart3Tx = 48,
  PattgenPda0Tx = 49,
  PattgenPcl0Tx = 50,
  PattgenPda1Tx = 51,
  PattgenPcl1Tx = 52,
  SpiHost1Sck = 53,
  SpiHost1Csb = 54,
  FlashCtrlTdo = 55,
  SensorCtrlAstDebugOut0 = 56,
  SensorCtrlAstDebugOut1 = 57,
  SensorCtrlAstDebugOut2 = 58,
  SensorCtrlAstDebugOut3 = 59,
  SensorCtrlAstDebugOut4 = 60,
  SensorCtrlAstDebugOut5 = 61,
  SensorCtrlAstDebugOut6 = 62,
  SensorCtrlAstDebugOut7 = 63,
  SensorCtrlAstDebugOut8 = 64,
  PwmAonPwm0 = 65,
  PwmAonPwm1 = 66,
  PwmAonPwm2 = 67,
  PwmAonPwm3 = 68,
  PwmAonPwm4 = 69,
  PwmAonPwm5 = 70,
  OtpCtrlTest0 = 71,
  SysrstCtrlAonBatDisable = 72,
  SysrstCtrlAonKey0Out = 73,
  SysrstCtrlAonKey1Out = 74,
  SysrstCtrlAonKey2Out = 75,
  SysrstCtrlAonPwrbOut = 76,
  SysrstCtrlAonZ3Wakeup = 77,
}

impl TryFrom<u8> for MioPeripheralOutput
{
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(MioPeripheralOutput::ConstantZero),
            1 => Ok(MioPeripheralOutput::ConstantOne),
            2 => Ok(MioPeripheralOutput::ConstantHighZ),
            3 => Ok(MioPeripheralOutput::GpioGpio0),
            4 => Ok(MioPeripheralOutput::GpioGpio1),
            5 => Ok(MioPeripheralOutput::GpioGpio2),
            6 => Ok(MioPeripheralOutput::GpioGpio3),
            7 => Ok(MioPeripheralOutput::GpioGpio4),
            8 => Ok(MioPeripheralOutput::GpioGpio5),
            9 => Ok(MioPeripheralOutput::GpioGpio6),
            10 => Ok(MioPeripheralOutput::GpioGpio7),
            11 => Ok(MioPeripheralOutput::GpioGpio8),
            12 => Ok(MioPeripheralOutput::GpioGpio9),
            13 => Ok(MioPeripheralOutput::GpioGpio10),
            14 => Ok(MioPeripheralOutput::GpioGpio11),
            15 => Ok(MioPeripheralOutput::GpioGpio12),
            16 => Ok(MioPeripheralOutput::GpioGpio13),
            17 => Ok(MioPeripheralOutput::GpioGpio14),
            18 => Ok(MioPeripheralOutput::GpioGpio15),
            19 => Ok(MioPeripheralOutput::GpioGpio16),
            20 => Ok(MioPeripheralOutput::GpioGpio17),
            21 => Ok(MioPeripheralOutput::GpioGpio18),
            22 => Ok(MioPeripheralOutput::GpioGpio19),
            23 => Ok(MioPeripheralOutput::GpioGpio20),
            24 => Ok(MioPeripheralOutput::GpioGpio21),
            25 => Ok(MioPeripheralOutput::GpioGpio22),
            26 => Ok(MioPeripheralOutput::GpioGpio23),
            27 => Ok(MioPeripheralOutput::GpioGpio24),
            28 => Ok(MioPeripheralOutput::GpioGpio25),
            29 => Ok(MioPeripheralOutput::GpioGpio26),
            30 => Ok(MioPeripheralOutput::GpioGpio27),
            31 => Ok(MioPeripheralOutput::GpioGpio28),
            32 => Ok(MioPeripheralOutput::GpioGpio29),
            33 => Ok(MioPeripheralOutput::GpioGpio30),
            34 => Ok(MioPeripheralOutput::GpioGpio31),
            35 => Ok(MioPeripheralOutput::I2c0Sda),
            36 => Ok(MioPeripheralOutput::I2c0Scl),
            37 => Ok(MioPeripheralOutput::I2c1Sda),
            38 => Ok(MioPeripheralOutput::I2c1Scl),
            39 => Ok(MioPeripheralOutput::I2c2Sda),
            40 => Ok(MioPeripheralOutput::I2c2Scl),
            41 => Ok(MioPeripheralOutput::SpiHost1Sd0),
            42 => Ok(MioPeripheralOutput::SpiHost1Sd1),
            43 => Ok(MioPeripheralOutput::SpiHost1Sd2),
            44 => Ok(MioPeripheralOutput::SpiHost1Sd3),
            45 => Ok(MioPeripheralOutput::Uart0Tx),
            46 => Ok(MioPeripheralOutput::Uart1Tx),
            47 => Ok(MioPeripheralOutput::Uart2Tx),
            48 => Ok(MioPeripheralOutput::Uart3Tx),
            49 => Ok(MioPeripheralOutput::PattgenPda0Tx),
            50 => Ok(MioPeripheralOutput::PattgenPcl0Tx),
            51 => Ok(MioPeripheralOutput::PattgenPda1Tx),
            52 => Ok(MioPeripheralOutput::PattgenPcl1Tx),
            53 => Ok(MioPeripheralOutput::SpiHost1Sck),
            54 => Ok(MioPeripheralOutput::SpiHost1Csb),
            55 => Ok(MioPeripheralOutput::FlashCtrlTdo),
            56 => Ok(MioPeripheralOutput::SensorCtrlAstDebugOut0),
            57 => Ok(MioPeripheralOutput::SensorCtrlAstDebugOut1),
            58 => Ok(MioPeripheralOutput::SensorCtrlAstDebugOut2),
            60 => Ok(MioPeripheralOutput::SensorCtrlAstDebugOut4),
            61 => Ok(MioPeripheralOutput::SensorCtrlAstDebugOut5),
            62 => Ok(MioPeripheralOutput::SensorCtrlAstDebugOut6),
            63 => Ok(MioPeripheralOutput::SensorCtrlAstDebugOut7),
            64 => Ok(MioPeripheralOutput::SensorCtrlAstDebugOut8),
            65 => Ok(MioPeripheralOutput::PwmAonPwm0),
            66 => Ok(MioPeripheralOutput::PwmAonPwm1),
            67 => Ok(MioPeripheralOutput::PwmAonPwm2),
            68 => Ok(MioPeripheralOutput::PwmAonPwm3),
            69 => Ok(MioPeripheralOutput::PwmAonPwm4),
            70 => Ok(MioPeripheralOutput::PwmAonPwm5),
            71 => Ok(MioPeripheralOutput::OtpCtrlTest0),
            72 => Ok(MioPeripheralOutput::SysrstCtrlAonBatDisable),
            73 => Ok(MioPeripheralOutput::SysrstCtrlAonKey0Out),
            74 => Ok(MioPeripheralOutput::SysrstCtrlAonKey1Out),
            75 => Ok(MioPeripheralOutput::SysrstCtrlAonKey2Out),
            76 => Ok(MioPeripheralOutput::SysrstCtrlAonPwrbOut),
            77 => Ok(MioPeripheralOutput::SysrstCtrlAonZ3Wakeup),
            _ => Err(()),
        }
    }
}

impl MioPadOutput{
    pub fn is_lock(&self, reg: &StaticRef<PinmuxRegisters>) -> bool
    {
        !reg.mio_outsel_regwen[*self as usize].is_set(MIO_OUTSEL_REGWEN::EN_0)
    }

    pub fn lock(&self, reg: &StaticRef<PinmuxRegisters>)
    {
        reg.mio_outsel_regwen[*self as usize].write(MIO_OUTSEL_REGWEN::EN_0::SET)
    }

    pub fn connect(&self, reg: &StaticRef<PinmuxRegisters>, peripheral: MioPeripheralOutput) -> Result<(), ErrorCode>
    {
        if self.is_lock(reg) {
            return Err(ErrorCode::FAIL);
        }
        reg.mio_outsel[*self as usize].write(MIO_OUTSEL::OUT_0.val(peripheral as u32));
        Ok(())
    }

    pub fn connect_zero(&self, reg: &StaticRef<PinmuxRegisters>) -> Result<(), ErrorCode>
    {
        Self::connect(self, reg, MioPeripheralOutput::ConstantZero)
    }

    pub fn connect_one(&self, reg: &StaticRef<PinmuxRegisters>) -> Result<(), ErrorCode>
    {
        Self::connect(self, reg, MioPeripheralOutput::ConstantOne)
    }

    pub fn connect_high_z(&self, reg: &StaticRef<PinmuxRegisters>) -> Result<(), ErrorCode>
    {
        Self::connect(self, reg, MioPeripheralOutput::ConstantHighZ)
    }

    pub fn get_conection(&self, reg: &StaticRef<PinmuxRegisters>) -> Result<MioPeripheralOutput, ()>
    {
        MioPeripheralOutput::try_from(reg.mio_outsel[*self as usize].read(MIO_OUTSEL::OUT_0) as u8)
    }
}

/**
 * Dedicated Pad Selects
 */
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum DioPad {
  UsbdevUsbDp = 0,
  UsbdevUsbDn = 1,
  SpiHost0Sd0 = 2,
  SpiHost0Sd1 = 3,
  SpiHost0Sd2 = 4,
  SpiHost0Sd3 = 5,
  SpiDeviceSd0 = 6,
  SpiDeviceSd1 = 7,
  SpiDeviceSd2 = 8,
  SpiDeviceSd3 = 9,
  SysrstCtrlAonEcRstL = 10,
  SysrstCtrlAonFlashWpL = 11,
  SpiDeviceSck = 12,
  SpiDeviceCsb = 13,
  SpiHost0Sck = 14,
  SpiHost0Csb = 15,
}

/**
 * Muxed Pad Selects
 */
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum MioPad {
  Ioa0 = 0,
  Ioa1 = 1,
  Ioa2 = 2,
  Ioa3 = 3,
  Ioa4 = 4,
  Ioa5 = 5,
  Ioa6 = 6,
  Ioa7 = 7,
  Ioa8 = 8,
  Iob0 = 9,
  Iob1 = 10,
  Iob2 = 11,
  Iob3 = 12,
  Iob4 = 13,
  Iob5 = 14,
  Iob6 = 15,
  Iob7 = 16,
  Iob8 = 17,
  Iob9 = 18,
  Iob10 = 19,
  Iob11 = 20,
  Iob12 = 21,
  Ioc0 = 22,
  Ioc1 = 23,
  Ioc2 = 24,
  Ioc3 = 25,
  Ioc4 = 26,
  Ioc5 = 27,
  Ioc6 = 28,
  Ioc7 = 29,
  Ioc8 = 30,
  Ioc9 = 31,
  Ioc10 = 32,
  Ioc11 = 33,
  Ioc12 = 34,
  Ior0 = 35,
  Ior1 = 36,
  Ior2 = 37,
  Ior3 = 38,
  Ior4 = 39,
  Ior5 = 40,
  Ior6 = 41,
  Ior7 = 42,
  Ior10 = 43,
  Ior11 = 44,
  Ior12 = 45,
  Ior13 = 46,
}

struct PinMux {
    pinmux_registers: StaticRef<PinmuxRegisters>,
    // maybe remove this and make pure functions
    input_mux: MioPeripheralInput,
    output_mux: MioPadOutput,
}

pub enum Pad {
    Mio(MioPad),
    Dio(DioPad),
}

struct PadAttributes {
    inversion: bool,
    open_drain: bool,
    pull_mode: FloatingState,
    keeper: bool,
    shmitt: bool,
    open_drain_enable: bool,
    // 0x0 - 0x3 fastest
    slew_rate: u8,
    // 0x0 - 0xf strongest
    drive_strength: u8,
}

struct PadCtl {
    pinmux_registers: StaticRef<PinmuxRegisters>,
    pad: Pad,
}

impl PadCtl {

    pub fn new(reg: StaticRef<PinmuxRegisters>, id: Pad) -> Self {
        PadCtl {
            pinmux_registers: reg,
            pad: id,
        }
    }

    pub fn is_lock_attr(&self) -> bool
    {
        match &self.pad {
            Pad::Mio(index) => !self.pinmux_registers.mio_pad_attr_regwen[*index as usize].is_set(MIO_PAD_ATTR_REGWEN::EN_0),
            Pad::Dio(index) => !self.pinmux_registers.dio_pad_attr_regwen[*index as usize].is_set(DIO_PAD_ATTR_REGWEN::EN_0),
        }
    }

    pub fn lock_attr(&self) {
        match &self.pad {
            Pad::Mio(index) => self.pinmux_registers.mio_pad_attr_regwen[*index as usize].write(MIO_PAD_ATTR_REGWEN::EN_0::SET),
            Pad::Dio(index) => self.pinmux_registers.dio_pad_attr_regwen[*index as usize].write(DIO_PAD_ATTR_REGWEN::EN_0::SET),
        };
    }

    pub fn get_inverted(&self) -> bool 
    {
        match &self.pad {
            Pad::Mio(index) => self.pinmux_registers.mio_pad_attr[*index as usize].is_set(MIO_PAD_ATTR::INVERT_0),
            Pad::Dio(index) => self.pinmux_registers.dio_pad_attr[*index as usize].is_set(DIO_PAD_ATTR::INVERT_0),
        }
    }

    pub fn set_inverted(&self, flag: bool) -> Result<(), ErrorCode>
    {
        let value: u32 = if flag { 1 } else { 0 };
        match &self.pad {
            Pad::Mio(index) => self.pinmux_registers.mio_pad_attr[*index as usize].modify(MIO_PAD_ATTR::INVERT_0.val(value)),
            Pad::Dio(index) => self.pinmux_registers.dio_pad_attr[*index as usize].modify(DIO_PAD_ATTR::INVERT_0.val(value)),
        }
        Ok(())
    }

    pub fn get_virtual_open_drain(&self) -> bool
    {
        match &self.pad {
            Pad::Mio(index) => self.pinmux_registers.mio_pad_attr[*index as usize].is_set(MIO_PAD_ATTR::VIRTUAL_OD_EN_0),
            Pad::Dio(index) => self.pinmux_registers.dio_pad_attr[*index as usize].is_set(DIO_PAD_ATTR::VIRTUAL_OD_EN_0),
        }
    }

    pub fn set_virtual_open_drain(&self, flag: bool) -> Result<(), ErrorCode> {
        let value: u32 = if flag { 1 } else { 0 };
        match &self.pad {
            Pad::Mio(index) => self.pinmux_registers.mio_pad_attr[*index as usize].modify(MIO_PAD_ATTR::VIRTUAL_OD_EN_0.val(value)),
            Pad::Dio(index) => self.pinmux_registers.dio_pad_attr[*index as usize].modify(DIO_PAD_ATTR::VIRTUAL_OD_EN_0.val(value)),
        }
        Ok(())
    }

    pub fn get_pull_mode(&self) -> Result<FloatingState, ErrorCode> {
        match &self.pad {
            Pad::Mio(index) => {
                let attr_reg = self.pinmux_registers.mio_pad_attr[*index as usize].extract();
                match (attr_reg.is_set(MIO_PAD_ATTR::PULL_EN_0), attr_reg.read_as_enum(MIO_PAD_ATTR::PULL_SELECT_0)) {
                    (true, Some(MIO_PAD_ATTR::PULL_SELECT_0::Value::PULL_UP)) => Ok(FloatingState::PullUp),
                    (true, Some(MIO_PAD_ATTR::PULL_SELECT_0::Value::PULL_DOWN)) => Ok(FloatingState::PullDown),
                    (true, None) => Err(ErrorCode::FAIL),
                    (false, _) => Ok(FloatingState::PullNone),
                }
            }
            Pad::Dio(index) => {
                let attr_reg = self.pinmux_registers.dio_pad_attr[*index as usize].extract();
                match (attr_reg.is_set(DIO_PAD_ATTR::PULL_EN_0), attr_reg.read_as_enum(DIO_PAD_ATTR::PULL_SELECT_0)) {
                    (true, Some(DIO_PAD_ATTR::PULL_SELECT_0::Value::PULL_UP)) => Ok(FloatingState::PullUp),
                    (true, Some(DIO_PAD_ATTR::PULL_SELECT_0::Value::PULL_DOWN)) => Ok(FloatingState::PullDown),
                    (true, None) => Err(ErrorCode::FAIL),
                    (false, _) => Ok(FloatingState::PullNone),
                }
            }
        }
    }

    pub fn set_pull_mode(&self, pull: FloatingState) -> Result<(), ErrorCode> {
        match &self.pad {
            Pad::Mio(index) => {
                match pull {
                    FloatingState::PullUp => {
                        self.pinmux_registers.mio_pad_attr[*index as usize].modify(MIO_PAD_ATTR::PULL_EN_0::SET +
                                                                                  MIO_PAD_ATTR::PULL_SELECT_0::PULL_UP)
                    }
                    FloatingState::PullDown => {
                        self.pinmux_registers.mio_pad_attr[*index as usize].modify(MIO_PAD_ATTR::PULL_EN_0::SET +
                                                                                  MIO_PAD_ATTR::PULL_SELECT_0::PULL_DOWN)
                    }
                    FloatingState::PullNone => {
                        self.pinmux_registers.mio_pad_attr[*index as usize].modify(MIO_PAD_ATTR::PULL_EN_0::CLEAR)
                    }
                }
            }
            Pad::Dio(index) => {
                match pull {
                    FloatingState::PullUp => {
                        self.pinmux_registers.dio_pad_attr[*index as usize].modify(DIO_PAD_ATTR::PULL_EN_0::SET + 
                                                                                  DIO_PAD_ATTR::PULL_SELECT_0::PULL_UP)
                    }
                    FloatingState::PullDown => {
                        self.pinmux_registers.dio_pad_attr[*index as usize].modify(DIO_PAD_ATTR::PULL_EN_0::SET +
                                                                                  DIO_PAD_ATTR::PULL_SELECT_0::PULL_DOWN)
                    }
                    FloatingState::PullNone => {
                        self.pinmux_registers.dio_pad_attr[*index as usize].modify(DIO_PAD_ATTR::PULL_EN_0::CLEAR)
                    }
                }
            }
        }
        Ok(())
    }

    pub fn get_keeper_enable(&self) -> bool
    {
        match &self.pad {
            Pad::Mio(index) => self.pinmux_registers.mio_pad_attr[*index as usize].is_set(MIO_PAD_ATTR::KEEPER_EN_0),
            Pad::Dio(index) => self.pinmux_registers.dio_pad_attr[*index as usize].is_set(DIO_PAD_ATTR::KEEPER_EN_0),
        }
    }

    pub fn set_keeper_enable(&self, flag: bool) -> Result<(), ErrorCode> {
        let value: u32 = if flag { 1 } else { 0 };
        match &self.pad {
            Pad::Mio(index) => self.pinmux_registers.mio_pad_attr[*index as usize].modify(MIO_PAD_ATTR::KEEPER_EN_0.val(value)),
            Pad::Dio(index) => self.pinmux_registers.dio_pad_attr[*index as usize].modify(DIO_PAD_ATTR::KEEPER_EN_0.val(value)),
        }
        Ok(())
    }

    pub fn get_schmitt_enable(&self) -> bool
    {
        match &self.pad {
            Pad::Mio(index) => self.pinmux_registers.mio_pad_attr[*index as usize].is_set(MIO_PAD_ATTR::SCHMITT_EN_0),
            Pad::Dio(index) => self.pinmux_registers.dio_pad_attr[*index as usize].is_set(DIO_PAD_ATTR::SCHMITT_EN_0),
        }
    }

    pub fn set_schmitt_enable(&self, flag: bool) -> Result<(), ErrorCode> {
        let value: u32 = if flag { 1 } else { 0 };
        match &self.pad {
            Pad::Mio(index) => self.pinmux_registers.mio_pad_attr[*index as usize].modify(MIO_PAD_ATTR::SCHMITT_EN_0.val(value)),
            Pad::Dio(index) => self.pinmux_registers.dio_pad_attr[*index as usize].modify(DIO_PAD_ATTR::SCHMITT_EN_0.val(value)),
        }
        Ok(())
    }

    pub fn get_slew_rate(&self) -> u8
    {
        match &self.pad {
            Pad::Mio(index) => self.pinmux_registers.mio_pad_attr[*index as usize].read(MIO_PAD_ATTR::SLEW_RATE_0) as u8,
            Pad::Dio(index) => self.pinmux_registers.dio_pad_attr[*index as usize].read(DIO_PAD_ATTR::SLEW_RATE_0) as u8,
        }
    }

    pub fn set_slew_rate(&self, value: u8) -> Result<(), ErrorCode> {
        match &self.pad {
            Pad::Mio(index) => self.pinmux_registers.mio_pad_attr[*index as usize].modify(MIO_PAD_ATTR::SCHMITT_EN_0.val(value as u32)),
            Pad::Dio(index) => self.pinmux_registers.dio_pad_attr[*index as usize].modify(DIO_PAD_ATTR::SCHMITT_EN_0.val(value as u32)),
        }
        Ok(())
    }

    pub fn get_drive_strength(&self) -> u8
    {
        match &self.pad {
            Pad::Mio(index) => self.pinmux_registers.mio_pad_attr[*index as usize].read(MIO_PAD_ATTR::DRIVE_STRENGTH_0) as u8,
            Pad::Dio(index) => self.pinmux_registers.dio_pad_attr[*index as usize].read(DIO_PAD_ATTR::DRIVE_STRENGTH_0) as u8,
        }
    }

    pub fn set_drive_strength(&self, value: u8) -> Result<(), ErrorCode> {
        match &self.pad {
            Pad::Mio(index) => self.pinmux_registers.mio_pad_attr[*index as usize].modify(MIO_PAD_ATTR::DRIVE_STRENGTH_0.val(value as u32)),
            Pad::Dio(index) => self.pinmux_registers.dio_pad_attr[*index as usize].modify(DIO_PAD_ATTR::DRIVE_STRENGTH_0.val(value as u32)),
        }
        Ok(())
    }

    pub fn get_sleep_status(&self) -> bool {
        // FIXME Number of bit don't match MIO pads.
        // with updated registers map this should be split to 2 read depend on registers pad number
        // or as one  64bit register
        match &self.pad {
            Pad::Mio(index) => {
                let mask: u32 = 1 << *index as u8;
                self.pinmux_registers.mio_pad_sleep_stat[0].get() & mask != 0
            }
            Pad::Dio(index) => {
                let mask: u32 = 1 << *index as u8;
                self.pinmux_registers.dio_pad_sleep_stat[0].get() & mask != 0
            }
        }
    }

    pub fn clear_sleep_status(&self) -> bool {
        // FIXME Number of bit don't match MIO pads.
        false
    }

    pub fn is_lock_sleep(&self) -> bool
    {
        match &self.pad {
            Pad::Mio(index) => !self.pinmux_registers.mio_pad_sleep_regwen[*index as usize].is_set(MIO_PAD_SLEEP_REGWEN::EN_0),
            Pad::Dio(index) => !self.pinmux_registers.dio_pad_sleep_regwen[*index as usize].is_set(DIO_PAD_SLEEP_REGWEN::EN_0),
        }
    }

    pub fn lock_sleep(&self) {
        match &self.pad {
            Pad::Mio(index) => self.pinmux_registers.mio_pad_sleep_regwen[*index as usize].write(MIO_PAD_SLEEP_REGWEN::EN_0::SET),
            Pad::Dio(index) => self.pinmux_registers.dio_pad_sleep_regwen[*index as usize].write(DIO_PAD_SLEEP_REGWEN::EN_0::SET),
        };
    }

    pub fn get_sleep_enable(&self) -> bool
    {
        match &self.pad {
            Pad::Mio(index) => self.pinmux_registers.mio_pad_sleep_en[*index as usize].is_set(MIO_PAD_SLEEP_EN::EN_0),
            Pad::Dio(index) => self.pinmux_registers.dio_pad_sleep_en[*index as usize].is_set(DIO_PAD_SLEEP_EN::EN_0),
        }
    }

    pub fn set_sleep_enable(&self, flag: bool) {
        let value: u32 = if flag { 1 } else { 0 };
        match &self.pad {
            Pad::Mio(index) => self.pinmux_registers.mio_pad_sleep_en[*index as usize].modify(MIO_PAD_SLEEP_EN::EN_0.val(value)),
            Pad::Dio(index) => self.pinmux_registers.dio_pad_sleep_en[*index as usize].modify(DIO_PAD_SLEEP_EN::EN_0.val(value)),
        };
    }

}

