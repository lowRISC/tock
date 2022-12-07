// Generated register constants for PWRMGR.
// This file is licensed under either of:
//   Apache License, Version 2.0 (LICENSE-APACHE <http://www.apache.org/licenses/LICENSE-2.0>)
//   MIT License (LICENSE-MIT <http://opensource.org/licenses/MIT>)

// Built for earlgrey_silver_release_v5-8869-g86fa2efb3
// https://github.com/lowRISC/opentitan/tree/86fa2efb3c48b13f429129b7f17b04376b886c3a
// Tree status: clean
// Build date: 2022-12-07T12:53:24

// Original reference file: hw/top_earlgrey/ip/pwrmgr/data/autogen/pwrmgr.hjson
use kernel::utilities::registers::ReadWrite;
use kernel::utilities::registers::{register_bitfields, register_structs};
// Number of wakeups
pub const PWRMGR_PARAM_NUM_WKUPS: u32 = 6;
// Vector index for sysrst_ctrl_aon wkup_req, applies for WAKEUP_EN, WAKE_STATUS and WAKE_INFO
pub const PWRMGR_PARAM_SYSRST_CTRL_AON_WKUP_REQ_IDX: u32 = 0;
// Vector index for adc_ctrl_aon wkup_req, applies for WAKEUP_EN, WAKE_STATUS and WAKE_INFO
pub const PWRMGR_PARAM_ADC_CTRL_AON_WKUP_REQ_IDX: u32 = 1;
// Vector index for pinmux_aon pin_wkup_req, applies for WAKEUP_EN, WAKE_STATUS and WAKE_INFO
pub const PWRMGR_PARAM_PINMUX_AON_PIN_WKUP_REQ_IDX: u32 = 2;
// Vector index for pinmux_aon usb_wkup_req, applies for WAKEUP_EN, WAKE_STATUS and WAKE_INFO
pub const PWRMGR_PARAM_PINMUX_AON_USB_WKUP_REQ_IDX: u32 = 3;
// Vector index for aon_timer_aon wkup_req, applies for WAKEUP_EN, WAKE_STATUS and WAKE_INFO
pub const PWRMGR_PARAM_AON_TIMER_AON_WKUP_REQ_IDX: u32 = 4;
// Vector index for sensor_ctrl wkup_req, applies for WAKEUP_EN, WAKE_STATUS and WAKE_INFO
pub const PWRMGR_PARAM_SENSOR_CTRL_WKUP_REQ_IDX: u32 = 5;
// Number of peripheral reset requets
pub const PWRMGR_PARAM_NUM_RST_REQS: u32 = 2;
// Number of pwrmgr internal reset requets
pub const PWRMGR_PARAM_NUM_INT_RST_REQS: u32 = 2;
// Number of debug reset requets
pub const PWRMGR_PARAM_NUM_DEBUG_RST_REQS: u32 = 1;
// Reset req idx for MainPwr
pub const PWRMGR_PARAM_RESET_MAIN_PWR_IDX: u32 = 2;
// Reset req idx for Esc
pub const PWRMGR_PARAM_RESET_ESC_IDX: u32 = 3;
// Reset req idx for Ndm
pub const PWRMGR_PARAM_RESET_NDM_IDX: u32 = 4;
// Number of alerts
pub const PWRMGR_PARAM_NUM_ALERTS: u32 = 1;
// Register width
pub const PWRMGR_PARAM_REG_WIDTH: u32 = 32;

register_structs! {
    pub PwrmgrRegisters {
        // Interrupt State Register
        (0x0000 => pub(crate) intr_state: ReadWrite<u32, INTR::Register>),
        // Interrupt Enable Register
        (0x0004 => pub(crate) intr_enable: ReadWrite<u32, INTR::Register>),
        // Interrupt Test Register
        (0x0008 => pub(crate) intr_test: ReadWrite<u32, INTR::Register>),
        // Alert Test Register
        (0x000c => pub(crate) alert_test: ReadWrite<u32, ALERT_TEST::Register>),
        // Controls the configurability of the !!CONTROL register.
        (0x0010 => pub(crate) ctrl_cfg_regwen: ReadWrite<u32, CTRL_CFG_REGWEN::Register>),
        // Control register
        (0x0014 => pub(crate) control: ReadWrite<u32, CONTROL::Register>),
        // The configuration registers CONTROL, WAKEUP_EN, RESET_EN are all written in the
        (0x0018 => pub(crate) cfg_cdc_sync: ReadWrite<u32, CFG_CDC_SYNC::Register>),
        // Configuration enable for wakeup_en register
        (0x001c => pub(crate) wakeup_en_regwen: ReadWrite<u32, WAKEUP_EN_REGWEN::Register>),
        // Bit mask for enabled wakeups
        (0x0020 => pub(crate) wakeup_: [ReadWrite<u32, WAKEUP_::Register>; 1]),
        // A read only register of all current wake requests post enable mask
        (0x0024 => pub(crate) wake_stat: [ReadWrite<u32, WAKE_STAT::Register>; 1]),
        // Configuration enable for reset_en register
        (0x0028 => pub(crate) reset_en_regwen: ReadWrite<u32, RESET_EN_REGWEN::Register>),
        // Bit mask for enabled reset requests
        (0x002c => pub(crate) reset_: [ReadWrite<u32, RESET_::Register>; 1]),
        // A read only register of all current reset requests post enable mask
        (0x0030 => pub(crate) reset_stat: [ReadWrite<u32, RESET_STAT::Register>; 1]),
        // A read only register of escalation reset request
        (0x0034 => pub(crate) escalate_reset_status: ReadWrite<u32, ESCALATE_RESET_STATUS::Register>),
        // Indicates which functions caused the chip to wakeup
        (0x0038 => pub(crate) wake_info_capture_dis: ReadWrite<u32, WAKE_INFO_CAPTURE_DIS::Register>),
        // Indicates which functions caused the chip to wakeup.
        (0x003c => pub(crate) wake_info: ReadWrite<u32, WAKE_INFO::Register>),
        // A read only register that shows the existing faults
        (0x0040 => pub(crate) fault_status: ReadWrite<u32, FAULT_STATUS::Register>),
        (0x0044 => @END),
    }
}

register_bitfields![u32,
    // Common Interrupt Offsets
    pub(crate) INTR [
        WAKEUP OFFSET(0) NUMBITS(1) [],
    ],
    pub(crate) ALERT_TEST [
        FATAL_FAULT OFFSET(0) NUMBITS(1) [],
    ],
    pub(crate) CTRL_CFG_REGWEN [
        EN OFFSET(0) NUMBITS(1) [],
    ],
    pub(crate) CONTROL [
        LOW_POWER_HINT OFFSET(0) NUMBITS(1) [
            NONE = 0,
            LOW_POWER = 1,
        ],
        CORE_CLK_EN OFFSET(4) NUMBITS(1) [
            DISABLED = 0,
            ENABLED = 1,
        ],
        IO_CLK_EN OFFSET(5) NUMBITS(1) [
            DISABLED = 0,
            ENABLED = 1,
        ],
        USB_CLK_EN_LP OFFSET(6) NUMBITS(1) [
            DISABLED = 0,
            ENABLED = 1,
        ],
        USB_CLK_EN_ACTIVE OFFSET(7) NUMBITS(1) [
            DISABLED = 0,
            ENABLED = 1,
        ],
        MAIN_PD_N OFFSET(8) NUMBITS(1) [
            POWER_DOWN = 0,
            POWER_UP = 1,
        ],
    ],
    pub(crate) CFG_CDC_SYNC [
        SYNC OFFSET(0) NUMBITS(1) [],
    ],
    pub(crate) WAKEUP_EN_REGWEN [
        EN OFFSET(0) NUMBITS(1) [],
    ],
    pub(crate) WAKEUP_ [
        EN_0 OFFSET(0) NUMBITS(1) [],
        EN_1 OFFSET(1) NUMBITS(1) [],
        EN_2 OFFSET(2) NUMBITS(1) [],
        EN_3 OFFSET(3) NUMBITS(1) [],
        EN_4 OFFSET(4) NUMBITS(1) [],
        EN_5 OFFSET(5) NUMBITS(1) [],
    ],
    pub(crate) WAKE_STAT [
        VAL_0 OFFSET(0) NUMBITS(1) [],
        VAL_1 OFFSET(1) NUMBITS(1) [],
        VAL_2 OFFSET(2) NUMBITS(1) [],
        VAL_3 OFFSET(3) NUMBITS(1) [],
        VAL_4 OFFSET(4) NUMBITS(1) [],
        VAL_5 OFFSET(5) NUMBITS(1) [],
    ],
    pub(crate) RESET_EN_REGWEN [
        EN OFFSET(0) NUMBITS(1) [],
    ],
    pub(crate) RESET_ [
        EN_0 OFFSET(0) NUMBITS(1) [],
        EN_1 OFFSET(1) NUMBITS(1) [],
    ],
    pub(crate) RESET_STAT [
        VAL_0 OFFSET(0) NUMBITS(1) [],
        VAL_1 OFFSET(1) NUMBITS(1) [],
    ],
    pub(crate) ESCALATE_RESET_STATUS [
        VAL OFFSET(0) NUMBITS(1) [],
    ],
    pub(crate) WAKE_INFO_CAPTURE_DIS [
        VAL OFFSET(0) NUMBITS(1) [],
    ],
    pub(crate) WAKE_INFO [
        REASONS OFFSET(0) NUMBITS(6) [],
        FALL_THROUGH OFFSET(6) NUMBITS(1) [],
        ABORT OFFSET(7) NUMBITS(1) [],
    ],
    pub(crate) FAULT_STATUS [
        REG_INTG_ERR OFFSET(0) NUMBITS(1) [],
        ESC_TIMEOUT OFFSET(1) NUMBITS(1) [],
        MAIN_PD_GLITCH OFFSET(2) NUMBITS(1) [],
    ],
];

// End generated register constants for PWRMGR
