// Generated register constants for SENSOR_CTRL.
// This file is licensed under either of:
//   Apache License, Version 2.0 (LICENSE-APACHE <http://www.apache.org/licenses/LICENSE-2.0>)
//   MIT License (LICENSE-MIT <http://opensource.org/licenses/MIT>)

// Built for earlgrey_silver_release_v5-8869-g86fa2efb3
// https://github.com/lowRISC/opentitan/tree/86fa2efb3c48b13f429129b7f17b04376b886c3a
// Tree status: clean
// Build date: 2022-12-07T12:53:24

// Original reference file: hw/top_earlgrey/ip/sensor_ctrl/data/sensor_ctrl.hjson
use kernel::utilities::registers::ReadWrite;
use kernel::utilities::registers::{register_bitfields, register_structs};
// Number of alert events from ast
pub const SENSOR_CTRL_PARAM_NUM_ALERT_EVENTS: u32 = 11;
// Number of local events
pub const SENSOR_CTRL_PARAM_NUM_LOCAL_EVENTS: u32 = 1;
// Number of alerts sent from sensor control
pub const SENSOR_CTRL_PARAM_NUM_ALERTS: u32 = 2;
// Number of IO rails
pub const SENSOR_CTRL_PARAM_NUM_IO_RAILS: u32 = 2;
// Register width
pub const SENSOR_CTRL_PARAM_REG_WIDTH: u32 = 32;

register_structs! {
    pub SensorCtrlRegisters {
        // Interrupt State Register
        (0x0000 => pub(crate) intr_state: ReadWrite<u32, INTR::Register>),
        // Interrupt Enable Register
        (0x0004 => pub(crate) intr_enable: ReadWrite<u32, INTR::Register>),
        // Interrupt Test Register
        (0x0008 => pub(crate) intr_test: ReadWrite<u32, INTR::Register>),
        // Alert Test Register
        (0x000c => pub(crate) alert_test: ReadWrite<u32, ALERT_TEST::Register>),
        // Controls the configurability of !!FATAL_ALERT_EN register.
        (0x0010 => pub(crate) cfg_regwen: ReadWrite<u32, CFG_REGWEN::Register>),
        // Alert trigger test
        (0x0014 => pub(crate) alert_tr: [ReadWrite<u32, ALERT_TR::Register>; 1]),
        // Each bit marks a corresponding alert as fatal or recoverable.
        (0x0018 => pub(crate) fatal_alert_: [ReadWrite<u32, FATAL_ALERT_::Register>; 1]),
        // Each bit represents a recoverable alert that has been triggered by AST.
        (0x001c => pub(crate) recov_ale: [ReadWrite<u32, RECOV_ALE::Register>; 1]),
        // Each bit represents a fatal alert that has been triggered by AST.
        (0x0020 => pub(crate) fatal_ale: [ReadWrite<u32, FATAL_ALE::Register>; 1]),
        // Status readback for ast
        (0x0024 => pub(crate) status: ReadWrite<u32, STATUS::Register>),
        (0x0028 => @END),
    }
}

register_bitfields![u32,
    // Common Interrupt Offsets
    pub(crate) INTR [
        IO_STATUS_CHANGE OFFSET(0) NUMBITS(1) [],
        INIT_STATUS_CHANGE OFFSET(1) NUMBITS(1) [],
    ],
    pub(crate) ALERT_TEST [
        RECOV_ALERT OFFSET(0) NUMBITS(1) [],
        FATAL_ALERT OFFSET(1) NUMBITS(1) [],
    ],
    pub(crate) CFG_REGWEN [
        EN OFFSET(0) NUMBITS(1) [],
    ],
    pub(crate) ALERT_TR [
        VAL_0 OFFSET(0) NUMBITS(1) [],
        VAL_1 OFFSET(1) NUMBITS(1) [],
        VAL_2 OFFSET(2) NUMBITS(1) [],
        VAL_3 OFFSET(3) NUMBITS(1) [],
        VAL_4 OFFSET(4) NUMBITS(1) [],
        VAL_5 OFFSET(5) NUMBITS(1) [],
        VAL_6 OFFSET(6) NUMBITS(1) [],
        VAL_7 OFFSET(7) NUMBITS(1) [],
        VAL_8 OFFSET(8) NUMBITS(1) [],
        VAL_9 OFFSET(9) NUMBITS(1) [],
        VAL_10 OFFSET(10) NUMBITS(1) [],
    ],
    pub(crate) FATAL_ALERT_ [
        VAL_0 OFFSET(0) NUMBITS(1) [],
        VAL_1 OFFSET(1) NUMBITS(1) [],
        VAL_2 OFFSET(2) NUMBITS(1) [],
        VAL_3 OFFSET(3) NUMBITS(1) [],
        VAL_4 OFFSET(4) NUMBITS(1) [],
        VAL_5 OFFSET(5) NUMBITS(1) [],
        VAL_6 OFFSET(6) NUMBITS(1) [],
        VAL_7 OFFSET(7) NUMBITS(1) [],
        VAL_8 OFFSET(8) NUMBITS(1) [],
        VAL_9 OFFSET(9) NUMBITS(1) [],
        VAL_10 OFFSET(10) NUMBITS(1) [],
    ],
    pub(crate) RECOV_ALE [
        VAL_0 OFFSET(0) NUMBITS(1) [],
        VAL_1 OFFSET(1) NUMBITS(1) [],
        VAL_2 OFFSET(2) NUMBITS(1) [],
        VAL_3 OFFSET(3) NUMBITS(1) [],
        VAL_4 OFFSET(4) NUMBITS(1) [],
        VAL_5 OFFSET(5) NUMBITS(1) [],
        VAL_6 OFFSET(6) NUMBITS(1) [],
        VAL_7 OFFSET(7) NUMBITS(1) [],
        VAL_8 OFFSET(8) NUMBITS(1) [],
        VAL_9 OFFSET(9) NUMBITS(1) [],
        VAL_10 OFFSET(10) NUMBITS(1) [],
    ],
    pub(crate) FATAL_ALE [
        VAL_0 OFFSET(0) NUMBITS(1) [],
        VAL_1 OFFSET(1) NUMBITS(1) [],
        VAL_2 OFFSET(2) NUMBITS(1) [],
        VAL_3 OFFSET(3) NUMBITS(1) [],
        VAL_4 OFFSET(4) NUMBITS(1) [],
        VAL_5 OFFSET(5) NUMBITS(1) [],
        VAL_6 OFFSET(6) NUMBITS(1) [],
        VAL_7 OFFSET(7) NUMBITS(1) [],
        VAL_8 OFFSET(8) NUMBITS(1) [],
        VAL_9 OFFSET(9) NUMBITS(1) [],
        VAL_10 OFFSET(10) NUMBITS(1) [],
        VAL_11 OFFSET(11) NUMBITS(1) [],
    ],
    pub(crate) STATUS [
        AST_INIT_DONE OFFSET(0) NUMBITS(1) [],
        IO_POK OFFSET(1) NUMBITS(2) [],
    ],
];

// End generated register constants for SENSOR_CTRL
