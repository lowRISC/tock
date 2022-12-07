// Generated register constants for CLKMGR.
// This file is licensed under either of:
//   Apache License, Version 2.0 (LICENSE-APACHE <http://www.apache.org/licenses/LICENSE-2.0>)
//   MIT License (LICENSE-MIT <http://opensource.org/licenses/MIT>)

// Built for earlgrey_silver_release_v5-8869-g86fa2efb3
// https://github.com/lowRISC/opentitan/tree/86fa2efb3c48b13f429129b7f17b04376b886c3a
// Tree status: clean
// Build date: 2022-12-07T12:53:24

// Original reference file: hw/ip/clkmgr/data/clkmgr.hjson
use kernel::utilities::registers::ReadWrite;
use kernel::utilities::registers::{register_bitfields, register_structs};
// Number of clock groups
pub const CLKMGR_PARAM_NUM_GROUPS: u32 = 7;
// Register width
pub const CLKMGR_PARAM_REG_WIDTH: u32 = 32;

register_structs! {
    pub ClkmgrRegisters {
        // Clock enable for software gateable clocks.
        (0x0000 => pub(crate) clk_enables: ReadWrite<u32, CLK_ENABLES::Register>),
        // Clock hint for software gateable clocks.
        (0x0004 => pub(crate) clk_hints: ReadWrite<u32, CLK_HINTS::Register>),
        // Since the final state of !!CLK_HINTS is not always determined by software,
        (0x0008 => pub(crate) clk_hints_status: ReadWrite<u32, CLK_HINTS_STATUS::Register>),
        (0x000c => @END),
    }
}

register_bitfields![u32,
    pub(crate) CLK_ENABLES [
        CLK_FIXED_PERI_EN OFFSET(0) NUMBITS(1) [],
        CLK_USB_48MHZ_PERI_EN OFFSET(1) NUMBITS(1) [],
    ],
    pub(crate) CLK_HINTS [
        CLK_MAIN_AES_HINT OFFSET(0) NUMBITS(1) [],
        CLK_MAIN_HMAC_HINT OFFSET(1) NUMBITS(1) [],
    ],
    pub(crate) CLK_HINTS_STATUS [
        CLK_MAIN_AES_VAL OFFSET(0) NUMBITS(1) [],
        CLK_MAIN_HMAC_VAL OFFSET(1) NUMBITS(1) [],
    ],
];

// End generated register constants for CLKMGR
