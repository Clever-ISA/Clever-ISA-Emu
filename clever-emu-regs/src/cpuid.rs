use clever_emu_primitives::primitive::LeU64;

pub const CPUEX2_PAS: u64 = 3;
pub const CPUEX2_VAS: u64 = 2;
pub const CPUEX2_RAND: u64 = cfg!(feature = "rand") as u64;
pub const CPUEX2_FP: u64 = cfg!(feature = "float") as u64;
pub const CPUEX2_FPEXT: u64 = cfg!(feature = "float-ext") as u64;
pub const CPUEX2_VEC: u64 = cfg!(feature = "vector") as u64;
pub const CPUEX2_VIRT: u64 = 0;
pub const CPUEX2_CRYPTO: u64 = cfg!(feature = "crypto") as u64;
pub const CPUEX2_NDRAND: u64 = 0;
pub const CPUEX2_HASH_ACCEL: u64 = cfg!(feature = "hash-accel") as u64;

pub const CPUEX2: LeU64 = LeU64::new(
    1 | (CPUEX2_PAS << 2)
        | (CPUEX2_VAS << 5)
        | (CPUEX2_RAND << 8)
        | (CPUEX2_FP << 9)
        | (CPUEX2_FPEXT << 10)
        | (CPUEX2_VEC << 11)
        | (CPUEX2_VIRT << 12)
        | (CPUEX2_NDRAND << 13)
        | (CPUEX2_HASH_ACCEL << 14)
        | (CPUEX2_CRYPTO << 16),
);
pub const MSCPUEX: LeU64 = LeU64::new(0x00_01);

pub const CPUEX: [LeU64; 6] = [
    CPUEX2,
    LeU64::new(0),
    LeU64::new(0),
    LeU64::new(0),
    LeU64::new(0),
    MSCPUEX,
];
