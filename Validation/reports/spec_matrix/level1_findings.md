# Spec matrix, level 1: what the review blocks on non-golden specs (2026-11-04)

50 specs (5 presets, a pairwise covering set over the Tier-1 choices, 13 Tier-2 edges); 31 pass the review, 19 are blocked. Every blocking message groups into one of these:

## 14 spec(s): `schema: data_path_mapping.pack_mode: 'unpack_32_to_64' is not one of ['direct', 'pack_32_to_8', 'pack_32_to_16', 'pack_32_to_32', 'pack_32_to_64', 'pa`

- edge_largest_space: DDR3-1333 8Gb x16 lanes=8 ecc=0
- pair_02: DDR3-1066 8Gb x8 lanes=8 ecc=0
- pair_03: DDR3-1333 1Gb x16 lanes=5 ecc=3
- pair_06: DDR3-1066 1Gb x16 lanes=5 ecc=2
- pair_08: DDR3-1333 8Gb x16 lanes=4 ecc=0
- pair_10: DDR3-800 1Gb x16 lanes=6 ecc=0
- pair_12: DDR3-1600 1Gb x16 lanes=8 ecc=0
- pair_15: DDR3-1333 4Gb x16 lanes=6 ecc=0
- ... and 6 more

## 7 spec(s): `registers: BIST_ADDR_START.reserved: bits 31:33 exceed the 32-bit data width`

- edge_largest_space: DDR3-1333 8Gb x16 lanes=8 ecc=0
- pair_02: DDR3-1066 8Gb x8 lanes=8 ecc=0
- pair_08: DDR3-1333 8Gb x16 lanes=4 ecc=0
- pair_09: DDR3-1600 8Gb x8 lanes=5 ecc=1
- pair_15: DDR3-1333 4Gb x16 lanes=6 ecc=0
- pair_24: DDR3-1066 8Gb x16 lanes=6 ecc=0
- pair_26: DDR3-1333 4Gb x8 lanes=8 ecc=0

## 7 spec(s): `registers: BIST_ADDR_START.reserved: bits 31:33 overlap another field`

- edge_largest_space: DDR3-1333 8Gb x16 lanes=8 ecc=0
- pair_02: DDR3-1066 8Gb x8 lanes=8 ecc=0
- pair_08: DDR3-1333 8Gb x16 lanes=4 ecc=0
- pair_09: DDR3-1600 8Gb x8 lanes=5 ecc=1
- pair_15: DDR3-1333 4Gb x16 lanes=6 ecc=0
- pair_24: DDR3-1066 8Gb x16 lanes=6 ecc=0
- pair_26: DDR3-1333 4Gb x8 lanes=8 ecc=0

## 7 spec(s): `registers: BIST_ADDR_END.reserved: bits 31:33 exceed the 32-bit data width`

- edge_largest_space: DDR3-1333 8Gb x16 lanes=8 ecc=0
- pair_02: DDR3-1066 8Gb x8 lanes=8 ecc=0
- pair_08: DDR3-1333 8Gb x16 lanes=4 ecc=0
- pair_09: DDR3-1600 8Gb x8 lanes=5 ecc=1
- pair_15: DDR3-1333 4Gb x16 lanes=6 ecc=0
- pair_24: DDR3-1066 8Gb x16 lanes=6 ecc=0
- pair_26: DDR3-1333 4Gb x8 lanes=8 ecc=0

## 7 spec(s): `registers: BIST_ADDR_END.reserved: bits 31:33 overlap another field`

- edge_largest_space: DDR3-1333 8Gb x16 lanes=8 ecc=0
- pair_02: DDR3-1066 8Gb x8 lanes=8 ecc=0
- pair_08: DDR3-1333 8Gb x16 lanes=4 ecc=0
- pair_09: DDR3-1600 8Gb x8 lanes=5 ecc=1
- pair_15: DDR3-1333 4Gb x16 lanes=6 ecc=0
- pair_24: DDR3-1066 8Gb x16 lanes=6 ecc=0
- pair_26: DDR3-1333 4Gb x8 lanes=8 ecc=0

## 5 spec(s): `schema: memory_geometry.row_bits: 17 is above maximum 16`

- pair_02: DDR3-1066 8Gb x8 lanes=8 ecc=0
- pair_09: DDR3-1600 8Gb x8 lanes=5 ecc=1
- pair_13: DDR3-800 8Gb x8 lanes=2 ecc=3
- pair_20: DDR3-1333 8Gb x8 lanes=3 ecc=2
- pair_25: DDR3-1066 8Gb x8 lanes=1 ecc=0

## 3 spec(s): `schema: host_interface.address_width_bits: 33 is above maximum 32`

- edge_largest_space: DDR3-1333 8Gb x16 lanes=8 ecc=0
- pair_02: DDR3-1066 8Gb x8 lanes=8 ecc=0
- pair_24: DDR3-1066 8Gb x16 lanes=6 ecc=0

## 3 spec(s): `registers: BIST_ADDR_START.start_addr: bits 32:0 exceed the 32-bit data width`

- edge_largest_space: DDR3-1333 8Gb x16 lanes=8 ecc=0
- pair_02: DDR3-1066 8Gb x8 lanes=8 ecc=0
- pair_24: DDR3-1066 8Gb x16 lanes=6 ecc=0

## 3 spec(s): `registers: BIST_ADDR_END.end_addr: bits 32:0 exceed the 32-bit data width`

- edge_largest_space: DDR3-1333 8Gb x16 lanes=8 ecc=0
- pair_02: DDR3-1066 8Gb x8 lanes=8 ecc=0
- pair_24: DDR3-1066 8Gb x16 lanes=6 ecc=0

## 1 spec(s): `registers: TIMING_1.tRFC_nCK: reset_value 0x118 does not fit 8 bit(s)`

- pair_09: DDR3-1600 8Gb x8 lanes=5 ecc=1

## 1 spec(s): `schema: initialization_sequence.mode_registers.MR0.burst_length: 'on_the_fly' is not one of ['fixed_8', 'on_the_fly_4_8']`

- edge_bl4: DDR3-1333 2Gb x8 lanes=2 ecc=0
