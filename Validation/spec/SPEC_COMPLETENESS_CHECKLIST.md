# Specification completeness checklist

A generated specification must answer every applicable question below explicitly. Silence is a defect: downstream validation cannot distinguish a design that does the wrong thing from a specification that never said what the right thing was.

## CSR_UNMAPPED_READ_DATA (when `csr_register_map` is present)
**Question.** What data accompanies a read of an address the register map does not declare?
**State it at** `csr_register_map.unmapped_read_data`, one of ['zero', 'all_ones', 'undefined', 'last_written'].
**Why it matters.** A spec-derived model and a design can both be 'correct' with different answers; the comparison is unfalsifiable until this is stated.

## CSR_UNMAPPED_WRITE (when `csr_register_map` is present)
**Question.** What happens on a write to an undeclared address — error flag, silent drop, or both?
**State it at** `csr_register_map.unmapped_write_behavior`, one of ['ignored_with_error', 'ignored_silently', 'error_only'].
**Why it matters.** Error-flag comparison on unmapped writes rests on an assumption.

## CSR_READ_BYTE_ENABLES (when `csr_register_map` is present)
**Question.** Do byte enables mean anything on a READ, and what value is expected on the request?
**State it at** `csr_register_map.read_byte_enable_semantics`, one of ['ignored', 'must_be_full', 'masks_data'].
**Why it matters.** A model predicted full enables on reads; the bus drove none. Neither is wrong.

## CSR_STATUS_READ_SAMPLING (when `csr_register_map` is present)
**Question.** When a status register is read in the same cycle its source changes, does the read return the old or the new value?
**State it at** `csr_register_map.status_read_sampling`, one of ['previous_edge', 'same_cycle'].
**Why it matters.** A one-cycle coincidence produced a mismatch that no waiver can express. Registered designs return the old value; the spec must say so.

## DDR_DM_POLARITY (when `data_path_mapping.pack_mode` is present)
**Question.** On the DDR channel, does the data-mask pin mask or enable a byte?
**State it at** `data_path_mapping.ddr_dm_polarity`, one of ['active_high_mask', 'active_high_enable'].
**Standard default.** JESD79-3 (DDR3): `active_high_mask` — DM=1 masks the byte. The host-side wishbone sel (1 = write this byte) is the inverse convention.
**Why it matters.** The design drives ~sel (JEDEC-correct); a spec-derived model carried sel through unchanged. The standard decides this one.

## TAXONOMY_SCHEDULER_FAMILY (when `controller_architecture.scheduler_policy` is present)
**Question.** Does the failure taxonomy have ids for what a queue + arbiter can do wrong — drop a request, invent a command, starve a refresh?
**State it as** failure_taxonomy ids prefixed `SCHED_` covering: dropped request, invented command, refresh never serviced.
**Why it matters.** Checkers reported real defects under locally proposed ids (SCHED_001..003) that the spec cannot name.

## INTERFACE_CONTRACTS
**Question.** For every pair of blocks a path connects, what are the port-level signals, widths and handshake between them?
**State it as** a `block_interfaces` section with one contract per connected block pair (signals, widths, directions, handshake).
**Why it matters.** The drop shipped 11 blocks and no top level; two block pairs did not compose (no bank on cmd_gen's feedback, nothing consuming calibration's ZQCS request). Validation had to author a 75-connection map by hand. Interfaces that are not specified cannot be generated consistently on both sides.

## TAXONOMY_NAMES_TIMING_PARAMS (when `timing_model` is present)
**Question.** Does the failure taxonomy have an id for violating EVERY timing parameter the timing model states?
**State it as** one failure_taxonomy id per `timing_model` parameter, naming the parameter.
**Why it matters.** A parameter with no failure id has no assertion name to report under; tREFI had none, so the refresh-interval assertion reports under a proposed TIMING_012.

## INIT_TMRD (when `initialization_sequence.mode_registers` is present)
**Question.** What is the minimum spacing between consecutive mode-register-set commands (tMRD)?
**State it at** `timing_model.tMRD`.
**Standard default.** JESD79-3 (DDR3): `4 nCK` — MRS-to-MRS command spacing. Stated in nanoseconds in timing_model (4 x tCK).
**Why it matters.** The init sequence issues four MRS commands; without tMRD their spacing cannot be asserted, so INIT_002 is only partially checkable.

## INIT_TMOD (when `initialization_sequence.mode_registers` is present)
**Question.** What is the minimum delay from a mode-register-set command to the next non-MRS command (tMOD)?
**State it at** `timing_model.tMOD`.
**Standard default.** JESD79-3 (DDR3): `max(12 nCK, 15 ns)` — MRS to any non-MRS command.
**Why it matters.** ZQCL after the last MRS cannot be checked for tMOD without it.

