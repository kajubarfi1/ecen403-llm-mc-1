from txn_contract import TransactionPredictor, Txn
from typing import List
from collections import deque


class WbPortPredictor(TransactionPredictor):
    """
    Transaction predictor for the wb_port block.

    Input interfaces:
      - wb: Host Wishbone request stream (kinds: write, read)
      - dp_rd_rsp: Read response data returned toward the host (kinds: response)

    Output interfaces:
      - req: Internal request descriptors wb_port emits toward cmd_queue (kinds: request)
      - wb_rsp: Host Wishbone response stream out of wb_port (kinds: read_data)

    Derivation rules (from interface catalog):
      req:
        - One req.request per accepted wb access, in order.
        - Field map: req.addr <- wb.addr, req.data <- wb.data (writes), req.mask <- wb.sel (writes)
        - req.we = 1 for wb.write, 0 for wb.read
        - On reads: data is not specified by the wb transaction. The spec says
          "fields absent on: {'read': ['data']}" — we must still emit a data field
          since the req schema requires it. We choose 0 as a neutral value.
        - On reads: mask is don't-care per the catalog note
          "don't-care: mask when {'we': 0} (keep mask 0)" so we emit 0.
      wb_rsp:
        - Emit exactly one wb_rsp.read_data per wb.read, in request order.
        - addr echoes the wb.read's addr.
        - data comes from the dp_rd_rsp.response for that read (in order).
        - Hold the response until that dp_rd_rsp arrives and emit it then.
        - Never derive read data from a memory image of earlier writes.
        - Never emit nothing for a read (drain will flush if needed, but
          per the contract the dp_rd_rsp must arrive).
    """

    INPUT_IFACES: tuple = ('wb', 'dp_rd_rsp')
    OUTPUT_IFACES: tuple = ('req', 'wb_rsp')

    def __init__(self, spec: dict):
        self._spec = spec
        # Extract host interface parameters from spec for field width validation
        # (not strictly needed for prediction, but ensures we read from spec)
        hi = spec.get('host_interface', {})
        self._addr_width = hi.get('address_width_bits', 29)
        self._data_width = hi.get('data_width_bits', 32)
        sel_width = hi.get('$derived', {}).get('sel_width_bits', 4)
        self._sel_width = sel_width

        # Controller architecture for aux_width
        ca = spec.get('controller_architecture', {})
        self._aux_width = ca.get('aux_width', 4)

        self.reset()

    def reset(self) -> None:
        """Return all modeled state to power-on values."""
        # Queue of pending read addresses awaiting dp_rd_rsp data.
        # Each entry is the addr from a wb.read, in request order.
        # Per the catalog: "responses return in request order"
        self._pending_reads: deque = deque()

        # Buffer for dp_rd_rsp responses that arrived before we could pair them.
        # This shouldn't normally happen if inputs arrive in proper order,
        # but we handle it for robustness: dp_rd_rsp could arrive and we
        # need to match it to the oldest pending read.
        # Actually, re-reading the spec: dp_rd_rsp arrives *after* the read
        # request has been issued downstream, so the flow is:
        #   wb.read -> emit req.request immediately
        #            -> enqueue addr in _pending_reads
        #   dp_rd_rsp.response -> dequeue oldest pending read addr
        #                       -> emit wb_rsp.read_data with that addr and dp_rd_rsp data
        #
        # We also handle the case where dp_rd_rsp arrives before we've seen
        # the corresponding wb.read (unlikely but defensive):
        self._buffered_responses: deque = deque()

    def process(self, txn: Txn) -> List[Txn]:
        iface = txn.iface
        kind = txn.kind
        fields = txn.fields

        if iface == 'wb':
            return self._process_wb(kind, fields)
        elif iface == 'dp_rd_rsp':
            return self._process_dp_rd_rsp(kind, fields)
        else:
            # Unknown interface — ignore per contract
            return []

    def _process_wb(self, kind: str, fields: dict) -> List[Txn]:
        outputs: List[Txn] = []

        if kind == 'write':
            # Spec / interface catalog:
            #   req.we = 1 for writes
            #   req.addr <- wb.addr
            #   req.data <- wb.data
            #   req.mask <- wb.sel
            addr = fields['addr']
            data = fields['data']
            sel = fields['sel']

            req_txn = Txn(
                iface='req',
                kind='request',
                fields={
                    'we': 1,
                    'addr': addr,
                    'data': data,
                    'mask': sel,
                }
            )
            outputs.append(req_txn)
            # Writes do not produce a wb_rsp (catalog: wb_rsp only for reads)

        elif kind == 'read':
            # Spec / interface catalog:
            #   req.we = 0 for reads
            #   req.addr <- wb.addr
            #   req.data: "fields absent on: {'read': ['data']}" — field still
            #     required by req schema, emit 0 as neutral/default value.
            #   req.mask: "don't-care: mask when {'we': 0} (keep mask 0)" — emit 0.
            addr = fields['addr']

            req_txn = Txn(
                iface='req',
                kind='request',
                fields={
                    'we': 0,
                    'addr': addr,
                    'data': 0,
                    'mask': 0,
                }
            )
            outputs.append(req_txn)

            # Enqueue this read's addr so we can pair it with dp_rd_rsp later.
            # Per catalog: "Emit exactly one wb_rsp.read_data per wb.read,
            # in request order, with the request's addr."
            self._pending_reads.append(addr)

            # Check if we already have buffered dp_rd_rsp responses
            # (arrived before this read was seen — unusual but handled)
            while self._pending_reads and self._buffered_responses:
                read_addr = self._pending_reads.popleft()
                rsp_data, rsp_aux = self._buffered_responses.popleft()
                wb_rsp_txn = Txn(
                    iface='wb_rsp',
                    kind='read_data',
                    fields={
                        'addr': read_addr,
                        'data': rsp_data,
                    }
                )
                outputs.append(wb_rsp_txn)

        return outputs

    def _process_dp_rd_rsp(self, kind: str, fields: dict) -> List[Txn]:
        if kind != 'response':
            return []

        outputs: List[Txn] = []
        data = fields['data']
        aux = fields.get('aux', 0)  # aux is present in schema but not used in wb_rsp

        if self._pending_reads:
            # Pair this response with the oldest pending read
            # Per catalog: "responses return in request order"
            read_addr = self._pending_reads.popleft()
            wb_rsp_txn = Txn(
                iface='wb_rsp',
                kind='read_data',
                fields={
                    'addr': read_addr,
                    'data': data,
                }
            )
            outputs.append(wb_rsp_txn)
        else:
            # No pending read yet — buffer the response
            # This handles out-of-order arrival at the model level
            self._buffered_responses.append((data, aux))

        return outputs

    def drain(self) -> List[Txn]:
        """
        Outputs still pending after the last input.

        Per the catalog: "never emit nothing for a read" — but we can only
        emit a wb_rsp when we have both the read address and the dp_rd_rsp
        data. If there are unmatched pending reads at drain time, that
        indicates the trace is incomplete. We do NOT fabricate data.

        If there are buffered responses that didn't get matched, pair them
        with any remaining pending reads.
        """
        outputs: List[Txn] = []

        # Match any remaining pending reads with buffered responses
        while self._pending_reads and self._buffered_responses:
            read_addr = self._pending_reads.popleft()
            rsp_data, rsp_aux = self._buffered_responses.popleft()
            wb_rsp_txn = Txn(
                iface='wb_rsp',
                kind='read_data',
                fields={
                    'addr': read_addr,
                    'data': rsp_data,
                }
            )
            outputs.append(wb_rsp_txn)

        return outputs
