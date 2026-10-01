from txn_contract import TransactionPredictor, Txn
from typing import List


class WbPortPredictor(TransactionPredictor):
    INPUT_IFACES = ('wb', 'dp_rd_rsp')
    OUTPUT_IFACES = ('req', 'wb_rsp')

    def __init__(self, spec: dict):
        self.spec = spec
        self.reset()

    def reset(self) -> None:
        # Queue of pending read addresses waiting for dp_rd_rsp responses
        self.pending_reads: list = []

    def process(self, txn: Txn) -> List[Txn]:
        iface = txn.iface
        kind = txn.kind
        fields = txn.fields

        if iface == 'wb':
            if kind == 'write':
                # Emit a req.request for a write
                addr = fields.get('addr', 0)
                data = fields.get('data', 0)
                sel = fields.get('sel', 0)

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
                return [req_txn]

            elif kind == 'read':
                addr = fields.get('addr', 0)

                # Emit a req.request for a read
                # mask is don't-care on reads; predict 0
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

                # Queue this read address; we'll emit wb_rsp when dp_rd_rsp arrives
                self.pending_reads.append(addr)

                return [req_txn]
            else:
                return []

        elif iface == 'dp_rd_rsp':
            if kind == 'response':
                # This is the read data returning from downstream for the oldest pending read
                if not self.pending_reads:
                    # No pending reads — unexpected, but spec says responses return in order
                    # Just ignore if there's nothing pending
                    return []

                addr = self.pending_reads.pop(0)
                data = fields.get('data', 0)

                rsp_txn = Txn(
                    iface='wb_rsp',
                    kind='read_data',
                    fields={
                        'addr': addr,
                        'data': data,
                    }
                )
                return [rsp_txn]
            else:
                return []

        else:
            # Unknown interface — ignore
            return []

    def drain(self) -> List[Txn]:
        # All read responses should have been matched by dp_rd_rsp inputs.
        # If any pending reads remain without responses, the spec says
        # "never emit nothing for a read" but we can only emit when we
        # have dp_rd_rsp data. Since drain is called after all inputs,
        # if there are still pending reads, there were missing dp_rd_rsp
        # transactions. We have no data to fill in, so return empty.
        return []
