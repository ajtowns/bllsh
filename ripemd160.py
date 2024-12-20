# Copyright (c) 2024 Anthony Towns
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Extend test-only RIPEMD160 implementation to offer hashlib-ish interface."""

from verystable.core.ripemd160 import compress

class hasher:
    def __init__(self):
        self.state = (0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0)
        self.pending = b''
        self.size = 0

    def copy(self):
        h = hasher()
        h.state, h.pending, h.size = self.state, self.pending[:], self.size
        return h

    def update(self, data):
        self.pending += data
        self.size += len(data)
        while len(self.pending) >= 64:
            self.state = compress(*self.state, self.pending[:64])
            self.pending = self.pending[64:]

    def digest(self):
        # padding
        pad = b"\x80" + b"\x00" * ((119 - len(self.pending)) & 63)
        # length
        l = (8 * self.size).to_bytes(8, 'little')
        data = self.pending + pad + l
        # finalize data
        state = compress(*self.state, data[:64])
        if len(data) > 64:
            state = compress(*state, data[64:])
        return b"".join((h & 0xffffffff).to_bytes(4, 'little') for h in state)

