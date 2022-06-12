from enum import Enum
from typing import List
import hashlib

class MerkelTreeNode():
    def __init__(self, left: bytes, right: bytes):
        ''' Metadata for traversing in memory.'''
        # hash(left child hash | right child hash) where "|" means concate
        self._hash = hashlib.sha256(left + right).digest()

    def hash(self):
        return self._hash

class MerkelLeafNode(MerkelTreeNode):
    def __init__(self, data: bytes):
        self._data = data
        self._hash = hashlib.sha256(self._data).digest()

    def hash(self):
        return self._hash

class NodePosition(Enum):
    '''
    Node's position relative to parent. LEFT iff the it is
    left child of the parent.
    '''
    LEFT = 1
    RIGHT = 2

class ProofEntry():
    def __init__(self, hash, position):
        self._hash = hash
        self._position = position

    def hash(self) -> bytes:
        return self._hash

    def position(self) -> NodePosition:
        return self._position
    
class NodeMetadata():
    def __init__(self, node: MerkelTreeNode):
        self._node = node

        # Mutable data
        self.parent: MerkelTreeNode = None
        self.position: NodePosition = None

    def node(self):
        return self._node
    
class Accumulator():
    def __init__(self):
        self._leaves_count = 0
        self._acc = [None]
        # key is hash
        self._nodes_metadata: Dict[bytes, NodeMetadata] = {}

    def _parent(self, left_hash: bytes, right_hash: bytes) -> bytes:
        assert left_hash in self._nodes_metadata
        assert right_hash in self._nodes_metadata

        left = self._nodes_metadata[left_hash].node()
        right = self._nodes_metadata[right_hash].node()

        # Make new node as the parent.
        parent = MerkelTreeNode(left.hash(), right.hash())
        self._nodes_metadata[parent.hash()] = NodeMetadata(parent)

        # Update metadata about the children
        left_metadata = self._nodes_metadata[left_hash]
        left_metadata.parent = parent
        left_metadata.position = NodePosition.LEFT

        right_metadata = self._nodes_metadata[right_hash]
        right_metadata.parent = parent
        right_metadata.position = NodePosition.RIGHT

        return parent.hash()

    def add_one(self, leaf: MerkelLeafNode):
        ''' Algorithm 1 in the paper '''
        self._nodes_metadata[leaf.hash()] = NodeMetadata(leaf)

        n = leaf.hash()
        h = 0
        r = self._acc[h]
        while r != None:
            n = self._parent(r, n)
            self._acc[h] = None
            h += 1
            r = self._acc[h]
        
        self._acc[h] = n
        
        # Allocate extra space at highest / most signaficant bit,
        # if self._acc[highest] is not None. This guarantees h in Algo 1 
        # above will always be valid.
        if self._acc[-1]:
            self._acc.append(None)

        self._leaves_count += 1
        return self.get_acc()

    def _delete_one(self, proof: List[ProofEntry]):
        ''' Algorithm 2 in the paper '''
        n = None
        h = 0
        while h < len(proof):
            p = proof[h].hash()
            if n is not None:
                n = self._parent(p, n)
            elif self._acc[h] is None:
                self._acc[h] = p
            else:
                n = self._parent(p, self._acc[h])
                self._acc[h] = None
            h += 1
        
        assert self._acc[h] in self._nodes_metadata
        del self._nodes_metadata[self._acc[h]]
        self._leaves_count -= 1

        self._acc[h] = n
        return self.get_acc()

    def get_acc(self):
        # without ending None
        highest_bit = len(self._acc)-1
        while not self._acc[highest_bit]:
            highest_bit -= 1

        return self._acc[:highest_bit+1]

    def verify_and_delete_one(self, proof: List[ProofEntry], leaf: MerkelLeafNode):
        ''' 
            An inclusion proof consists of a integer position of the element to be proven, 
            and a sequence of siblings to insert into the parent function. Root is not included
            in the proof. The length of proof equals the index of root (in @self._acc) where leaf
            is part of.
        '''
        assert leaf.hash() in self._nodes_metadata

        if not self._verify_proof(proof, leaf):
            raise Exception("Verification failed")

        del self._nodes_metadata[leaf.hash()]
        self._delete_one(proof)

    def _verify_proof(self, proof: List[ProofEntry], leaf: MerkelLeafNode):

        def compute_hash(left_hash: bytes, right_hash: bytes):
            return hashlib.sha256(left_hash + right_hash).digest()

        n = leaf.hash()
        h = 0
        while h < len(proof):
            p = proof[h].hash()
            position = proof[h].position()

            if position == NodePosition.LEFT:
                n = compute_hash(p, n)
            else:
                n = compute_hash(n, p)
            h += 1

        return self._acc[h] == n


if __name__ == '__main__':
    acc = Accumulator()

    node0 = MerkelLeafNode(b'\x01\x30\xaf')
    acc.add_one(node0)

    assert acc._verify_proof([], node0)

    node1 = MerkelLeafNode(b'\x02\x50\xff')
    acc.add_one(node1)

    assert acc._verify_proof([
            ProofEntry(bytes.fromhex('f69b3dba6514720d19d78000b1a22c6c1724a0c8b3d1c6e480158e281e533fe5'),
                NodePosition.LEFT
            )], node1)

    node2 = MerkelLeafNode(b'\x03\x60\xdf')
    acc.add_one(node2)
    node3 = MerkelLeafNode(b'\x04\x70\xdf')
    acc.add_one(node3)

    node2_proof = [
        ProofEntry(
            bytes.fromhex('72ae8fe3ae289c617b4d0b213fe7fb658b8049bd13c3130d976353fb9b402694'),
            NodePosition.RIGHT,
        ),
        ProofEntry(
            bytes.fromhex('62ffbcb91ffde591e756b8bc1533e308e570f4e7b8290ddb69e37ebc6d6e0370'),
            NodePosition.LEFT,
        ),
    ]
    assert acc._verify_proof(node2_proof, node2)

    acc.verify_and_delete_one(node2_proof, node2)
    assert not acc._verify_proof(node2_proof, node2)
    assert acc._leaves_count == 3

    assert acc._verify_proof([
        ProofEntry(bytes.fromhex('f69b3dba6514720d19d78000b1a22c6c1724a0c8b3d1c6e480158e281e533fe5'),
            NodePosition.LEFT
        )], node1)

    node4 = MerkelLeafNode(b'\x05\x90\xaf')
    acc.add_one(node4)
    node5 = MerkelLeafNode(b'\x06\x90\xaf')
    acc.add_one(node5)

    node4_proof = [
        ProofEntry(
            bytes.fromhex('72ae8fe3ae289c617b4d0b213fe7fb658b8049bd13c3130d976353fb9b402694'),
            NodePosition.LEFT,
        ),
        ProofEntry(
            bytes.fromhex('62ffbcb91ffde591e756b8bc1533e308e570f4e7b8290ddb69e37ebc6d6e0370'),
            NodePosition.LEFT,
        ),
    ]
    assert acc._verify_proof(node4_proof, node4)

    print(acc.get_acc())



