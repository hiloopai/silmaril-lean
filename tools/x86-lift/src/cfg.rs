//! How control leaves an instruction, independent of the instruction set.
//!
//! [`crate::Lifted::flow`] classifies each lifted instruction by its [`Flow`];
//! [`Node`] is the view of one instruction that a basic-block or control-flow
//! graph builder needs. The successors follow the Lean side: [`Node::cfg_targets`]
//! lists them as `Silmaril.X86.Decompile.Decoded.cfgTargets` does and
//! [`Node::retiring`] is `Decompile.retiring`.

/// How control leaves one instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Flow {
    /// Falls through to the next instruction (every "retiring" instruction).
    Next,
    /// Unconditional direct jump.
    Jump(u64),
    /// Conditional direct branch: to the target when taken, else falls through.
    Branch(u64),
    /// Direct call: to the target, and back to the next instruction.
    Call(u64),
    /// Return to the address on the stack.
    Ret,
    /// Traps (`ud2`); no successor.
    Halt,
}

/// One instruction as a control-flow-graph builder sees it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Node {
    /// Address of the first byte.
    pub addr: u64,
    /// Encoded length.
    pub len: u64,
    /// Control flow out of it.
    pub flow: Flow,
}

impl Node {
    /// The fall-through address, modulo 2^64 as the machine computes it.
    pub fn next(&self) -> u64 {
        self.addr.wrapping_add(self.len)
    }

    /// Intraprocedural successors, in `Decoded.cfgTargets` order: the branch
    /// target before the fall-through. A call contributes only its
    /// fall-through; `ret` and `ud2` contribute none.
    pub fn cfg_targets(&self) -> Vec<u64> {
        match self.flow {
            Flow::Next => vec![self.next()],
            Flow::Jump(t) => vec![t],
            Flow::Branch(t) => vec![t, self.next()],
            Flow::Call(_) => vec![self.next()],
            Flow::Ret | Flow::Halt => vec![],
        }
    }

    /// `Decompile.retiring`: the instruction simply falls through.
    pub fn retiring(&self) -> bool {
        matches!(self.flow, Flow::Next)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn targets_in_lean_order() {
        let n = |addr, len, flow| Node { addr, len, flow };
        assert_eq!(n(0, 4, Flow::Next).cfg_targets(), vec![4]);
        assert_eq!(n(7, 6, Flow::Branch(20)).cfg_targets(), vec![20, 13]);
        assert_eq!(n(15, 5, Flow::Jump(4)).cfg_targets(), vec![4]);
        assert_eq!(n(20, 5, Flow::Call(100)).cfg_targets(), vec![25]);
        assert!(n(25, 1, Flow::Ret).cfg_targets().is_empty());
        assert!(n(26, 2, Flow::Halt).cfg_targets().is_empty());
        assert!(n(0, 4, Flow::Next).retiring());
        assert!(!n(20, 5, Flow::Call(100)).retiring());
        assert_eq!(n(u64::MAX, 1, Flow::Next).next(), 0);
    }
}
