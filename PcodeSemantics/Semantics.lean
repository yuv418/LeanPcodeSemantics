import PcodeSemantics.Syntax

inductive OpSemInstructions: PCodeInstruction × State → State → Prop where
  | STORE (x output input state):
    OpSemInstructions (PCodeInstruction.STORE x, state)
      ((State.mem state).setValue
      -- interpret this address as a Nat.
        (VarNode.getBytes state output)
        (VarNode.getBytes state input), State.regs state, State.vars state)
