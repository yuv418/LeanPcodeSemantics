import PcodeSemantics.Syntax

inductive OpSemInstructions: PCodeInstruction × State → State → Prop where
  | STORE (x output input state):
    OpSemInstructions (PCodeInstruction.STORE x, output, input) (state[input ↦ output])
