import Mathlib

/- I am not sure why Naus et al.-/
/- defines this as a Word8 instead of a 64-bit value-/
@[reducible] def Address: Type := Nat
@[reducible] def Size: Type := Nat
@[reducible] def BitVecArray: Type := (Array (BitVec 8))

inductive VarNode: Type where
  | Reg:  Address × Size → VarNode
  | Ram: Address × Size → VarNode
  | Var: String × Size → VarNode
  | Const: BitVecArray × Size → VarNode


inductive PCodeInstruction: Type where
  | STORE: VarNode × VarNode × VarNode → PCodeInstruction
  | BRANCH: VarNode → PCodeInstruction
  | BRANCHIND: VarNode → PCodeInstruction
  /- Has a parameter not present in Raw P-Code -/
  | RETURN: VarNode → PCodeInstruction

/- All have parameters not present in Raw P-Code -/
inductive PCodeCall: Type where
  | CALL: VarNode → PCodeCall
  | CALLIND: VarNode → PCodeCall
  | CALLOTHER: VarNode → PCodeCall
  /- EXTCALL not implemented. It's not in the manual
  and I don't know if it's high or low PCode -/

-- Copied from
-- https://github.com/niconaus/pcode-interpreter/blob/main/Types.hs
inductive PCodeOp: Type where
  | LOAD : VarNode × VarNode → PCodeOp
  | PIECE : VarNode × VarNode → PCodeOp
  | SUBPIECE : VarNode × VarNode → PCodeOp
  | POPCOUNT: VarNode → PCodeOp
  -- INTEGER OPERATIONS
  | INT_EQUAL : VarNode × VarNode → PCodeOp
  | INT_NOTEQUAL : VarNode × VarNode → PCodeOp
  | INT_LESS : VarNode × VarNode → PCodeOp
  | INT_SLESS : VarNode × VarNode → PCodeOp
  | INT_LESSEQUAL : VarNode × VarNode → PCodeOp
  | INT_SLESSEQUAL : VarNode × VarNode → PCodeOp
  | INT_ZEXT: VarNode  → PCodeOp
  | INT_SEXT: VarNode → PCodeOp
  | INT_ADD : VarNode × VarNode → PCodeOp
  | INT_SUB : VarNode × VarNode → PCodeOp
  | INT_CARRY : VarNode × VarNode → PCodeOp
  | INT_SCARRY : VarNode × VarNode → PCodeOp
  | INT_SBORROW : VarNode × VarNode → PCodeOp
  | INT_2COMP: VarNode → PCodeOp
  | INT_NEGATE: VarNode → PCodeOp
  | INT_XOR : VarNode × VarNode → PCodeOp
  | INT_AND : VarNode × VarNode → PCodeOp
  | INT_OR : VarNode × VarNode → PCodeOp
  | INT_LEFT : VarNode × VarNode → PCodeOp
  | INT_RIGHT : VarNode × VarNode → PCodeOp
  | INT_SRIGHT : VarNode × VarNode → PCodeOp
  | INT_MULT : VarNode × VarNode → PCodeOp
  | INT_DIV : VarNode × VarNode → PCodeOp
  | INT_REM : VarNode × VarNode → PCodeOp
  | INT_SDIV : VarNode × VarNode → PCodeOp
  | INT_SREM : VarNode × VarNode → PCodeOp
  -- BOOLEAN OPERATIONS
  | BOOL_NEGATE: VarNode → PCodeOp
  | BOOL_XOR : VarNode × VarNode → PCodeOp
  | BOOL_AND : VarNode × VarNode → PCodeOp
  | BOOL_OR : VarNode × VarNode → PCodeOp
  -- FLOATING POINT NUMBER OPERATIONS
  | FLOAT_EQUAL : VarNode × VarNode → PCodeOp
  | FLOAT_NOTEQUAL : VarNode × VarNode → PCodeOp
  | FLOAT_LESS : VarNode × VarNode → PCodeOp
  | FLOAT_LESSEQUAL : VarNode × VarNode → PCodeOp
  | FLOAT_ADD : VarNode × VarNode → PCodeOp
  | FLOAT_SUB : VarNode × VarNode → PCodeOp
  | FLOAT_MULT : VarNode × VarNode → PCodeOp
  | FLOAT_DIV : VarNode × VarNode → PCodeOp
  | FLOAT_NEG : VarNode → PCodeOp
  | FLOAT_ABS : VarNode → PCodeOp
  | FLOAT_SQRT : VarNode → PCodeOp
  | FLOAT_CEIL : VarNode → PCodeOp
  | FLOAT_FLOOR : VarNode → PCodeOp
  | FLOAT_ROUND : VarNode → PCodeOp
  | FLOAT_NAN : VarNode → PCodeOp
  | INT2FLOAT : VarNode → PCodeOp
  | FLOAT2FLOAT : VarNode → PCodeOp
  -- OTHER OPERATIONS
  | TRUNC VarNode : VarNode → PCodeOp
  -- UNDOCUMENTED INSTRUCTIONS
  -- | CALLOTHER VarNode [VarNode]-- I have no idea what this instruction does...
  -- ADDITIONAL INSTRUCTIONS
  | MULTIEQUAL: Array (VarNode × Address) → PCodeOp
  | INDIRECT : VarNode × VarNode → PCodeOp
  | PTRADD : VarNode × VarNode × VarNode → PCodeOp
  | PTRSUB : VarNode × VarNode → PCodeOp
  | CAST: VarNode  → PCodeOp

def Mem: Type := Batteries.HashMap Address (BitVec 8)

def Mem.getValue (mem: Mem) (addr: Address)
  (size: Size) : BitVecArray :=
  ((List.range size).map
    -- (fun off => BitVec.ofNat 8 off)).toArray
    (fun off =>
      let adj: Address := off + addr
      (match mem.findEntry? adj with
       | some (_, entry) => entry
       | none => panic! "Missing data in memory"))
   ).toArray

def Mem.setValue (mem: Mem) (addr: Address)
  (data: BitVecArray): Mem :=
  Batteries.HashMap.mergeWith (fun _ _ new => new)
    (mem)
    (Batteries.HashMap.ofList
      ((List.range data.size).map
        fun x => (x + addr, data.get! x))
    )


def Regs: Type := Batteries.HashMap Address (BitVec 8)

-- TODO: Don't repeat yourself

def Regs.setValue (regs: Regs) (addr: Address)
  (data: BitVecArray): Mem :=
  Batteries.HashMap.mergeWith (fun _ _ new => new)
    (regs)
    (Batteries.HashMap.ofList
      ((List.range data.size).map
        fun x => (x + addr, data.get! x))
    )

def Regs.getValue (regs: Regs) (addr: Address) (size: Size)
  : BitVecArray :=
  ((List.range size).map
    -- (fun off => BitVec.ofNat 8 off)).toArray
    (fun off =>
      let adj: Address := off + addr
      (match regs.findEntry? adj with
       | some (_, entry) => entry
       | none => panic! "Missing data in memory"))
   ).toArray

/- It appears in Naus et al.'s original work, this is
   64 bits because each offset in in mem/regs is 1 byte
   so you can just use 8 bytes for an 8-byte integer,
   but here you can't. -/
def Vars: Type := Batteries.HashMap String (Array (BitVec 8))

-- Update the byte array at the variable location
-- Size is in bytes
def Vars.setValue (vars: Vars) (string: String) (value: BitVecArray) : Vars :=
  vars.insert string value

-- Get the slice of vars
-- If vars is emtpy, zero. Should panic though.
def Vars.getValue (vars: Vars) (string: String) (size: Size) : BitVecArray :=
  match vars.findEntry? string with
    -- truncate it.
    | some (_, entry) => entry.extract 0 size
    | none => panic! "Can't access invalid variables" -- (List.replicate size (BitVec.ofNat 8 0)).toArray


def State: Type := Mem × Regs × Vars

def State.mem : State → Mem
  | ⟨ mem, _, _ ⟩ => mem

def State.regs : State → Regs
  | ⟨ _, regs, _ ⟩ => regs

def State.vars : State → Vars
  | ⟨ _, _, vars ⟩ => vars

/- Largely taken from LoVelib.lean -/

def State.update (input: VarNode) (value: BitVecArray) (state : State) : State :=
  let ⟨mem, regs, vars⟩ := state
  match input with
  | VarNode.Reg (addr, size) => (mem, regs, vars)
  | VarNode.Ram (addr, size) => (mem.setValue addr value, regs, vars)
  | VarNode.Var (string, size) => (mem, regs, vars.insert string value)
  -- This is illegal. How do we panic in lean?
  | VarNode.Const (arr, size) => (mem, regs, vars)

macro s:term "[" name:term "↦" val:term "]" : term =>
  `(State.update $name $val $s)

def VarNode.getBytes (state: State) (vn: VarNode) : BitVecArray :=
  let ⟨mem, regs, vars⟩ := state
  match vn with
  | VarNode.Reg (addr, sz) => regs.getValue addr sz
  | VarNode.Ram (addr, sz) => mem.getValue addr sz
  | VarNode.Var (string, sz) => vars.getValue string sz
  | VarNode.Const (data, sz) => data.extract 0 sz
