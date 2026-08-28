


/-- The structure of a machine number. -/
inductive MachineNumber where
  | base(val: UInt64): MachineNumber
  | succ(digit: MachineNumber) (word: MachineNumber): MachineNumber
