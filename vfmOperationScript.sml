open HolKernel boolLib bossLib Parse
     wordsLib blastLib
     optionTheory vfmTypesTheory;

val _ = new_theory "vfmOperation";

Datatype:
  opname =
    Stop
  | Add
  | Mul
  | Sub
  | Div
  | SDiv
  | Mod
  | SMod
  | AddMod
  | MulMod
  | Exp
  | SignExtend
  | LT
  | GT
  | SLT
  | SGT
  | Eq
  | IsZero
  | And
  | Or
  | XOr
  | Not
  | Byte
  | ShL
  | ShR
  | SAR
  | SHA3
  | Address
  | Balance
  | Origin
  | Caller
  | CallValue
  | CallDataLoad
  | CallDataSize
  | CallDataCopy
  | CodeSize
  | CodeCopy
  | GasPrice
  | ExtCodeSize
  | ExtCodeCopy
  | ReturnDataSize
  | ReturnDataCopy
  | ExtCodeHash
  | BlockHash
  | CoinBase
  | TimeStamp
  | Number
  | PrevRandao
  | GasLimit
  | ChainId
  | SelfBalance
  | BaseFee
  | Pop
  | MLoad
  | MStore
  | MStore8
  | SLoad
  | SStore
  | Jump
  | JumpI
  | PC
  | MSize
  | Gas
  | JumpDest
  | Push (6 word) (word8 list)
  | Dup (4 word)
  | Swap (4 word)
  | Log (3 word)
  | Create
  | Call
  | CallCode
  | Return
  | DelegateCall
  | Create2
  | StaticCall
  | Revert
  | Invalid
End

Definition wf_opname_def[simp]:
    wf_opname (Push n w) = (n ≤ n2w 32 ∧ LENGTH w = w2n n)
  ∧ wf_opname (Log n) = (n ≤ n2w 4)
  ∧ wf_opname _ = T
End

Definition opcode_def:
    opcode Stop           = [n2w 0x00]
  ∧ opcode Add            = [n2w 0x01]
  ∧ opcode Mul            = [n2w 0x02]
  ∧ opcode Sub            = [n2w 0x03]
  ∧ opcode Div            = [n2w 0x04]
  ∧ opcode SDiv           = [n2w 0x05]
  ∧ opcode Mod            = [n2w 0x06]
  ∧ opcode SMod           = [n2w 0x07]
  ∧ opcode AddMod         = [n2w 0x08]
  ∧ opcode MulMod         = [n2w 0x09]
  ∧ opcode Exp            = [n2w 0x0a]
  ∧ opcode SignExtend     = [n2w 0x0b]
  ∧ opcode LT             = [n2w 0x10]
  ∧ opcode GT             = [n2w 0x11]
  ∧ opcode SLT            = [n2w 0x12]
  ∧ opcode SGT            = [n2w 0x13]
  ∧ opcode Eq             = [n2w 0x14]
  ∧ opcode IsZero         = [n2w 0x15]
  ∧ opcode And            = [n2w 0x16]
  ∧ opcode Or             = [n2w 0x17]
  ∧ opcode XOr            = [n2w 0x18]
  ∧ opcode Not            = [n2w 0x19]
  ∧ opcode Byte           = [n2w 0x1a]
  ∧ opcode ShL            = [n2w 0x1b]
  ∧ opcode ShR            = [n2w 0x1c]
  ∧ opcode SAR            = [n2w 0x1d]
  ∧ opcode SHA3           = [n2w 0x20]
  ∧ opcode Address        = [n2w 0x30]
  ∧ opcode Balance        = [n2w 0x31]
  ∧ opcode Origin         = [n2w 0x32]
  ∧ opcode Caller         = [n2w 0x33]
  ∧ opcode CallValue      = [n2w 0x34]
  ∧ opcode CallDataLoad   = [n2w 0x35]
  ∧ opcode CallDataSize   = [n2w 0x36]
  ∧ opcode CallDataCopy   = [n2w 0x37]
  ∧ opcode CodeSize       = [n2w 0x38]
  ∧ opcode CodeCopy       = [n2w 0x39]
  ∧ opcode GasPrice       = [n2w 0x3a]
  ∧ opcode ExtCodeSize    = [n2w 0x3b]
  ∧ opcode ExtCodeCopy    = [n2w 0x3c]
  ∧ opcode ReturnDataSize = [n2w 0x3d]
  ∧ opcode ReturnDataCopy = [n2w 0x3e]
  ∧ opcode ExtCodeHash    = [n2w 0x3f]
  ∧ opcode BlockHash      = [n2w 0x40]
  ∧ opcode CoinBase       = [n2w 0x41]
  ∧ opcode TimeStamp      = [n2w 0x42]
  ∧ opcode Number         = [n2w 0x43]
  ∧ opcode PrevRandao     = [n2w 0x44]
  ∧ opcode GasLimit       = [n2w 0x45]
  ∧ opcode ChainId        = [n2w 0x46]
  ∧ opcode SelfBalance    = [n2w 0x47]
  ∧ opcode BaseFee        = [n2w 0x48]
  ∧ opcode Pop            = [n2w 0x50]
  ∧ opcode MLoad          = [n2w 0x51]
  ∧ opcode MStore         = [n2w 0x52]
  ∧ opcode MStore8        = [n2w 0x53]
  ∧ opcode SLoad          = [n2w 0x54]
  ∧ opcode SStore         = [n2w 0x55]
  ∧ opcode Jump           = [n2w 0x56]
  ∧ opcode JumpI          = [n2w 0x57]
  ∧ opcode PC             = [n2w 0x58]
  ∧ opcode MSize          = [n2w 0x59]
  ∧ opcode Gas            = [n2w 0x5a]
  ∧ opcode JumpDest       = [n2w 0x5b]
  ∧ opcode (Push n w)     = [n2w 0x5f + w2w n] ++ w
  ∧ opcode (Dup n)        = [n2w 0x81 + w2w n]
  ∧ opcode (Swap n)       = [n2w 0x91 + w2w n]
  ∧ opcode (Log n)        = [n2w 0xa0 + w2w n]
  ∧ opcode Create         = [n2w 0xf0]
  ∧ opcode Call           = [n2w 0xf1]
  ∧ opcode CallCode       = [n2w 0xf2]
  ∧ opcode Return         = [n2w 0xf3]
  ∧ opcode DelegateCall   = [n2w 0xf4]
  ∧ opcode Create2        = [n2w 0xf5]
  ∧ opcode StaticCall     = [n2w 0xfa]
  ∧ opcode Revert         = [n2w 0xfd]
  ∧ opcode Invalid        = [n2w 0xfe]
End

Definition parse_opcode_def:
  parse_opcode (opc:byte list) =
    some opn. wf_opname opn ∧ opcode opn = opc
End

(*
* finish if necessary
Theorem parse_opcode_cond_thm:
  parse_opcode (opc:byte) =
  if opc = n2w 0x00 then SOME Stop else
  if opc = n2w 0x01 then SOME Add else
  if opc = n2w 0x02 then SOME Mul else
  if opc = n2w 0x03 then SOME Sub else
  if opc = n2w 0x04 then SOME Div else
  if opc = n2w 0x05 then SOME SDiv else
  if opc = n2w 0x06 then SOME Mod else
  if opc = n2w 0x07 then SOME SMod else
  if opc = n2w 0x08 then SOME AddMod else
  if opc = n2w 0x09 then SOME MulMod else
  if opc = n2w 0x0a then SOME Exp else
  if opc = n2w 0x0b then SOME SignExtend else
  if opc = n2w 0x10 then SOME LT else
  if opc = n2w 0x11 then SOME GT else
  if opc = n2w 0x12 then SOME SLT else
  if opc = n2w 0x13 then SOME SGT else
  if opc = n2w 0x14 then SOME Eq else
  if opc = n2w 0x15 then SOME IsZero else
  if opc = n2w 0x16 then SOME And else
  if opc = n2w 0x17 then SOME Or else
  if opc = n2w 0x18 then SOME XOr else
  if opc = n2w 0x19 then SOME Not else
  if opc = n2w 0x1a then SOME Byte else
  if opc = n2w 0x1b then SOME ShL else
  if opc = n2w 0x1c then SOME ShR else
  if opc = n2w 0x1d then SOME SAR else
  if opc = n2w 0x20 then SOME SHA3 else
  if opc = n2w 0x30 then SOME Address else
  if opc = n2w 0x31 then SOME Balance else
  if opc = n2w 0x32 then SOME Origin else
  if opc = n2w 0x33 then SOME Caller else
  if opc = n2w 0x34 then SOME CallValue else
  if opc = n2w 0x35 then SOME CallDataLoad else
  if opc = n2w 0x36 then SOME CallDataSize else
  if opc = n2w 0x37 then SOME CallDataCopy else
  if opc = n2w 0x38 then SOME CodeSize else
  if opc = n2w 0x39 then SOME CodeCopy else
  if opc = n2w 0x3a then SOME GasPrice else
  if opc = n2w 0x3b then SOME ExtCodeSize else
  if opc = n2w 0x3c then SOME ExtCodeCopy else
  if opc = n2w 0x3d then SOME ReturnDataSize else
  if opc = n2w 0x3e then SOME ReturnDataCopy else
  if opc = n2w 0x3f then SOME ExtCodeHash else
  if opc = n2w 0x40 then SOME BlockHash else
  if opc = n2w 0x41 then SOME CoinBase else
  if opc = n2w 0x42 then SOME TimeStamp else
  if opc = n2w 0x43 then SOME Number else
  if opc = n2w 0x44 then SOME PrevRandao else
  if opc = n2w 0x45 then SOME GasLimit else
  if opc = n2w 0x46 then SOME ChainId else
  if opc = n2w 0x47 then SOME SelfBalance else
  if opc = n2w 0x48 then SOME BaseFee else
  if opc = n2w 0x50 then SOME Pop else
  if opc = n2w 0x51 then SOME MLoad else
  if opc = n2w 0x52 then SOME MStore else
  if opc = n2w 0x53 then SOME MStore8 else
  if opc = n2w 0x54 then SOME SLoad else
  if opc = n2w 0x55 then SOME SStore else
  if opc = n2w 0x56 then SOME Jump else
  if opc = n2w 0x57 then SOME JumpI else
  if opc = n2w 0x58 then SOME PC else
  if opc = n2w 0x59 then SOME MSize else
  if opc = n2w 0x5a then SOME Gas else
  if opc = n2w 0x5b then SOME JumpDest else
  if n2w 0x5f ≤ opc ∧ opc ≤ n2w 0x7f then SOME (Push (w2w opc - n2w 0x5f)) else
  if n2w 0x80 ≤ opc ∧ opc ≤ n2w 0x8f then SOME (Dup (w2w opc - n2w 0x81)) else
  if n2w 0x90 ≤ opc ∧ opc ≤ n2w 0x9f then SOME (Swap (w2w opc - n2w 0x91)) else
  if n2w 0xa0 ≤ opc ∧ opc ≤ n2w 0xa4 then SOME (Log (w2w opc - n2w 0xa0)) else
  if opc = n2w 0xf0 then SOME Create else
  if opc = n2w 0xf1 then SOME Call else
  if opc = n2w 0xf2 then SOME CallCode else
  if opc = n2w 0xf3 then SOME Return else
  if opc = n2w 0xf4 then SOME DelegateCall else
  if opc = n2w 0xf5 then SOME Create2 else
  if opc = n2w 0xfa then SOME StaticCall else
  if opc = n2w 0xfd then SOME Revert else
  if opc = n2w 0xfe then SOME Invalid else
  NONE
Proof
  simp[parse_opcode_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ rw[]
  \\ TRY(rename1`opcode opc` \\ Cases_on`opc` \\ fs[opcode_def])
  \\ pop_assum mp_tac \\ blastLib.BBLAST_TAC
End
*)

val _ = export_theory();
