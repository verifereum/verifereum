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
  | Keccak256
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
  ∧ opcode Keccak256      = [n2w 0x20]
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
  ∧ opcode (Dup n)        = [n2w 0x80 + w2w n]
  ∧ opcode (Swap n)       = [n2w 0x90 + w2w n]
  ∧ opcode (Log n)        = [n2w 0xa0 + w2w n]
  ∧ opcode Create         = [n2w 0xf0]
  ∧ opcode Call           = [n2w 0xf1]
  ∧ opcode CallCode       = [n2w 0xf2]
  ∧ opcode Return         = [n2w 0xf3]
  ∧ opcode DelegateCall   = [n2w 0xf4]
  ∧ opcode Create2        = [n2w 0xf5]
  ∧ opcode StaticCall     = [n2w 0xfa]
  ∧ opcode Revert         = [n2w 0xfd]
End

Definition invalid_opcode_def:
  invalid_opcode : byte = n2w 0xfe
End

Definition parse_opcode_def:
  parse_opcode (opc:byte list) =
    some opn. wf_opname opn ∧ opcode opn ≼ opc
End

Definition static_gas_def[simp]:
    static_gas Stop           = 0
  ∧ static_gas Add            = 3
  ∧ static_gas Mul            = 5
  ∧ static_gas Sub            = 3
  ∧ static_gas Div            = 5
  ∧ static_gas SDiv           = 5
  ∧ static_gas Mod            = 5
  ∧ static_gas SMod           = 5
  ∧ static_gas AddMod         = 8
  ∧ static_gas MulMod         = 8
  ∧ static_gas Exp            = 10
  ∧ static_gas SignExtend     = 5
  ∧ static_gas LT             = 3
  ∧ static_gas GT             = 3
  ∧ static_gas SLT            = 3
  ∧ static_gas SGT            = 3
  ∧ static_gas Eq             = 3
  ∧ static_gas IsZero         = 3
  ∧ static_gas And            = 3
  ∧ static_gas Or             = 3
  ∧ static_gas XOr            = 3
  ∧ static_gas Not            = 3
  ∧ static_gas Byte           = 3
  ∧ static_gas ShL            = 3
  ∧ static_gas ShR            = 3
  ∧ static_gas SAR            = 3
  ∧ static_gas Keccak256      = 30
  ∧ static_gas Address        = 30
  ∧ static_gas Balance        = 0
  ∧ static_gas Origin         = 2
  ∧ static_gas Caller         = 2
  ∧ static_gas CallValue      = 2
  ∧ static_gas CallDataLoad   = 3
  ∧ static_gas CallDataSize   = 2
  ∧ static_gas CallDataCopy   = 3
  ∧ static_gas CodeSize       = 2
  ∧ static_gas CodeCopy       = 3
  ∧ static_gas GasPrice       = 2
  ∧ static_gas ExtCodeSize    = 0
  ∧ static_gas ExtCodeCopy    = 0
  ∧ static_gas ReturnDataSize = 2
  ∧ static_gas ReturnDataCopy = 3
  ∧ static_gas ExtCodeHash    = 0
  ∧ static_gas BlockHash      = 20
  ∧ static_gas CoinBase       = 2
  ∧ static_gas TimeStamp      = 2
  ∧ static_gas Number         = 2
  ∧ static_gas PrevRandao     = 2
  ∧ static_gas GasLimit       = 2
  ∧ static_gas ChainId        = 2
  ∧ static_gas SelfBalance    = 5
  ∧ static_gas BaseFee        = 2
  ∧ static_gas Pop            = 2
  ∧ static_gas MLoad          = 3
  ∧ static_gas MStore         = 3
  ∧ static_gas MStore8        = 3
  ∧ static_gas SLoad          = 0
  ∧ static_gas SStore         = 0
  ∧ static_gas Jump           = 8
  ∧ static_gas JumpI          = 10
  ∧ static_gas PC             = 2
  ∧ static_gas MSize          = 2
  ∧ static_gas Gas            = 2
  ∧ static_gas JumpDest       = 1
  ∧ static_gas (Push n w)     = (if n = 0w then 2 else 3)
  ∧ static_gas (Dup n)        = 3
  ∧ static_gas (Swap n)       = 3
  ∧ static_gas (Log n)        = 375
  ∧ static_gas Create         = 32000
  ∧ static_gas Call           = 0
  ∧ static_gas CallCode       = 0
  ∧ static_gas Return         = 0
  ∧ static_gas DelegateCall   = 0
  ∧ static_gas Create2        = 32000
  ∧ static_gas StaticCall     = 0
  ∧ static_gas Revert         = 0
End

(*
Theorem parse_opcode_cond_thm:
  parse_opcode (opc::rest: byte list) =
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
  if opc = n2w 0x20 then SOME Keccak256 else
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
  if opc = n2w 0x5f then SOME (Push 0w  (TAKE 0 rest)) else
  if opc = n2w 0x60 then SOME (Push 1w  (TAKE 1 rest)) else
  if opc = n2w 0x61 then SOME (Push 2w  (TAKE 2 rest)) else
  if opc = n2w 0x62 then SOME (Push 3w  (TAKE 3 rest)) else
  if opc = n2w 0x63 then SOME (Push 4w  (TAKE 4 rest)) else
  if opc = n2w 0x64 then SOME (Push 5w  (TAKE 5 rest)) else
  if opc = n2w 0x65 then SOME (Push 6w  (TAKE 6 rest)) else
  if opc = n2w 0x66 then SOME (Push 7w  (TAKE 7 rest)) else
  if opc = n2w 0x67 then SOME (Push 8w  (TAKE 8 rest)) else
  if opc = n2w 0x68 then SOME (Push 9w  (TAKE 9 rest)) else
  if opc = n2w 0x69 then SOME (Push 10w (TAKE 10 rest)) else
  if opc = n2w 0x6a then SOME (Push 11w (TAKE 11 rest)) else
  if opc = n2w 0x6b then SOME (Push 12w (TAKE 12 rest)) else
  if opc = n2w 0x6c then SOME (Push 13w (TAKE 13 rest)) else
  if opc = n2w 0x6d then SOME (Push 14w (TAKE 14 rest)) else
  if opc = n2w 0x6e then SOME (Push 15w (TAKE 15 rest)) else
  if opc = n2w 0x6f then SOME (Push 16w (TAKE 16 rest)) else
  if opc = n2w 0x70 then SOME (Push 17w (TAKE 17 rest)) else
  if opc = n2w 0x71 then SOME (Push 18w (TAKE 18 rest)) else
  if opc = n2w 0x72 then SOME (Push 19w (TAKE 19 rest)) else
  if opc = n2w 0x73 then SOME (Push 20w (TAKE 20 rest)) else
  if opc = n2w 0x74 then SOME (Push 21w (TAKE 21 rest)) else
  if opc = n2w 0x75 then SOME (Push 22w (TAKE 22 rest)) else
  if opc = n2w 0x76 then SOME (Push 23w (TAKE 23 rest)) else
  if opc = n2w 0x77 then SOME (Push 24w (TAKE 24 rest)) else
  if opc = n2w 0x78 then SOME (Push 25w (TAKE 25 rest)) else
  if opc = n2w 0x79 then SOME (Push 26w (TAKE 26 rest)) else
  if opc = n2w 0x7a then SOME (Push 27w (TAKE 27 rest)) else
  if opc = n2w 0x7b then SOME (Push 28w (TAKE 28 rest)) else
  if opc = n2w 0x7c then SOME (Push 29w (TAKE 29 rest)) else
  if opc = n2w 0x7d then SOME (Push 30w (TAKE 30 rest)) else
  if opc = n2w 0x7e then SOME (Push 31w (TAKE 31 rest)) else
  if opc = n2w 0x7f then SOME (Push 32w (TAKE 32 rest)) else
  if opc = n2w 0x80 then SOME (Dup 0w) else
  if opc = n2w 0x81 then SOME (Dup 1w) else
  if opc = n2w 0x82 then SOME (Dup 2w) else
  if opc = n2w 0x83 then SOME (Dup 3w) else
  if opc = n2w 0x84 then SOME (Dup 4w) else
  if opc = n2w 0x85 then SOME (Dup 5w) else
  if opc = n2w 0x86 then SOME (Dup 6w) else
  if opc = n2w 0x87 then SOME (Dup 7w) else
  if opc = n2w 0x88 then SOME (Dup 8w) else
  if opc = n2w 0x89 then SOME (Dup 9w) else
  if opc = n2w 0x8a then SOME (Dup 10w) else
  if opc = n2w 0x8b then SOME (Dup 11w) else
  if opc = n2w 0x8c then SOME (Dup 12w) else
  if opc = n2w 0x8d then SOME (Dup 13w) else
  if opc = n2w 0x8e then SOME (Dup 14w) else
  if opc = n2w 0x8f then SOME (Dup 15w) else
  if opc = n2w 0x90 then SOME (Swap 0w) else
  if opc = n2w 0x91 then SOME (Swap 1w) else
  if opc = n2w 0x92 then SOME (Swap 2w) else
  if opc = n2w 0x93 then SOME (Swap 3w) else
  if opc = n2w 0x94 then SOME (Swap 4w) else
  if opc = n2w 0x95 then SOME (Swap 5w) else
  if opc = n2w 0x96 then SOME (Swap 6w) else
  if opc = n2w 0x97 then SOME (Swap 7w) else
  if opc = n2w 0x98 then SOME (Swap 8w) else
  if opc = n2w 0x99 then SOME (Swap 9w) else
  if opc = n2w 0x9a then SOME (Swap 10w) else
  if opc = n2w 0x9b then SOME (Swap 11w) else
  if opc = n2w 0x9c then SOME (Swap 12w) else
  if opc = n2w 0x9d then SOME (Swap 13w) else
  if opc = n2w 0x9e then SOME (Swap 14w) else
  if opc = n2w 0x9f then SOME (Swap 15w) else
  if opc = n2w 0xa0 then SOME (Log 0w) else
  if opc = n2w 0xa1 then SOME (Log 1w) else
  if opc = n2w 0xa2 then SOME (Log 2w) else
  if opc = n2w 0xa3 then SOME (Log 3w) else
  if opc = n2w 0xf0 then SOME Create else
  if opc = n2w 0xf1 then SOME Call else
  if opc = n2w 0xf2 then SOME CallCode else
  if opc = n2w 0xf3 then SOME Return else
  if opc = n2w 0xf4 then SOME DelegateCall else
  if opc = n2w 0xf5 then SOME Create2 else
  if opc = n2w 0xfa then SOME StaticCall else
  if opc = n2w 0xfd then SOME Revert else
  NONE
Proof
  simp[parse_opcode_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ rw[]
  \\ TRY (
    rename1`Push 32w (TAKE 32 _)`
    \\ rename1`opcode opc`
    \\ Cases_on`opc`
    \\ qpat_x_assum`_ ≼ _`mp_tac
    \\ qpat_x_assum`wf_opname _`mp_tac
    \\ simp_tac(srw_ss())[opcode_def]
    \\ TRY(blastLib.BBLAST_TAC \\ NO_TAC)
    \\ ntac 2 strip_tac
    \\ conj_asm1_tac >- (
      qpat_x_assum`_ = _`mp_tac
      \\ blastLib.BBLAST_TAC)
    \\ rw[] \\ fs[rich_listTheory.IS_PREFIX_APPEND]
    \\ rw[rich_listTheory.TAKE_APPEND]
  )
  \\ TRY (
    rename1`opcode opc`
    \\ Cases_on`opc`
    \\ qpat_x_assum`_ ≼ _`mp_tac
    \\ qpat_x_assum`wf_opname _`mp_tac
    \\ simp_tac(srw_ss())[opcode_def]
    \\ blastLib.BBLAST_TAC
    )
QED


  \\ tac
  THENL (List.tabulate(until, fn _ => tac) @
         List.tabulate(282 - until, fn _ => ALL_TAC))

val until = 130
val tac =
    rename1`opcode opc`
    \\ Cases_on`opc`
    \\ qpat_x_assum`_ ≼ _`mp_tac
    \\ qpat_x_assum`wf_opname _`mp_tac
    \\ simp_tac(srw_ss())[opcode_def]
    \\ blastLib.BBLAST_TAC

  \\ TRY(
    rename1`opcode opc`
    \\ Cases_on`opc`
    \\ qpat_x_assum`_ ≼ _`mp_tac
    \\ qpat_x_assum`wf_opname _`mp_tac
    \\ simp_tac(srw_ss())[opcode_def]
    \\ blastLib.BBLAST_TAC
  )
  THENL


  \\ TRY(rename1 ‘opcode opc‘ \\ Cases_on ‘opc’ \\ qhdtm_x_assum ‘opcode‘ mp_tac \\ simp_tac(srw_ss())[opcode_def])
  \\ ntac 2 (pop_assum mp_tac)
  \\ rpt (pop_assum kall_tac)
  \\ TRY(rename1`opcode opc` \\ Cases_on`opc` \\ fs[opcode_def])
  \\ rpt (pop_assum mp_tac)
   \\ blastLib.BBLAST_TAC
End

open cv_transLib cv_stdTheory;

Definition parse_opcode_exec_def:
  parse_opcode_exec (opc:byte list)
    = case opc of
      | [n2w 0x00] => SOME Stop
      | [n2w 0x01] => SOME Add
      | [n2w 0x02] => SOME Mul
      | [n2w 0x03] => SOME Sub
      | [n2w 0x04] => SOME Div
      | [n2w 0x05] => SOME SDiv
      | [n2w 0x06] => SOME Mod
      | [n2w 0x07] => SOME SMod
      | [n2w 0x08] => SOME AddMod
      | [n2w 0x09] => SOME MulMod
      | [n2w 0x0a] => SOME Exp
      | [n2w 0x0b] => SOME SignExtend
      | [n2w 0x10] => SOME LT
      | [n2w 0x11] => SOME GT
      | [n2w 0x12] => SOME SLT
      | [n2w 0x13] => SOME SGT
      | [n2w 0x14] => SOME Eq
      | [n2w 0x15] => SOME IsZero
      | [n2w 0x16] => SOME And
      | [n2w 0x17] => SOME Or
      | [n2w 0x18] => SOME XOr
      | [n2w 0x19] => SOME Not
      | [n2w 0x1a] => SOME Byte
      | [n2w 0x1b] => SOME ShL
      | [n2w 0x1c] => SOME ShR
      | [n2w 0x1d] => SOME SAR
      | [n2w 0x20] => SOME Keccak256
      | [n2w 0x30] => SOME Address
      | [n2w 0x31] => SOME Balance
      | [n2w 0x32] => SOME Origin
      | [n2w 0x33] => SOME Caller
      | [n2w 0x34] => SOME CallValue
      | [n2w 0x35] => SOME CallDataLoad
      | [n2w 0x36] => SOME CallDataSize
      | [n2w 0x37] => SOME CallDataCopy
      | [n2w 0x38] => SOME CodeSize
      | [n2w 0x39] => SOME CodeCopy
      | [n2w 0x3a] => SOME GasPrice
      | [n2w 0x3b] => SOME ExtCodeSize
      | [n2w 0x3c] => SOME ExtCodeCopy
      | [n2w 0x3d] => SOME ReturnDataSize
      | [n2w 0x3e] => SOME ReturnDataCopy
      | [n2w 0x3f] => SOME ExtCodeHash
      | [n2w 0x40] => SOME BlockHash
      | [n2w 0x41] => SOME CoinBase
      | [n2w 0x42] => SOME TimeStamp
      | [n2w 0x43] => SOME Number
      | [n2w 0x44] => SOME PrevRandao
      | [n2w 0x45] => SOME GasLimit
      | [n2w 0x46] => SOME ChainId
      | [n2w 0x47] => SOME SelfBalance
      | [n2w 0x48] => SOME BaseFee
      | [n2w 0x50] => SOME Pop
      | [n2w 0x51] => SOME MLoad
      | [n2w 0x52] => SOME MStore
      | [n2w 0x53] => SOME MStore8
      | [n2w 0x54] => SOME SLoad
      | [n2w 0x55] => SOME SStore
      | [n2w 0x56] => SOME Jump
      | [n2w 0x57] => SOME JumpI
      | [n2w 0x58] => SOME PC
      | [n2w 0x59] => SOME MSize
      | [n2w 0x5a] => SOME Gas
      | [n2w 0x5b] => SOME JumpDest
      | [n2w 0xf0] => SOME Create
      | [n2w 0xf1] => SOME Call
      | [n2w 0xf2] => SOME CallCode
      | [n2w 0xf3] => SOME Return
      | [n2w 0xf4] => SOME DelegateCall
      | [n2w 0xf5] => SOME Create2
      | [n2w 0xfa] => SOME StaticCall
      | op::rest => if n2w 0x5f ≤ op ∧ op ≤ n2w 0x7f then SOME $ Push (w2w op - n2w 0x5f) rest else
                    if n2w 0x80 ≤ op ∧ op ≤ n2w 0x8f then SOME (Dup (w2w op - n2w 0x81)) else
                    if n2w 0x90 ≤ op ∧ op ≤ n2w 0x9f then SOME (Swap (w2w op - n2w 0x91)) else
                    if n2w 0xa0 ≤ op ∧ op ≤ n2w 0xa4 then SOME (Log (w2w op - n2w 0xa0)) else
                    NONE
      | _ => NONE
End

val _ = cv_trans parse_opcode_exec_def;


        open Tactic;

Triviality parse_opcode_eqv_parse_opcode_exec:
  ∀opc. parse_opcode opc = parse_opcode_exec opc
Proof
  Cases
  \\ EVAL_TAC
  strip_tac
  \\ simp[parse_opcode_def]
  \\ fs[some_def]
  \\ Cases_on ‘opc’

  \\ rw[]
  \\ (
  Cases_on ‘opn’ >> fs[opcode_def]
  )
  \\DEEP_INTRO_TAC some_intro
  \\ Cases_on ‘x’
  \\ (fs[opcode_def])
  \\ rw[]
  \\ Cases_on ‘opc’
  \\ rw[opcode_def]
  \\ rw[parse_opcode_def, parse_opcode_exec_def]
  \\ ‘∃opn. wf_opname opn ∧ opcode opn = []’ by metis_tac []
  \\ rw[some_intro]
QED

val _ = cv_auto_trans parse_opcode_def;
(* TODO: parse_opcode_unique theorem *)
*)

val _ = export_theory();
