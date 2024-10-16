open HolKernel boolLib bossLib Parse
     wordsLib blastLib
     listTheory rich_listTheory optionTheory
     arithmeticTheory wordsTheory
     vfmTypesTheory
     cv_transLib cv_stdTheory;

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
  | Push num (word8 list)
  | Dup num
  | Swap num
  | Log num
  | Create
  | Call
  | CallCode
  | Return
  | DelegateCall
  | Create2
  | StaticCall
  | Revert
  | SelfDestruct
End

Definition wf_opname_def[simp]:
    wf_opname (Push n w) = (n ≤ 32 ∧ LENGTH w = n)
  ∧ wf_opname (Log n) = (n < 4)
  ∧ wf_opname (Dup n) = (n < 16)
  ∧ wf_opname (Swap n) = (n < 16)
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
  ∧ opcode (Push n w)     = [n2w 0x5f + n2w n] ++ w
  ∧ opcode (Dup n)        = [n2w 0x80 + n2w n]
  ∧ opcode (Swap n)       = [n2w 0x90 + n2w n]
  ∧ opcode (Log n)        = [n2w 0xa0 + n2w n]
  ∧ opcode Create         = [n2w 0xf0]
  ∧ opcode Call           = [n2w 0xf1]
  ∧ opcode CallCode       = [n2w 0xf2]
  ∧ opcode Return         = [n2w 0xf3]
  ∧ opcode DelegateCall   = [n2w 0xf4]
  ∧ opcode Create2        = [n2w 0xf5]
  ∧ opcode StaticCall     = [n2w 0xfa]
  ∧ opcode Revert         = [n2w 0xfd]
  ∧ opcode SelfDestruct   = [n2w 0xff]
End

Definition invalid_opcode_def:
  invalid_opcode : byte = n2w 0xfe
End

Definition parse_opcode_def:
  parse_opcode (opc:byte list) =
    some opn. wf_opname opn ∧
      ∃n. opcode opn ≼ opc ++ REPLICATE n 0w
End

Definition static_gas_def[simp]:
    static_gas Stop           = 0n
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
  ∧ static_gas Address        = 2
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
  ∧ static_gas (Push n w)     = (if n = 0 then 2 else 3)
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
  ∧ static_gas SelfDestruct   = 5000
End

Definition take_pad_0_def:
  take_pad_0 z l = PAD_RIGHT 0w z (TAKE z l)
End

Theorem take_pad_0_0[simp]:
  take_pad_0 0 l = []
Proof
  rw[take_pad_0_def, PAD_RIGHT]
QED

Theorem LENGTH_take_pad_0[simp]:
  LENGTH (take_pad_0 z l) = z
Proof
  rw[take_pad_0_def, bitstringTheory.length_pad_right, LENGTH_TAKE_EQ]
QED

Theorem take_pad_0_IS_PREFIX:
  ∃m. take_pad_0 n t ≼ t ++ REPLICATE m 0w
Proof
  rw[take_pad_0_def, PAD_RIGHT, IS_PREFIX_APPEND]
  \\ `t = TAKE n t ++ DROP n t` by simp[]
  \\ pop_assum(fn th => CONV_TAC(STRIP_QUANT_CONV(LAND_CONV(ONCE_REWRITE_CONV[th]))))
  \\ simp[REPLICATE_GENLIST, LENGTH_TAKE_EQ]
  \\ rw[DROP_LENGTH_TOO_LONG]
  \\ qexists_tac`n - LENGTH t` \\ rw[]
QED

(* TODO: move *)

Theorem REPLICATE_EQ_CONS:
  REPLICATE n x = y :: r <=> y = x /\ ?m. n = SUC m /\ r = REPLICATE m x
Proof
  Cases_on`n` \\ rw[rich_listTheory.REPLICATE, EQ_IMP_THM]
QED

(* -- *)

Theorem parse_opcode_cond_thm:
  parse_opcode (opcs: byte list) =
  case opcs of
  | [] => SOME Stop
  | opc::rest =>
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
      if opc = n2w 0x5f then SOME (Push 0  (take_pad_0 0  rest)) else
      if opc = n2w 0x60 then SOME (Push 1  (take_pad_0 1  rest)) else
      if opc = n2w 0x61 then SOME (Push 2  (take_pad_0 2  rest)) else
      if opc = n2w 0x62 then SOME (Push 3  (take_pad_0 3  rest)) else
      if opc = n2w 0x63 then SOME (Push 4  (take_pad_0 4  rest)) else
      if opc = n2w 0x64 then SOME (Push 5  (take_pad_0 5  rest)) else
      if opc = n2w 0x65 then SOME (Push 6  (take_pad_0 6  rest)) else
      if opc = n2w 0x66 then SOME (Push 7  (take_pad_0 7  rest)) else
      if opc = n2w 0x67 then SOME (Push 8  (take_pad_0 8  rest)) else
      if opc = n2w 0x68 then SOME (Push 9  (take_pad_0 9  rest)) else
      if opc = n2w 0x69 then SOME (Push 10 (take_pad_0 10 rest)) else
      if opc = n2w 0x6a then SOME (Push 11 (take_pad_0 11 rest)) else
      if opc = n2w 0x6b then SOME (Push 12 (take_pad_0 12 rest)) else
      if opc = n2w 0x6c then SOME (Push 13 (take_pad_0 13 rest)) else
      if opc = n2w 0x6d then SOME (Push 14 (take_pad_0 14 rest)) else
      if opc = n2w 0x6e then SOME (Push 15 (take_pad_0 15 rest)) else
      if opc = n2w 0x6f then SOME (Push 16 (take_pad_0 16 rest)) else
      if opc = n2w 0x70 then SOME (Push 17 (take_pad_0 17 rest)) else
      if opc = n2w 0x71 then SOME (Push 18 (take_pad_0 18 rest)) else
      if opc = n2w 0x72 then SOME (Push 19 (take_pad_0 19 rest)) else
      if opc = n2w 0x73 then SOME (Push 20 (take_pad_0 20 rest)) else
      if opc = n2w 0x74 then SOME (Push 21 (take_pad_0 21 rest)) else
      if opc = n2w 0x75 then SOME (Push 22 (take_pad_0 22 rest)) else
      if opc = n2w 0x76 then SOME (Push 23 (take_pad_0 23 rest)) else
      if opc = n2w 0x77 then SOME (Push 24 (take_pad_0 24 rest)) else
      if opc = n2w 0x78 then SOME (Push 25 (take_pad_0 25 rest)) else
      if opc = n2w 0x79 then SOME (Push 26 (take_pad_0 26 rest)) else
      if opc = n2w 0x7a then SOME (Push 27 (take_pad_0 27 rest)) else
      if opc = n2w 0x7b then SOME (Push 28 (take_pad_0 28 rest)) else
      if opc = n2w 0x7c then SOME (Push 29 (take_pad_0 29 rest)) else
      if opc = n2w 0x7d then SOME (Push 30 (take_pad_0 30 rest)) else
      if opc = n2w 0x7e then SOME (Push 31 (take_pad_0 31 rest)) else
      if opc = n2w 0x7f then SOME (Push 32 (take_pad_0 32 rest)) else
      if opc = n2w 0x80 then SOME (Dup 0) else
      if opc = n2w 0x81 then SOME (Dup 1) else
      if opc = n2w 0x82 then SOME (Dup 2) else
      if opc = n2w 0x83 then SOME (Dup 3) else
      if opc = n2w 0x84 then SOME (Dup 4) else
      if opc = n2w 0x85 then SOME (Dup 5) else
      if opc = n2w 0x86 then SOME (Dup 6) else
      if opc = n2w 0x87 then SOME (Dup 7) else
      if opc = n2w 0x88 then SOME (Dup 8) else
      if opc = n2w 0x89 then SOME (Dup 9) else
      if opc = n2w 0x8a then SOME (Dup 10) else
      if opc = n2w 0x8b then SOME (Dup 11) else
      if opc = n2w 0x8c then SOME (Dup 12) else
      if opc = n2w 0x8d then SOME (Dup 13) else
      if opc = n2w 0x8e then SOME (Dup 14) else
      if opc = n2w 0x8f then SOME (Dup 15) else
      if opc = n2w 0x90 then SOME (Swap 0) else
      if opc = n2w 0x91 then SOME (Swap 1) else
      if opc = n2w 0x92 then SOME (Swap 2) else
      if opc = n2w 0x93 then SOME (Swap 3) else
      if opc = n2w 0x94 then SOME (Swap 4) else
      if opc = n2w 0x95 then SOME (Swap 5) else
      if opc = n2w 0x96 then SOME (Swap 6) else
      if opc = n2w 0x97 then SOME (Swap 7) else
      if opc = n2w 0x98 then SOME (Swap 8) else
      if opc = n2w 0x99 then SOME (Swap 9) else
      if opc = n2w 0x9a then SOME (Swap 10) else
      if opc = n2w 0x9b then SOME (Swap 11) else
      if opc = n2w 0x9c then SOME (Swap 12) else
      if opc = n2w 0x9d then SOME (Swap 13) else
      if opc = n2w 0x9e then SOME (Swap 14) else
      if opc = n2w 0x9f then SOME (Swap 15) else
      if opc = n2w 0xa0 then SOME (Log 0) else
      if opc = n2w 0xa1 then SOME (Log 1) else
      if opc = n2w 0xa2 then SOME (Log 2) else
      if opc = n2w 0xa3 then SOME (Log 3) else
      if opc = n2w 0xf0 then SOME Create else
      if opc = n2w 0xf1 then SOME Call else
      if opc = n2w 0xf2 then SOME CallCode else
      if opc = n2w 0xf3 then SOME Return else
      if opc = n2w 0xf4 then SOME DelegateCall else
      if opc = n2w 0xf5 then SOME Create2 else
      if opc = n2w 0xfa then SOME StaticCall else
      if opc = n2w 0xfd then SOME Revert else
      if opc = n2w 0xff then SOME SelfDestruct else
      NONE
Proof
  rewrite_tac[parse_opcode_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ simp_tac std_ss [CaseEq"list", CaseEq"bool", PULL_EXISTS]
  \\ CONJ_TAC
  >- (
    Cases \\ simp_tac (srw_ss()) [
      opcode_def, IS_PREFIX_APPEND, PULL_EXISTS,
      APPEND_EQ_CONS, REPLICATE_EQ_CONS
    ]
    >- srw_tac[DNF_ss][]
    \\ rpt gen_tac
    \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[NUMERAL_LESS_THM, LESS_OR_EQ]))
    \\ strip_tac \\ gvs[take_pad_0_def, PAD_RIGHT]
    \\ pop_assum mp_tac
    \\ simp[LIST_EQ_REWRITE, EL_APPEND_EQN, EL_REPLICATE, LENGTH_TAKE_EQ,
            EL_TAKE, LENGTH_REPLICATE, GSYM AND_IMP_INTRO]
    \\ rw[] \\ rw[]
    \\ TRY(first_x_assum(qspec_then`x`mp_tac) \\ simp[] \\ NO_TAC)
    \\ gvs[LENGTH_EQ_NUM_compute]
    \\ first_x_assum(qspec_then`0`mp_tac) \\ simp[])
  \\ Cases_on ‘opcs’ \\ simp[wf_opname_def, opcode_def]
  >- (
    qexists_tac`Stop` \\ rw[opcode_def]
    \\ qexists_tac`SUC 0` \\ rw[rich_listTheory.REPLICATE] )
  \\ strip_tac
  \\ CCONTR_TAC \\ gvs[]
  \\ pop_assum mp_tac \\ simp[PULL_EXISTS]
  \\ let
    val def_cases = opcode_def |> concl |> strip_conj |> List.map
      (fn tm => (EXISTS_TAC(rand (lhs tm)) handle HOL_ERR _ => NO_TAC)
                \\ rw[opcode_def] \\ NO_TAC)
    val push_cases =  List.tabulate(33, (fn n =>
          let
            val nn = numSyntax.term_of_int n
          in
            EXISTS_TAC “Push ^nn (take_pad_0 ^nn t)”
            \\ simp[wf_opname_def, opcode_def, take_pad_0_IS_PREFIX]
            \\ NO_TAC
          end))
    fun mk_x_cases m tm = List.tabulate(m, fn n =>
      let val nn = numSyntax.term_of_int n in
        EXISTS_TAC (mk_comb (tm, nn)) \\ rw[opcode_def, wf_opname_def] \\ NO_TAC
      end)
    val dup_cases = mk_x_cases 16 “Dup”
    val swap_cases = mk_x_cases 16 “Swap”
    val log_cases = mk_x_cases 4 “Log”
  in
    TRY $ FIRST (def_cases @ push_cases @ dup_cases @ swap_cases @ log_cases)
  end
QED

val _ = cv_auto_trans parse_opcode_cond_thm

Theorem opcode_not_null[simp]:
  ¬ NULL (opcode op)
Proof
  Cases_on`op` \\ rw[opcode_def]
QED

val _ = export_theory();
