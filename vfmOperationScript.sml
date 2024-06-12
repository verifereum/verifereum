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
End


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
  if opc = n2w 0x5f ∧ LENGTH rest >= 0 then SOME (Push 0  (TAKE 0 rest)) else
  if opc = n2w 0x60 ∧ LENGTH rest >= 1 then SOME (Push 1  (TAKE 1 rest)) else
  if opc = n2w 0x61 ∧ LENGTH rest >= 2 then SOME (Push 2  (TAKE 2 rest)) else
  if opc = n2w 0x62 ∧ LENGTH rest >= 3 then SOME (Push 3  (TAKE 3 rest)) else
  if opc = n2w 0x63 ∧ LENGTH rest >= 4 then SOME (Push 4  (TAKE 4 rest)) else
  if opc = n2w 0x64 ∧ LENGTH rest >= 5 then SOME (Push 5  (TAKE 5 rest)) else
  if opc = n2w 0x65 ∧ LENGTH rest >= 6 then SOME (Push 6  (TAKE 6 rest)) else
  if opc = n2w 0x66 ∧ LENGTH rest >= 7 then SOME (Push 7  (TAKE 7 rest)) else
  if opc = n2w 0x67 ∧ LENGTH rest >= 8 then SOME (Push 8  (TAKE 8 rest)) else
  if opc = n2w 0x68 ∧ LENGTH rest >= 9 then SOME (Push 9  (TAKE 9 rest)) else
  if opc = n2w 0x69 ∧ LENGTH rest >= 10 then SOME (Push 10 (TAKE 10 rest)) else
  if opc = n2w 0x6a ∧ LENGTH rest >= 11 then SOME (Push 11 (TAKE 11 rest)) else
  if opc = n2w 0x6b ∧ LENGTH rest >= 12 then SOME (Push 12 (TAKE 12 rest)) else
  if opc = n2w 0x6c ∧ LENGTH rest >= 13 then SOME (Push 13 (TAKE 13 rest)) else
  if opc = n2w 0x6d ∧ LENGTH rest >= 14 then SOME (Push 14 (TAKE 14 rest)) else
  if opc = n2w 0x6e ∧ LENGTH rest >= 15 then SOME (Push 15 (TAKE 15 rest)) else
  if opc = n2w 0x6f ∧ LENGTH rest >= 16 then SOME (Push 16 (TAKE 16 rest)) else
  if opc = n2w 0x70 ∧ LENGTH rest >= 17 then SOME (Push 17 (TAKE 17 rest)) else
  if opc = n2w 0x71 ∧ LENGTH rest >= 18 then SOME (Push 18 (TAKE 18 rest)) else
  if opc = n2w 0x72 ∧ LENGTH rest >= 19 then SOME (Push 19 (TAKE 19 rest)) else
  if opc = n2w 0x73 ∧ LENGTH rest >= 20 then SOME (Push 20 (TAKE 20 rest)) else
  if opc = n2w 0x74 ∧ LENGTH rest >= 21 then SOME (Push 21 (TAKE 21 rest)) else
  if opc = n2w 0x75 ∧ LENGTH rest >= 22 then SOME (Push 22 (TAKE 22 rest)) else
  if opc = n2w 0x76 ∧ LENGTH rest >= 23 then SOME (Push 23 (TAKE 23 rest)) else
  if opc = n2w 0x77 ∧ LENGTH rest >= 24 then SOME (Push 24 (TAKE 24 rest)) else
  if opc = n2w 0x78 ∧ LENGTH rest >= 25 then SOME (Push 25 (TAKE 25 rest)) else
  if opc = n2w 0x79 ∧ LENGTH rest >= 26 then SOME (Push 26 (TAKE 26 rest)) else
  if opc = n2w 0x7a ∧ LENGTH rest >= 27 then SOME (Push 27 (TAKE 27 rest)) else
  if opc = n2w 0x7b ∧ LENGTH rest >= 28 then SOME (Push 28 (TAKE 28 rest)) else
  if opc = n2w 0x7c ∧ LENGTH rest >= 29 then SOME (Push 29 (TAKE 29 rest)) else
  if opc = n2w 0x7d ∧ LENGTH rest >= 30 then SOME (Push 30 (TAKE 30 rest)) else
  if opc = n2w 0x7e ∧ LENGTH rest >= 31 then SOME (Push 31 (TAKE 31 rest)) else
  if opc = n2w 0x7f ∧ LENGTH rest >= 32 then SOME (Push 32 (TAKE 32 rest)) else
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
  NONE
Proof
  simp[parse_opcode_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ CONJ_TAC
  >- (
  Cases
  \\ simp [rich_listTheory.IS_PREFIX_APPEND, opcode_def]
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[wordsTheory.NUMERAL_LESS_THM, arithmeticTheory.LESS_OR_EQ]))
  \\ strip_tac
  \\ rw[rich_listTheory.TAKE_APPEND]
  \\ fs[listTheory.LENGTH_NIL]
  )

  val def_cases =  opcode_def |> concl |> strip_conj |> List.map (fn tm => (EXISTS_TAC(rand (lhs tm)) \\ rw[opcode_def] \\ NO_TAC)
                                                                handle HOL_ERR _ => ALL_TAC)
val push_cases =  List.tabulate(33, (fn n =>
                                       let val nn = numSyntax.term_of_int n
                                       in (EXISTS_TAC “Push ^nn (TAKE ^nn rest)” \\ rw[opcode_def, wf_opname_def]
                                           \\ rw[rich_listTheory.IS_PREFIX_EQ_TAKE] \\ EXISTS_TAC nn \\ rw[])
                                          end))
    \\ rw[]
    \\ FIRST def_cases
    \\ TRY (FIRST push_cases)

  
\\ TRY $ FIRST(
     List.tabulate(16, (fn n =>
                          let val nn = numSyntax.term_of_int n
                          in (EXISTS_TAC “Dup ^nn” \\ rw[opcode_def, wf_opname_def] \\ NO_TAC) end))
     )   

\\ TRY $ FIRST(
       List.tabulate(16, (fn n =>
                            let val nn = numSyntax.term_of_int n in (EXISTS_TAC “Swap ^nn” \\ rw[opcode_def, wf_opname_def] \\ NO_TAC) end))
       )
\\ TRY $ FIRST(
    List.tabulate(4, (fn n =>
       let val nn = numSyntax.term_of_int n in (EXISTS_TAC “Log ^nn” \\ rw[opcode_def, wf_opname_def] \\ NO_TAC) end))
    )

\\ qexists ‘Create’ \\ rw[opcode_def]
\\ qexists ‘Call’ \\ rw[opcode_def] 
\\ qexists ‘CallCode’ \\ rw[opcode_def]
\\ qexists ‘Return’ \\ rw[opcode_def]
\\ qexists ‘DelegateCall’ \\ rw[opcode_def]
\\ qexists ‘Create2’ \\ rw[opcode_def] 
\\ qexists ‘StaticCall’ \\ rw[opcode_def]
\\ qexists ‘Revert’ \\ rw[opcode_def]
    

QED

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
