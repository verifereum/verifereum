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
  parse_opcode (opcs : byte list)
    = case opcs of
     | n2w 0x00 :: rest => SOME Stop
     | n2w 0x01 :: rest => SOME Add 
     | n2w 0x02 :: rest => SOME Mul 
     | n2w 0x03 :: rest => SOME Sub 
     | n2w 0x04  :: rest => SOME Div 
     | n2w 0x05  :: rest => SOME SDiv 
     | n2w 0x06  :: rest => SOME Mod 
     | n2w 0x07  :: rest => SOME SMod 
     | n2w 0x08  :: rest => SOME AddMod 
     | n2w 0x09  :: rest => SOME MulMod 
     | n2w 0x0a  :: rest => SOME Exp 
     | n2w 0x0b  :: rest => SOME SignExtend 
     | n2w 0x10  :: rest => SOME LT 
     | n2w 0x11  :: rest => SOME GT 
     | n2w 0x12  :: rest => SOME SLT 
     | n2w 0x13  :: resgt => SOME SGT 
     | n2w 0x14  :: rest => SOME Eq 
     | n2w 0x15  :: rest => SOME IsZero 
     | n2w 0x16  :: rest => SOME And 
     | n2w 0x17  :: rest => SOME Or 
     | n2w 0x18  :: rest => SOME XOr 
     | n2w 0x19  :: rest => SOME Not 
     | n2w 0x1a  :: rest => SOME Byte 
     | n2w 0x1b  :: rest => SOME ShL 
     | n2w 0x1c  :: rest => SOME ShR 
     | n2w 0x1d  :: rest => SOME SAR 
     | n2w 0x20  :: rest => SOME Keccak256 
     | n2w 0x30  :: rest => SOME Address 
     | n2w 0x31  :: rest => SOME Balance 
     | n2w 0x32  :: rest => SOME Origin 
     | n2w 0x33  :: rest => SOME Caller 
     | n2w 0x34  :: rest => SOME CallValue 
     | n2w 0x35  :: rest => SOME CallDataLoad 
     | n2w 0x36  :: rest => SOME CallDataSize 
     | n2w 0x37  :: rest => SOME CallDataCopy 
     | n2w 0x38  :: rest => SOME CodeSize 
     | n2w 0x39  :: rest => SOME CodeCopy 
     | n2w 0x3a  :: rest => SOME GasPrice 
     | n2w 0x3b  :: rest => SOME ExtCodeSize 
     | n2w 0x3c  :: rest => SOME ExtCodeCopy 
     | n2w 0x3d  :: rest => SOME ReturnDataSize 
     | n2w 0x3e  :: rest => SOME ReturnDataCopy 
     | n2w 0x3f  :: rest => SOME ExtCodeHash 
     | n2w 0x40  :: rest => SOME BlockHash 
     | n2w 0x41  :: rest => SOME CoinBase 
     | n2w 0x42  :: rest => SOME TimeStamp 
     | n2w 0x43  :: rest => SOME Number 
     | n2w 0x44  :: rest => SOME PrevRandao 
     | n2w 0x45  :: rest => SOME GasLimit 
     | n2w 0x46  :: rest => SOME ChainId 
     | n2w 0x47  :: rest => SOME SelfBalance 
     | n2w 0x48  :: rest => SOME BaseFee 
     | n2w 0x50  :: rest => SOME Pop 
     | n2w 0x51  :: rest => SOME MLoad 
     | n2w 0x52  :: rest => SOME MStore 
     | n2w 0x53  :: rest => SOME MStore8 
     | n2w 0x54  :: rest => SOME SLoad 
     | n2w 0x55  :: rest => SOME SStore 
     | n2w 0x56  :: rest => SOME Jump 
     | n2w 0x57  :: rest => SOME JumpI 
     | n2w 0x58  :: rest => SOME PC 
     | n2w 0x59  :: rest => SOME MSize 
     | n2w 0x5a  :: rest => SOME Gas 
     | n2w 0x5b  :: rest => SOME JumpDest 
     | n2w 0x5f  :: rest => if LENGTH rest >= 0 then SOME $ Push 0  (TAKE 0 rest) else NONE 
     | n2w 0x60  :: rest => if LENGTH rest >= 1 then SOME $ Push 1  (TAKE 1 rest) else NONE 
     | n2w 0x61  :: rest => if LENGTH rest >= 2 then SOME $ Push 2  (TAKE 2 rest) else NONE 
     | n2w 0x62  :: rest => if LENGTH rest >= 3 then SOME $ Push 3  (TAKE 3 rest) else NONE 
     | n2w 0x63  :: rest => if LENGTH rest >= 4 then SOME $ Push 4  (TAKE 4 rest) else NONE 
     | n2w 0x64  :: rest => if LENGTH rest >= 5 then SOME $ Push 5  (TAKE 5 rest) else NONE 
     | n2w 0x65  :: rest => if LENGTH rest >= 6 then SOME $ Push 6  (TAKE 6 rest) else NONE 
     | n2w 0x66  :: rest => if LENGTH rest >= 7 then SOME $ Push 7  (TAKE 7 rest) else NONE 
     | n2w 0x67  :: rest => if LENGTH rest >= 8 then SOME $ Push 8  (TAKE 8 rest) else NONE 
     | n2w 0x68  :: rest => if LENGTH rest >= 9 then SOME $ Push 9  (TAKE 9 rest) else NONE 
     | n2w 0x69  :: rest => if LENGTH rest >= 10 then SOME $ Push 10 (TAKE 10 rest) else NONE 
     | n2w 0x6a  :: rest => if LENGTH rest >= 11 then SOME $ Push 11 (TAKE 11 rest) else NONE 
     | n2w 0x6b  :: rest => if LENGTH rest >= 12 then SOME $ Push 12 (TAKE 12 rest) else NONE 
     | n2w 0x6c  :: rest => if LENGTH rest >= 13 then SOME $ Push 13 (TAKE 13 rest) else NONE 
     | n2w 0x6d  :: rest => if LENGTH rest >= 14 then SOME $ Push 14 (TAKE 14 rest) else NONE 
     | n2w 0x6e  :: rest => if LENGTH rest >= 15 then SOME $ Push 15 (TAKE 15 rest) else NONE 
     | n2w 0x6f  :: rest => if LENGTH rest >= 16 then SOME $ Push 16 (TAKE 16 rest) else NONE 
     | n2w 0x70  :: rest => if LENGTH rest >= 17 then SOME $ Push 17 (TAKE 17 rest) else NONE 
     | n2w 0x71  :: rest => if LENGTH rest >= 18 then SOME $ Push 18 (TAKE 18 rest) else NONE 
     | n2w 0x72  :: rest => if LENGTH rest >= 19 then SOME $ Push 19 (TAKE 19 rest) else NONE 
     | n2w 0x73  :: rest => if LENGTH rest >= 20 then SOME $ Push 20 (TAKE 20 rest) else NONE 
     | n2w 0x74  :: rest => if LENGTH rest >= 21 then SOME $ Push 21 (TAKE 21 rest) else NONE 
     | n2w 0x75  :: rest => if LENGTH rest >= 22 then SOME $ Push 22 (TAKE 22 rest) else NONE 
     | n2w 0x76  :: rest => if LENGTH rest >= 23 then SOME $ Push 23 (TAKE 23 rest) else NONE 
     | n2w 0x77  :: rest => if LENGTH rest >= 24 then SOME $ Push 24 (TAKE 24 rest) else NONE 
     | n2w 0x78  :: rest => if LENGTH rest >= 25 then SOME $ Push 25 (TAKE 25 rest) else NONE 
     | n2w 0x79  :: rest => if LENGTH rest >= 26 then SOME $ Push 26 (TAKE 26 rest) else NONE 
     | n2w 0x7a  :: rest => if LENGTH rest >= 27 then SOME $ Push 27 (TAKE 27 rest) else NONE 
     | n2w 0x7b  :: rest => if LENGTH rest >= 28 then SOME $ Push 28 (TAKE 28 rest) else NONE 
     | n2w 0x7c  :: rest => if LENGTH rest >= 29 then SOME $ Push 29 (TAKE 29 rest) else NONE 
     | n2w 0x7d  :: rest => if LENGTH rest >= 30 then SOME $ Push 30 (TAKE 30 rest) else NONE 
     | n2w 0x7e  :: rest => if LENGTH rest >= 31 then SOME $ Push 31 (TAKE 31 rest) else NONE 
     | n2w 0x7f  :: rest => if LENGTH rest >= 32 then SOME $ Push 32 (TAKE 32 rest) else NONE 
     | n2w 0x80  :: rest => SOME $ Dup 0 
     | n2w 0x81  :: rest => SOME $ Dup 1 
     | n2w 0x82  :: rest => SOME $ Dup 2 
     | n2w 0x83  :: rest => SOME $ Dup 3 
     | n2w 0x84  :: rest => SOME $ Dup 4 
     | n2w 0x85  :: rest => SOME $ Dup 5 
     | n2w 0x86  :: rest => SOME $ Dup 6 
     | n2w 0x87  :: rest => SOME $ Dup 7 
     | n2w 0x88  :: rest => SOME $ Dup 8 
     | n2w 0x89  :: rest => SOME $ Dup 9 
     | n2w 0x8a  :: rest => SOME $ Dup 10 
     | n2w 0x8b  :: rest => SOME $ Dup 11 
     | n2w 0x8c  :: rest => SOME $ Dup 12 
     | n2w 0x8d  :: rest => SOME $ Dup 13 
     | n2w 0x8e  :: rest => SOME $ Dup 14 
     | n2w 0x8f  :: rest => SOME $ Dup 15 
     | n2w 0x90  :: rest => SOME $ Swap 0 
     | n2w 0x91  :: rest => SOME $ Swap 1 
     | n2w 0x92  :: rest => SOME $ Swap 2 
     | n2w 0x93  :: rest => SOME $ Swap 3 
     | n2w 0x94  :: rest => SOME $ Swap 4 
     | n2w 0x95  :: rest => SOME $ Swap 5 
     | n2w 0x96  :: rest => SOME $ Swap 6 
     | n2w 0x97  :: rest => SOME $ Swap 7 
     | n2w 0x98  :: rest => SOME $ Swap 8 
     | n2w 0x99  :: rest => SOME $ Swap 9
     | n2w 0x9a  :: rest => SOME $ Swap 10 
     | n2w 0x9b  :: rest => SOME $ Swap 11 
     | n2w 0x9c  :: rest => SOME $ Swap 12 
     | n2w 0x9d  :: rest => SOME $ Swap 13 
     | n2w 0x9e  :: rest => SOME $ Swap 14
     | n2w 0x9f  :: rest => SOME $ Swap 15
     | n2w 0xa0  :: rest => SOME $ Log 0 
     | n2w 0xa1  :: rest => SOME $ Log 1 
     | n2w 0xa2  :: rest => SOME $ Log 2 
     | n2w 0xa3  :: rest => SOME $ Log 3
     | n2w 0xf0  :: rest => SOME Create 
     | n2w 0xf1  :: rest => SOME Call 
     | n2w 0xf2  :: rest => SOME CallCode 
     | n2w 0xf3  :: rest => SOME Return 
     | n2w 0xf4  :: rest => SOME DelegateCall 
     | n2w 0xf5  :: rest => SOME Create2 
     | n2w 0xfa  :: rest => SOME StaticCall 
     | n2w 0xfd  :: rest => SOME Revert 
     | _ => NONE
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
  \\ Cases_on ‘opcs’
  \\ rw[wf_opname_def, opcode_def]
  \\ let
    val def_cases = opcode_def |> concl |> strip_conj |> List.map
      (fn tm => (EXISTS_TAC(rand (lhs tm)) handle HOL_ERR _ => NO_TAC)
                \\ rw[opcode_def] \\ NO_TAC)
    val push_cases =  List.tabulate(33, (fn n =>
          let val nn = numSyntax.term_of_int n
          in EXISTS_TAC “Push ^nn (TAKE ^nn t)” \\ rw[opcode_def, wf_opname_def]
             \\ rw[rich_listTheory.IS_PREFIX_EQ_TAKE] \\ EXISTS_TAC nn \\ rw[]
          end))
    fun mk_x_cases m tm = List.tabulate(m, fn n =>
      let val nn = numSyntax.term_of_int n in
        EXISTS_TAC (mk_comb (tm, nn)) \\ rw[opcode_def, wf_opname_def] \\ NO_TAC
      end)
    val dup_cases = mk_x_cases 16 ``Dup``
    val swap_cases = mk_x_cases 16 ``Swap``
    val log_cases = mk_x_cases 4 ``Log``
  in
    TRY $ FIRST (def_cases @ push_cases @ dup_cases @ swap_cases @ log_cases)
  end
QED

open cv_transLib cv_stdTheory;
cv_auto_trans parse_opcode_cond_thm

val _ = export_theory();
