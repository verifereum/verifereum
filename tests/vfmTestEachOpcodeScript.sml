open HolKernel boolLib bossLib Parse wordsLib vfmTestLib

val () = new_theory "vfmTestEachOpcode";

fun mk_path s = "tests/BlockchainTests/GeneralStateTests/" ^ s

(* Stop *)
val test_path = mk_path "stInitCodeTest/TransactionCreateStopInInitcode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* Add *)
val test_path = mk_path "VMTests/vmArithmeticTest/add.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 3;

(* Mul *)
val test_path = mk_path "VMTests/vmArithmeticTest/mul.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 6;

(* Sub *)
val test_path = mk_path "VMTests/vmArithmeticTest/sub.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 2;

(* Div *)
val test_path = mk_path "VMTests/vmArithmeticTest/div.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 4;

(* SDiv *)
val test_path = mk_path "VMTests/vmArithmeticTest/sdiv.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 11;

(* Mod *)
val test_path = mk_path "VMTests/vmArithmeticTest/mod.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 1;

(* SMod *)
val test_path = mk_path "VMTests/vmArithmeticTest/smod.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 5;

(* AddMod *)
val test_path = mk_path "VMTests/vmArithmeticTest/addmod.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 12;

(* MulMod *)
val test_path = mk_path "VMTests/vmArithmeticTest/mulmod.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 8;

(* Exp *)
val test_path = mk_path "VMTests/vmArithmeticTest/exp.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 10;

(* SignExtend *)
val test_path = mk_path "VMTests/vmArithmeticTest/signextend.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 7;

(*
LT
GT
SLT
SGT
Eq
IsZero
And
Or
XOr
Not
Byte
ShL
ShR
SAR
Keccak256
Address
Balance
Origin
Caller
CallValue
CallDataLoad
CallDataSize
CallDataCopy
CodeSize
CodeCopy
GasPrice
ExtCodeSize
ExtCodeCopy
ReturnDataSize
ReturnDataCopy
ExtCodeHash
BlockHash
CoinBase
TimeStamp
Number
PrevRandao
GasLimit
ChainId
SelfBalance
BaseFee
Pop
MLoad
MStore
MStore8
SLoad
SStore
Jump
JumpI
PC
MSize
Gas
JumpDest
TLoad
TStore
MCopy
Push num (word8 list)
Dup num
Swap num
Log num
Create
Call
CallCode
Return
DelegateCall
Create2
StaticCall
Revert
Invalid
SelfDestruct
*)

val () = export_theory();
