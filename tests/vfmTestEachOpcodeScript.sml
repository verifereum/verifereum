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

(* LT *)
val test_path = mk_path "VMTests/vmBitwiseLogicOperation/lt.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* GT *)
val test_path = mk_path "VMTests/vmBitwiseLogicOperation/gt.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 1;

(* SLT *)
val test_path = mk_path "VMTests/vmBitwiseLogicOperation/slt.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 2;

(* SGT *)
val test_path = mk_path "VMTests/vmBitwiseLogicOperation/sgt.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 3;

(* Eq *)
val test_path = mk_path "VMTests/vmBitwiseLogicOperation/eq.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 2;

(* IsZero *)
val test_path = mk_path "VMTests/vmBitwiseLogicOperation/iszero.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 1;

(* And *)
val test_path = mk_path "VMTests/vmBitwiseLogicOperation/and.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* Or *)
val test_path = mk_path "VMTests/vmBitwiseLogicOperation/or.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 5;

(* XOr *)
val test_path = mk_path "VMTests/vmBitwiseLogicOperation/xor.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 4;

(* Not *)
val test_path = mk_path "VMTests/vmBitwiseLogicOperation/not.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 3;

(* Byte *)
val test_path = mk_path "VMTests/vmBitwiseLogicOperation/byte.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 9;

(* ShL *)
val test_path = mk_path "stShift/shl_-1_255.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* ShR *)
val test_path = mk_path "stShift/shr_-1_0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* SAR *)
val test_path = mk_path "stShift/sar_2^256-1_255.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* Keccak256 *)
val test_path = mk_path "VMTests/vmTests/sha3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 15;

(* Address *)
val test_path = mk_path "stEIP2930/addressOpcodes.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 25;

(* Balance *)
val test_path = mk_path "stSelfBalance/selfBalanceEqualsBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* TODO Origin *)

(* TODO Caller *)

(* TODO CallValue *)

(* CallDataLoad *)
val test_path = mk_path "VMTests/vmTests/calldataload.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* CallDataSize *)
val test_path = mk_path "VMTests/vmTests/calldatasize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 1;

(* CallDataCopy *)
val test_path = mk_path "VMTests/vmTests/calldatacopy.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 2;

(* TODO CodeSize *)

(* CodeCopy *)
val test_path = mk_path "stMemoryTest/codecopy_dejavu.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* TODO GasPrice *)

val test_path = mk_path "stArgsZeroOneBalance/extcodesizeNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 1;

(* ExtCodeCopy *)
val test_path = mk_path "stSystemOperationsTest/extcodecopy.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* ReturnDataSize *)
val test_path = mk_path "stCreate2/returndatasize_following_successful_create.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* ReturnDataCopy *)
val test_path = mk_path "stBugs/returndatacopyPythonBug_Tue_03_48_41-1432.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 2;

(* ExtCodeHash *)
val test_path = mk_path
  "stExtCodeHash/extCodeHashCreatedAndDeletedAccountRecheckInOuterCall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* TODO BlockHash *)

(* TODO CoinBase *)

(* TODO TimeStamp *)
(* TODO Number *)
(* TODO PrevRandao *)
(* TODO GasLimit *)

(* ChainId *)
val test_path = mk_path "stChainId/chainId.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* SelfBalance *)
val test_path = mk_path "stSelfBalance/selfBalanceUpdate.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* TODO
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
