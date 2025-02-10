open HolKernel boolLib bossLib Parse wordsLib vfmTestLib

val () = new_theory "vfmTestEachOpcode";

fun mk_path s = "tests/BlockchainTests/GeneralStateTests/" ^ s

(* BlockHash *)
val test_path =
  "tests/BlockchainTests/ValidBlocks/bcStateTests/blockhashTests.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

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

(* Origin *)
val test_path = mk_path "stSystemOperationsTest/suicideOrigin.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* Caller *)
val test_path = mk_path "stSystemOperationsTest/callerAccountBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* CallValue *)
val test_path = mk_path "stSystemOperationsTest/callValue.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

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

(* CodeSize *)
val test_path = mk_path "stCodeSizeLimit/codesizeValid.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 1;

(* CodeCopy *)
val test_path = mk_path "stMemoryTest/codecopy_dejavu.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* GasPrice *)
val test_path = mk_path "stEIP1559/gasPriceDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 11;

(* ExtCodeSize *)
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

(* CoinBase *)
val test_path = mk_path "VMTests/vmTests/blockInfo.json"
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* TimeStamp *)
val test_path = mk_path "VMTests/vmTests/blockInfo.json"
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 4;

(* Number *)
val test_path = mk_path "VMTests/vmTests/blockInfo.json"
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 3;

(* Difficulty/prevrandao *)
val test_path = mk_path "VMTests/vmTests/blockInfo.json"
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 1;

(* GasLimit *)
val test_path = mk_path "VMTests/vmTests/blockInfo.json"
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 2;

(* ChainId *)
val test_path = mk_path "stChainId/chainId.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* SelfBalance *)
val test_path = mk_path "stSelfBalance/selfBalanceUpdate.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* BaseFee *)
val test_path = mk_path "stExample/basefeeExample.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* Pop *)
val test_path = mk_path "VMTests/vmIOandFlowOperations/pop.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 1;

(* MLoad *)
val test_path = mk_path "VMTests/vmIOandFlowOperations/mload.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* MStore *)
val test_path = mk_path "VMTests/vmIOandFlowOperations/mstore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 2;

(* MStore8 *)
val test_path = mk_path "VMTests/vmIOandFlowOperations/mstore8.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 1;

(* SLoad *)
val test_path = mk_path "VMTests/vmIOandFlowOperations/sstore_sload.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 2;

(* SStore *)
val test_path = mk_path "stSStoreTest/sstore_Xto0toXto0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 16;

(* Jump *)
val test_path = mk_path "VMTests/vmIOandFlowOperations/jump.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 14;

(* JumpI *)
val test_path = mk_path "VMTests/vmIOandFlowOperations/jumpi.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 22;

(* PC *)
val test_path = mk_path "VMTests/vmIOandFlowOperations/pc.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 1;

(* MSize *)
val test_path = mk_path "VMTests/vmIOandFlowOperations/msize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 4;

(* Gas *)
val test_path = mk_path "stNonZeroCallsTest/NonZeroValue_CALLCODE_ToEmpty_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* JumpDest *)
val test_path = mk_path "VMTests/vmIOandFlowOperations/jumpToPush.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 64;

(* TLoad *)
val test_path = mk_path
  "Cancun/stEIP1153-transientStorage/transStorageOK.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 12;

(* TStore *)
val test_path = mk_path
  "Cancun/stEIP1153-transientStorage/19_oogUndoesTransientStore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* MCopy *)
val test_path = mk_path "stMemoryTest/memCopySelf.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* Push *)
val test_path = mk_path "VMTests/vmTests/push.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 12;

(* Dup *)
val test_path = mk_path "VMTests/vmTests/dup.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 7;

(* Swap *)
val test_path = mk_path "VMTests/vmTests/swap.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 14;

(* Log *)
val test_path = mk_path "VMTests/vmLogTest/log3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 9;

(* Create *)
val test_path = mk_path "stArgsZeroOneBalance/createNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 1;

(* Call *)
val test_path = mk_path "stCallCodes/callcallcall_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* CallCode *)
val test_path = mk_path "stCallCodes/callcallcodecall_010_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* Return *)
val test_path = mk_path "stInitCodeTest/ReturnTest2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* DelegateCall *)
val test_path = mk_path
  "stNonZeroCallsTest/NonZeroValue_DELEGATECALL_ToNonNonZeroBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* Create2 *)
val test_path = mk_path "stCreate2/CREATE2_HighNonceMinus1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* StaticCall *)
val test_path = mk_path "stStaticCall/static_ABAcalls3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 1;

(* Revert *)
val test_path = mk_path "stRevertTest/RevertDepth2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 1;

(* Invalid *)
val test_path = mk_path "stSystemOperationsTest/createWithInvalidOpcode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 0;

(* SelfDestruct *)
val test_path = mk_path "VMTests/vmTests/suicide.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thm = prove_test 2;

val () = export_theory();
