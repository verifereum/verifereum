Theory vfmTestDefs2486[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/SuicidesAndInternalCallSuicidesBonusGasAtCallFailed.json";
val defs = mapi (define_test "2486") tests;
