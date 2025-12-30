Theory vfmTestDefs0913[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150Specific/SuicideToNotExistingContract.json";
val defs = mapi (define_test "0913") tests;
