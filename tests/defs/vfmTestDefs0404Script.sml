Theory vfmTestDefs0404[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP1153_transientStorage/17_tstoreGas.json";
val defs = mapi (define_test "0404") tests;
