Theory vfmTestDefs0406[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP1153_transientStorage/transStorageOK.json";
val defs = mapi (define_test "0406") tests;
