Theory vfmTestDefs0405[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP1153_transientStorage/19_oogUndoesTransientStore.json";
val defs = mapi (define_test "0405") tests;
