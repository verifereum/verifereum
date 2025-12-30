Theory vfmTestDefs0409[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP4844_blobtransactions/emptyBlobhashList.json";
val defs = mapi (define_test "0409") tests;
