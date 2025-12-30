Theory vfmTestDefs0476[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmTests/envInfo.json";
val defs = mapi (define_test "0476") tests;
