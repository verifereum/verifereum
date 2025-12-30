Theory vfmTestDefs1292[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecover2.json";
val defs = mapi (define_test "1292") tests;
