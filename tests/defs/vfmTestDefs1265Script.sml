Theory vfmTestDefs1265[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODERipemd160_0.json";
val defs = mapi (define_test "1265") tests;
