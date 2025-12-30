Theory vfmTestDefs1273[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODERipemd160_5.json";
val defs = mapi (define_test "1273") tests;
