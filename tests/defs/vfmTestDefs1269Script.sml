Theory vfmTestDefs1269[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODERipemd160_3_postfixed0.json";
val defs = mapi (define_test "1269") tests;
