Theory vfmTestDefs1282[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODESha256_4_gas99.json";
val defs = mapi (define_test "1282") tests;
