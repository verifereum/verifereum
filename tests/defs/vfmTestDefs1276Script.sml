Theory vfmTestDefs1276[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODESha256_1_nonzeroValue.json";
val defs = mapi (define_test "1276") tests;
