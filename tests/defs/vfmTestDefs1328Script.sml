Theory vfmTestDefs1328[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/modexp_0_0_0_35000.json";
val defs = mapi (define_test "1328") tests;
