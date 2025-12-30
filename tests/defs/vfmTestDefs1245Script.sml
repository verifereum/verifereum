Theory vfmTestDefs1245[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts/modexp.json";
val defs = mapi (define_test "1245") tests;
