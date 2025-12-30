Theory vfmTestDefs1293[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecover3.json";
val defs = mapi (define_test "1293") tests;
