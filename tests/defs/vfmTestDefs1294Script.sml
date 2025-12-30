Theory vfmTestDefs1294[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecover80.json";
val defs = mapi (define_test "1294") tests;
