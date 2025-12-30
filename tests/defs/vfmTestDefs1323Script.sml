Theory vfmTestDefs1323[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/ecrecoverWeirdV.json";
val defs = mapi (define_test "1323") tests;
