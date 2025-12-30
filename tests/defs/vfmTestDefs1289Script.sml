Theory vfmTestDefs1289[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecover0_gas3000.json";
val defs = mapi (define_test "1289") tests;
