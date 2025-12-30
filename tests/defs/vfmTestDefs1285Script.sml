Theory vfmTestDefs1285[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecover0_0input.json";
val defs = mapi (define_test "1285") tests;
