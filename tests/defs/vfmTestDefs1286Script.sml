Theory vfmTestDefs1286[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecover0_Gas2999.json";
val defs = mapi (define_test "1286") tests;
