Theory vfmTestDefs1297[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecoverH_prefixed0.json";
val defs = mapi (define_test "1297") tests;
