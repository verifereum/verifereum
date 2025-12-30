Theory vfmTestDefs1298[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecoverInvalidSignature.json";
val defs = mapi (define_test "1298") tests;
