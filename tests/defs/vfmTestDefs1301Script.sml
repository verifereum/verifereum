Theory vfmTestDefs1301[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecoverUnrecoverableKey.json";
val defs = mapi (define_test "1301") tests;
