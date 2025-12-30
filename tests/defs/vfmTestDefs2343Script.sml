Theory vfmTestDefs2343[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcodecall_110_SuicideEnd2.json";
val defs = mapi (define_test "2343") tests;
