Theory vfmTestDefs2187[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_InternalCallHittingGasLimit2.json";
val defs = mapi (define_test "2187") tests;
