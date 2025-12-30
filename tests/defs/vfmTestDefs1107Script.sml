Theory vfmTestDefs1107[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemExpandingEIP150Calls/CreateAndGasInsideCreateWithMemExpandingCalls.json";
val defs = mapi (define_test "1107") tests;
