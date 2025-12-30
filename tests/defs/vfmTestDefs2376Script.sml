Theory vfmTestDefs2376[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticFlagEnabled/CallcodeToPrecompileFromCalledContract.json";
val defs = mapi (define_test "2376") tests;
