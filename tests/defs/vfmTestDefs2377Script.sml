Theory vfmTestDefs2377[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticFlagEnabled/CallcodeToPrecompileFromContractInitialization.json";
val defs = mapi (define_test "2377") tests;
