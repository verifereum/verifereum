Theory vfmTestDefs2374[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticFlagEnabled/CallWithZeroValueToPrecompileFromContractInitialization.json";
val defs = mapi (define_test "2374") tests;
