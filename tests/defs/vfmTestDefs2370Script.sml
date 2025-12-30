Theory vfmTestDefs2370[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticFlagEnabled/CallWithNOTZeroValueToPrecompileFromCalledContract.json";
val defs = mapi (define_test "2370") tests;
