Theory vfmTestDefs2379[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticFlagEnabled/DelegatecallToPrecompileFromCalledContract.json";
val defs = mapi (define_test "2379") tests;
