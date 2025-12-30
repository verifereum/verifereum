Theory vfmTestDefs2381[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticFlagEnabled/DelegatecallToPrecompileFromTransaction.json";
val defs = mapi (define_test "2381") tests;
