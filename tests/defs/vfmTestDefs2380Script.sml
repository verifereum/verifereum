Theory vfmTestDefs2380[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticFlagEnabled/DelegatecallToPrecompileFromContractInitialization.json";
val defs = mapi (define_test "2380") tests;
