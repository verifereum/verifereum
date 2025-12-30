Theory vfmTestDefs0903[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/delegatecodeDynamicCode2SelfCall.json";
val defs = mapi (define_test "0903") tests;
