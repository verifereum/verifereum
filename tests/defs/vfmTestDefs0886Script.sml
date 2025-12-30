Theory vfmTestDefs0886[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/callOutput3.json";
val defs = mapi (define_test "0886") tests;
