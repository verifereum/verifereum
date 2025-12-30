Theory vfmTestDefs0887[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/callOutput3partial.json";
val defs = mapi (define_test "0887") tests;
