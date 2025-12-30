Theory vfmTestDefs0890[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/callcodeOutput3.json";
val defs = mapi (define_test "0890") tests;
