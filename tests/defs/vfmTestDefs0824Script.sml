Theory vfmTestDefs0824[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/create2collisionSelfdestructed2.json";
val defs = mapi (define_test "0824") tests;
