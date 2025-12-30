Theory vfmTestDefs0823[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/create2collisionSelfdestructed.json";
val defs = mapi (define_test "0823") tests;
