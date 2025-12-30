Theory vfmTestDefs0820[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/create2collisionCode.json";
val defs = mapi (define_test "0820") tests;
