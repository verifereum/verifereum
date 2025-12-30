Theory vfmTestDefs0821[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/create2collisionCode2.json";
val defs = mapi (define_test "0821") tests;
