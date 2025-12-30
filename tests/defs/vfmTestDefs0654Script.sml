Theory vfmTestDefs0654[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/createJS_NoCollision.json";
val defs = mapi (define_test "0654") tests;
