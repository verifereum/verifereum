Theory vfmTestDefs0638[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callcodeOutput3partial.json";
val defs = mapi (define_test "0638") tests;
