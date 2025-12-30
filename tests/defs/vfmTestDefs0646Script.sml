Theory vfmTestDefs0646[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/createInitFailStackSizeLargerThan1024.json";
val defs = mapi (define_test "0646") tests;
