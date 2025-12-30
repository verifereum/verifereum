Theory vfmTestDefs0777[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCodeCopyTest/ExtCodeCopyTargetRangeLongerThanCodeTests.json";
val defs = mapi (define_test "0777") tests;
