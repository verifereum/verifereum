Theory vfmTestDefs1887[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/clearReturnBuffer.json";
val defs = mapi (define_test "1887") tests;
