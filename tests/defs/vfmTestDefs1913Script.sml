Theory vfmTestDefs1913[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatasize_after_oog_after_deeper.json";
val defs = mapi (define_test "1913") tests;
