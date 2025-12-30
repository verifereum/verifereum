Theory vfmTestDefs1883[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/call_ecrec_success_empty_then_returndatasize.json";
val defs = mapi (define_test "1883") tests;
