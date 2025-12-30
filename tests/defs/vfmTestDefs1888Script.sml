Theory vfmTestDefs1888[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/create_callprecompile_returndatasize.json";
val defs = mapi (define_test "1888") tests;
