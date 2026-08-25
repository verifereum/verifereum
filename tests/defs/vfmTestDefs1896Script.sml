Theory vfmTestDefs1896[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_after_successful_callcode.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_after_successful_callcode.json");
val defs = mapi (define_test "1896") tests;
