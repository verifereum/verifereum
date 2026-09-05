Theory vfmTestDefs1605[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stReturnDataTest/returndatacopy_following_failing_call/returndatacopy_following_failing_call.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stReturnDataTest/returndatacopy_following_failing_call/returndatacopy_following_failing_call.json");
val defs = mapi (define_test "1605") tests;
