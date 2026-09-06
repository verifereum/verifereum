Theory vfmTestDefs1614[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stReturnDataTest/returndatasize_after_failing_callcode/returndatasize_after_failing_callcode.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stReturnDataTest/returndatasize_after_failing_callcode/returndatasize_after_failing_callcode.json");
val defs = mapi (define_test "1614") tests;
