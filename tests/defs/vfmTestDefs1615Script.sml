Theory vfmTestDefs1615[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stReturnDataTest/returndatasize_after_failing_delegatecall/returndatasize_after_failing_delegatecall.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stReturnDataTest/returndatasize_after_failing_delegatecall/returndatasize_after_failing_delegatecall.json");
val defs = mapi (define_test "1615") tests;
