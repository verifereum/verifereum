Theory vfmTestDefs1613[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stRevertTest/loop_calls_then_revert/loop_calls_then_revert.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stRevertTest/loop_calls_then_revert/loop_calls_then_revert.json");
val defs = mapi (define_test "1613") tests;
