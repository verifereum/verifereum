Theory vfmTestDefs1637[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stRevertTest/revert_in_delegate_call/revert_in_delegate_call.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stRevertTest/revert_in_delegate_call/revert_in_delegate_call.json");
val defs = mapi (define_test "1637") tests;
