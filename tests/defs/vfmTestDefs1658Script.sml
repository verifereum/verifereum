Theory vfmTestDefs1658[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stRevertTest/revert_prefound_empty_call_oog_paris/revert_prefound_empty_call_oog_paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stRevertTest/revert_prefound_empty_call_oog_paris/revert_prefound_empty_call_oog_paris.json");
val defs = mapi (define_test "1658") tests;
