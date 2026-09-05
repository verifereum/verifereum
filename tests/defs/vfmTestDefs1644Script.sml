Theory vfmTestDefs1644[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stRevertTest/revert_opcode_in_calls_on_non_empty_return_data/revert_opcode_in_calls_on_non_empty_return_data.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stRevertTest/revert_opcode_in_calls_on_non_empty_return_data/revert_opcode_in_calls_on_non_empty_return_data.json");
val defs = mapi (define_test "1644") tests;
