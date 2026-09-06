Theory vfmTestDefs1645[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stRevertTest/revert_opcode_in_create_returns/revert_opcode_in_create_returns.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stRevertTest/revert_opcode_in_create_returns/revert_opcode_in_create_returns.json");
val defs = mapi (define_test "1645") tests;
