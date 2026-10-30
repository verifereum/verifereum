Theory vfmTestDefs2361[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stRevertTest/revert_opcode_return/revert_opcode_return.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stRevertTest/revert_opcode_return/revert_opcode_return.json");
val defs = mapi (define_test "2361") tests;
