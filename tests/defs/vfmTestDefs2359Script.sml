Theory vfmTestDefs2359[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stRevertTest/revert_opcode_in_init/revert_opcode_in_init.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stRevertTest/revert_opcode_in_init/revert_opcode_in_init.json");
val defs = mapi (define_test "2359") tests;
