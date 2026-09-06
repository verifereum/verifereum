Theory vfmTestDefs2075[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/create_with_invalid_opcode/create_with_invalid_opcode.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/create_with_invalid_opcode/create_with_invalid_opcode.json");
val defs = mapi (define_test "2075") tests;
