Theory vfmTestDefs1079[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/frontier/opcodes/dynamic_jump/dynamic_jump_invalid_destination.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/frontier/opcodes/dynamic_jump/dynamic_jump_invalid_destination.json");
val defs = mapi (define_test "1079") tests;
