Theory vfmTestDefs0190[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/frontier/opcodes/all_opcodes/max_stack.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/frontier/opcodes/all_opcodes/max_stack.json");
val defs = mapi (define_test "0190") tests;
