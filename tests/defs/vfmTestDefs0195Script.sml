Theory vfmTestDefs0195[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/frontier/opcodes/call/call_memory_expands_on_early_revert.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/frontier/opcodes/call/call_memory_expands_on_early_revert.json");
val defs = mapi (define_test "0195") tests;
