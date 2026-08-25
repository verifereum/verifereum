Theory vfmTestDefs0129[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/frontier/opcodes/test_call_memory_expands_on_early_revert.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/frontier/opcodes/test_call_memory_expands_on_early_revert.json");
val defs = mapi (define_test "0129") tests;
