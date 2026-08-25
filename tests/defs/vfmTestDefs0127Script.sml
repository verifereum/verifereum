Theory vfmTestDefs0127[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/frontier/opcodes/test_call_large_args_offset_size_zero.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/frontier/opcodes/test_call_large_args_offset_size_zero.json");
val defs = mapi (define_test "0127") tests;
