Theory vfmTestDefs0831[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stLogTests/log2_non_empty_mem_log_mem_size1/log2_non_empty_mem_log_mem_size1.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stLogTests/log2_non_empty_mem_log_mem_size1/log2_non_empty_mem_log_mem_size1.json");
val defs = mapi (define_test "0831") tests;
