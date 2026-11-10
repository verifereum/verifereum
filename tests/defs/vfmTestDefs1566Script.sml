Theory vfmTestDefs1566[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stLogTests/log2_non_empty_mem_log_mem_size1_log_mem_start31/log2_non_empty_mem_log_mem_size1_log_mem_start31.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stLogTests/log2_non_empty_mem_log_mem_size1_log_mem_start31/log2_non_empty_mem_log_mem_size1_log_mem_start31.json");
val defs = mapi (define_test "1566") tests;
