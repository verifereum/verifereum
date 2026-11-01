Theory vfmTestDefs1562[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stLogTests/log2_log_memsize_zero/log2_log_memsize_zero.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stLogTests/log2_log_memsize_zero/log2_log_memsize_zero.json");
val defs = mapi (define_test "1562") tests;
