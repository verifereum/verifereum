Theory vfmTestDefs0847[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stLogTests/log4_log_memsize_zero/log4_log_memsize_zero.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stLogTests/log4_log_memsize_zero/log4_log_memsize_zero.json");
val defs = mapi (define_test "0847") tests;
