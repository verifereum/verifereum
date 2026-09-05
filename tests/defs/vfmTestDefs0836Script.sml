Theory vfmTestDefs0836[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stLogTests/log3_log_memsize_too_high/log3_log_memsize_too_high.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stLogTests/log3_log_memsize_too_high/log3_log_memsize_too_high.json");
val defs = mapi (define_test "0836") tests;
