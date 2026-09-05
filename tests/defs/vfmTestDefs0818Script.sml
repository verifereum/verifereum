Theory vfmTestDefs0818[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stLogTests/log1_log_memsize_too_high/log1_log_memsize_too_high.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stLogTests/log1_log_memsize_too_high/log1_log_memsize_too_high.json");
val defs = mapi (define_test "0818") tests;
