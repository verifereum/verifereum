Theory vfmTestDefs2006[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_log1_log_memsize_too_high/static_log1_log_memsize_too_high.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_log1_log_memsize_too_high/static_log1_log_memsize_too_high.json");
val defs = mapi (define_test "2006") tests;
