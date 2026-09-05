Theory vfmTestDefs0849[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stLogTests/log4_non_empty_mem/log4_non_empty_mem.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stLogTests/log4_non_empty_mem/log4_non_empty_mem.json");
val defs = mapi (define_test "0849") tests;
