Theory vfmTestDefs0663[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreateTest/create_oo_gafter_init_code_revert/create_oo_gafter_init_code_revert.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreateTest/create_oo_gafter_init_code_revert/create_oo_gafter_init_code_revert.json");
val defs = mapi (define_test "0663") tests;
