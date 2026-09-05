Theory vfmTestDefs0659[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreateTest/create_oo_gafter_init_code/create_oo_gafter_init_code.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreateTest/create_oo_gafter_init_code/create_oo_gafter_init_code.json");
val defs = mapi (define_test "0659") tests;
