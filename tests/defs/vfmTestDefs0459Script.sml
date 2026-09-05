Theory vfmTestDefs0459[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallCreateCallCodeTest/create_init_fail_oo_gduring_init/create_init_fail_oo_gduring_init.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallCreateCallCodeTest/create_init_fail_oo_gduring_init/create_init_fail_oo_gduring_init.json");
val defs = mapi (define_test "0459") tests;
