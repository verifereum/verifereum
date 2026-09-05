Theory vfmTestDefs0460[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallCreateCallCodeTest/create_init_fail_oo_gduring_init2/create_init_fail_oo_gduring_init2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallCreateCallCodeTest/create_init_fail_oo_gduring_init2/create_init_fail_oo_gduring_init2.json");
val defs = mapi (define_test "0460") tests;
