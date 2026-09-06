Theory vfmTestDefs0644[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreateTest/create_address_warm_after_fail/create_address_warm_after_fail.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreateTest/create_address_warm_after_fail/create_address_warm_after_fail.json");
val defs = mapi (define_test "0644") tests;
