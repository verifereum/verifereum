Theory vfmTestDefs0610[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreate2/create2_oo_gafter_init_code_returndata_size/create2_oo_gafter_init_code_returndata_size.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreate2/create2_oo_gafter_init_code_returndata_size/create2_oo_gafter_init_code_returndata_size.json");
val defs = mapi (define_test "0610") tests;
