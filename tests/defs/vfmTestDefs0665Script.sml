Theory vfmTestDefs0665[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreateTest/create_oog_after_init_code_returndata_size/create_oog_after_init_code_returndata_size.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreateTest/create_oog_after_init_code_returndata_size/create_oog_after_init_code_returndata_size.json");
val defs = mapi (define_test "0665") tests;
