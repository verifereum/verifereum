Theory vfmTestDefs1017[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/constantinople/eip1014_create2/create_returndata/create2_return_data.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/constantinople/eip1014_create2/create_returndata/create2_return_data.json");
val defs = mapi (define_test "1017") tests;
