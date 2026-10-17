Theory vfmTestDefs0148[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/constantinople/eip1014_create2/create_returndata/create2_return_data.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/constantinople/eip1014_create2/create_returndata/create2_return_data.json");
val defs = mapi (define_test "0148") tests;
