Theory vfmTestDefs0173[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/frontier/create/create_one_byte/create_one_byte.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/frontier/create/create_one_byte/create_one_byte.json");
val defs = mapi (define_test "0173") tests;
