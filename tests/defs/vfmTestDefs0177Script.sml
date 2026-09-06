Theory vfmTestDefs0177[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/frontier/create/create_preimage_layout/create_preimage_layout_increment_nonce.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/frontier/create/create_preimage_layout/create_preimage_layout_increment_nonce.json");
val defs = mapi (define_test "0177") tests;
