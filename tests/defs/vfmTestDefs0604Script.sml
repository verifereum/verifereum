Theory vfmTestDefs0604[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreate2/create2_high_nonce_minus1/create2_high_nonce_minus1.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreate2/create2_high_nonce_minus1/create2_high_nonce_minus1.json");
val defs = mapi (define_test "0604") tests;
