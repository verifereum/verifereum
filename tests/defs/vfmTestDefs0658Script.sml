Theory vfmTestDefs0658[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreateTest/create_high_nonce_minus1/create_high_nonce_minus1.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreateTest/create_high_nonce_minus1/create_high_nonce_minus1.json");
val defs = mapi (define_test "0658") tests;
