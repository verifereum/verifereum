Theory vfmTestDefs0603[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreate2/create2_high_nonce_delegatecall/create2_high_nonce_delegatecall.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreate2/create2_high_nonce_delegatecall/create2_high_nonce_delegatecall.json");
val defs = mapi (define_test "0603") tests;
