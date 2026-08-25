Theory vfmTestDefs0153[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/frontier/validation/test_tx_nonce.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/frontier/validation/test_tx_nonce.json");
val defs = mapi (define_test "0153") tests;
