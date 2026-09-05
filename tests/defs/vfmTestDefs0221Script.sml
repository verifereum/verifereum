Theory vfmTestDefs0221[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/frontier/validation/transaction/tx_max_nonce.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/frontier/validation/transaction/tx_max_nonce.json");
val defs = mapi (define_test "0221") tests;
