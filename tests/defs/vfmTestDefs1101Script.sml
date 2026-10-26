Theory vfmTestDefs1101[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/frontier/validation/transaction/tx_max_nonce.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/frontier/validation/transaction/tx_max_nonce.json");
val defs = mapi (define_test "1101") tests;
