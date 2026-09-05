Theory vfmTestDefs0671[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreateTest/create_transaction_high_nonce/create_transaction_high_nonce.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreateTest/create_transaction_high_nonce/create_transaction_high_nonce.json");
val defs = mapi (define_test "0671") tests;
