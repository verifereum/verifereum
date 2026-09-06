Theory vfmTestDefs2159[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stWalletTest/wallet_add_owner_remove_pending_transaction/wallet_add_owner_remove_pending_transaction.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stWalletTest/wallet_add_owner_remove_pending_transaction/wallet_add_owner_remove_pending_transaction.json");
val defs = mapi (define_test "2159") tests;
