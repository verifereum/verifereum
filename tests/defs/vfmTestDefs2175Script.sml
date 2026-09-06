Theory vfmTestDefs2175[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stWalletTest/wallet_remove_owner_remove_pending_transaction/wallet_remove_owner_remove_pending_transaction.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stWalletTest/wallet_remove_owner_remove_pending_transaction/wallet_remove_owner_remove_pending_transaction.json");
val defs = mapi (define_test "2175") tests;
