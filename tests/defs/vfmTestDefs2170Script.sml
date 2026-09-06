Theory vfmTestDefs2170[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stWalletTest/wallet_execute_over_daily_limit_only_one_owner_new/wallet_execute_over_daily_limit_only_one_owner_new.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stWalletTest/wallet_execute_over_daily_limit_only_one_owner_new/wallet_execute_over_daily_limit_only_one_owner_new.json");
val defs = mapi (define_test "2170") tests;
