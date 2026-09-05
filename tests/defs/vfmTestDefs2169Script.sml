Theory vfmTestDefs2169[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stWalletTest/wallet_execute_over_daily_limit_only_one_owner/wallet_execute_over_daily_limit_only_one_owner.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stWalletTest/wallet_execute_over_daily_limit_only_one_owner/wallet_execute_over_daily_limit_only_one_owner.json");
val defs = mapi (define_test "2169") tests;
