Theory vfmTestDefs2874[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stWalletTest/wallet_execute_over_daily_limit_multi_owner/wallet_execute_over_daily_limit_multi_owner.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stWalletTest/wallet_execute_over_daily_limit_multi_owner/wallet_execute_over_daily_limit_multi_owner.json");
val defs = mapi (define_test "2874") tests;
