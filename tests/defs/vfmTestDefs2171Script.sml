Theory vfmTestDefs2171[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stWalletTest/wallet_execute_under_daily_limit/wallet_execute_under_daily_limit.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stWalletTest/wallet_execute_under_daily_limit/wallet_execute_under_daily_limit.json");
val defs = mapi (define_test "2171") tests;
