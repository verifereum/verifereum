Theory vfmTestDefs2139[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stWalletTest/day_limit_set_daily_limit_no_data/day_limit_set_daily_limit_no_data.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stWalletTest/day_limit_set_daily_limit_no_data/day_limit_set_daily_limit_no_data.json");
val defs = mapi (define_test "2139") tests;
