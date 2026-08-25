Theory vfmTestDefs2507[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stWalletTest/dayLimitSetDailyLimitNoData.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stWalletTest/dayLimitSetDailyLimitNoData.json");
val defs = mapi (define_test "2507") tests;
