Theory vfmTestDefs2782[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stSystemOperationsTest/current_account_balance/current_account_balance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stSystemOperationsTest/current_account_balance/current_account_balance.json");
val defs = mapi (define_test "2782") tests;
