Theory vfmTestDefs1473[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stEIP1559/sender_balance/sender_balance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stEIP1559/sender_balance/sender_balance.json");
val defs = mapi (define_test "1473") tests;
