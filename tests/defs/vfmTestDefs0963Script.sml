Theory vfmTestDefs0963[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stEIP1559/outOfFunds.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stEIP1559/outOfFunds.json");
val defs = mapi (define_test "0963") tests;
