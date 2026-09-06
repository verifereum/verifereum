Theory vfmTestDefs0736[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP1559/sender_balance/sender_balance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP1559/sender_balance/sender_balance.json");
val defs = mapi (define_test "0736") tests;
