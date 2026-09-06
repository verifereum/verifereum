Theory vfmTestDefs2121[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stTransactionTest/suicides_and_send_money_to_itself_ether_destroyed/suicides_and_send_money_to_itself_ether_destroyed.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stTransactionTest/suicides_and_send_money_to_itself_ether_destroyed/suicides_and_send_money_to_itself_ether_destroyed.json");
val defs = mapi (define_test "2121") tests;
