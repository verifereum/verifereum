Theory vfmTestDefs2091[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/suicide_send_ether_post_death/suicide_send_ether_post_death.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/suicide_send_ether_post_death/suicide_send_ether_post_death.json");
val defs = mapi (define_test "2091") tests;
