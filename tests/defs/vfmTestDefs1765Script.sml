Theory vfmTestDefs1765[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSpecialTest/tx_e1c174e2/tx_e1c174e2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSpecialTest/tx_e1c174e2/tx_e1c174e2.json");
val defs = mapi (define_test "1765") tests;
