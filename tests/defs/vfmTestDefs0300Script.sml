Theory vfmTestDefs0300[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/paris/security/selfdestruct_balance_bug/tx_selfdestruct_balance_bug.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/paris/security/selfdestruct_balance_bug/tx_selfdestruct_balance_bug.json");
val defs = mapi (define_test "0300") tests;
