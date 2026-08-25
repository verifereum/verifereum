Theory vfmTestDefs0236[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/paris/security/test_tx_selfdestruct_balance_bug.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/paris/security/test_tx_selfdestruct_balance_bug.json");
val defs = mapi (define_test "0236") tests;
