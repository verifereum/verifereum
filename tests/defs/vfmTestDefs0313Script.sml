Theory vfmTestDefs0313[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_delegation_clearing_failing_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7702_set_code_tx/test_delegation_clearing_failing_tx.json");
val defs = mapi (define_test "0313") tests;
