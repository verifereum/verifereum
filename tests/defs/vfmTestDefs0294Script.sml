Theory vfmTestDefs0294[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7623_increase_calldata_cost/test_transaction_validity_type_3.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7623_increase_calldata_cost/test_transaction_validity_type_3.json");
val defs = mapi (define_test "0294") tests;
