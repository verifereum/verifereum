Theory vfmTestDefs2347[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7623_increase_calldata_cost/transaction_validity/transaction_validity_type_0.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7623_increase_calldata_cost/transaction_validity/transaction_validity_type_0.json");
val defs = mapi (define_test "2347") tests;
