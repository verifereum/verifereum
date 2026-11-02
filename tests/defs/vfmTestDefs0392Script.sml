Theory vfmTestDefs0392[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7981_increase_access_list_cost/transaction_validity/valid_gas_limits_with_access_list.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7981_increase_access_list_cost/transaction_validity/valid_gas_limits_with_access_list.json");
val defs = mapi (define_test "0392") tests;
