Theory vfmTestDefs0384[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7981_increase_access_list_cost/execution_gas/execution_gas_after_access_list_surcharge.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7981_increase_access_list_cost/execution_gas/execution_gas_after_access_list_surcharge.json");
val defs = mapi (define_test "0384") tests;
