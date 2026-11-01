Theory vfmTestDefs0790[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/ext_code_opcodes_gas/ext_code_double_read_empty_account.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/ext_code_opcodes_gas/ext_code_double_read_empty_account.json");
val defs = mapi (define_test "0790") tests;
