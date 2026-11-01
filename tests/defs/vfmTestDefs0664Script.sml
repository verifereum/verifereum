Theory vfmTestDefs0664[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_reservoir/subcall_revert_does_not_leak_grandchild_storage_clear_credit.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_reservoir/subcall_revert_does_not_leak_grandchild_storage_clear_credit.json");
val defs = mapi (define_test "0664") tests;
