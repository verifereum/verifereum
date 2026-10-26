Theory vfmTestDefs0625[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_ordering/state_charge_oog_full_burn_no_state_credit.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_ordering/state_charge_oog_full_burn_no_state_credit.json");
val defs = mapi (define_test "0625") tests;
