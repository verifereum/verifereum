Theory vfmTestDefs0736[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_sstore/sstore_restoration_nonzero_no_state_refund.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_sstore/sstore_restoration_nonzero_no_state_refund.json");
val defs = mapi (define_test "0736") tests;
