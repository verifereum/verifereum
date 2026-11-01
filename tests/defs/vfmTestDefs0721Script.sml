Theory vfmTestDefs0721[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_sstore/partially_discharged_advance_revoked_by_halt.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_sstore/partially_discharged_advance_revoked_by_halt.json");
val defs = mapi (define_test "0721") tests;
