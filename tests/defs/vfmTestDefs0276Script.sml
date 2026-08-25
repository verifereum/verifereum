Theory vfmTestDefs0276[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7002_el_triggerable_withdrawals/test_system_contract_deployment.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7002_el_triggerable_withdrawals/test_system_contract_deployment.json");
val defs = mapi (define_test "0276") tests;
