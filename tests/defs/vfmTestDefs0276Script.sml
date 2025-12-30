Theory vfmTestDefs0276[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7002_el_triggerable_withdrawals/test_system_contract_deployment.json";
val defs = mapi (define_test "0276") tests;
