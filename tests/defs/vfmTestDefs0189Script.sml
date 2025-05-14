open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0189";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7002_el_triggerable_withdrawals/contract_deployment/system_contract_deployment.json";
val defs = mapi (define_test "0189") tests;
val () = export_theory_no_docs ();
