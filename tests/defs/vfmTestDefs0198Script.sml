open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0198";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7251_consolidations/contract_deployment/system_contract_deployment.json";
val defs = mapi (define_test "0198") tests;
val () = export_theory_no_docs ();
