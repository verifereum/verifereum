open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0194";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7251_consolidations/contract_deployment/system_contract_deployment.json";
val defs = mapi (define_test "0194") tests;
val () = export_theory_no_docs ();
