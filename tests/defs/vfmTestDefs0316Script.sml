open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0316";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_deploying_delegation_designation_contract.json";
val defs = mapi (define_test "0316") tests;
val () = export_theory_no_docs ();
