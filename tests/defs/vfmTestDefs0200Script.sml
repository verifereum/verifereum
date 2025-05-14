open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0200";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7251_consolidations/modified_consolidation_contract/system_contract_errors.json";
val defs = mapi (define_test "0200") tests;
val () = export_theory_no_docs ();
