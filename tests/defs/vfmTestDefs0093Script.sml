open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0093";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/selfdestruct/calling_from_pre_existing_contract_to_new_contract.json";
val defs = mapi (define_test "0093") tests;
val () = export_theory_no_docs ();
