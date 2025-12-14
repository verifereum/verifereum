open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0096";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_calling_from_new_contract_to_pre_existing_contract.json";
val defs = mapi (define_test "0096") tests;
val () = export_theory_no_docs ();
