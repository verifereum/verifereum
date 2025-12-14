open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0184";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7883_modexp_gas_increase/test_contract_creation_transaction.json";
val defs = mapi (define_test "0184") tests;
val () = export_theory_no_docs ();
