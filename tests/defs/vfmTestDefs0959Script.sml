open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0959";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stHomesteadSpecific/createContractViaTransactionCost53000.json";
val defs = mapi (define_test "0959") tests;
val () = export_theory_no_docs ();
