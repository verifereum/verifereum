open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0957";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stHomesteadSpecific/createContractViaContract.json";
val defs = mapi (define_test "0957") tests;
val () = export_theory_no_docs ();
