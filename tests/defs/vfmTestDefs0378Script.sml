open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0378";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/pop.json";
val defs = mapi (define_test "0378") tests;
val () = export_theory_no_docs ();
