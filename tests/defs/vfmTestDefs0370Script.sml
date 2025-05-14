open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0370";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/jumpi.json";
val defs = mapi (define_test "0370") tests;
val () = export_theory_no_docs ();
