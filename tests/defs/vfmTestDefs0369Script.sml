open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0369";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/jumpToPush.json";
val defs = mapi (define_test "0369") tests;
val () = export_theory_no_docs ();
