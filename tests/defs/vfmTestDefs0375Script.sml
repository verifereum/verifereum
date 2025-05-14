open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0375";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/mstore.json";
val defs = mapi (define_test "0375") tests;
val () = export_theory_no_docs ();
