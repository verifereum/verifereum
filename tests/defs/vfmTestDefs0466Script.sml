open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0466";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/pc.json";
val defs = mapi (define_test "0466") tests;
val () = export_theory_no_docs ();
