open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0372";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/mstore8.json";
val defs = mapi (define_test "0372") tests;
val () = export_theory_no_docs ();
