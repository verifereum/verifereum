open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0367";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/gas.json";
val defs = mapi (define_test "0367") tests;
val () = export_theory_no_docs ();
