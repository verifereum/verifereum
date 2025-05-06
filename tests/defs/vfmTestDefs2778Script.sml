open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2778";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_perturb_zeropoint_by_curve_order.json";
val defs = mapi (define_test "2778") tests;
val () = export_theory_no_docs ();
