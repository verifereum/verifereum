open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2664";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_perturb_zeropoint_by_curve_order.json";
val defs = mapi (define_test "2664") tests;
val () = export_theory_no_docs ();
