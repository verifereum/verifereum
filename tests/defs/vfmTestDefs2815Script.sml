open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2815";
val tests = json_path_to_tests "../fixtures/blockchain_tests/zkevm/worst_compute/worst_modexp.json";
val defs = mapi (define_test "2815") tests;
val () = export_theory_no_docs ();
