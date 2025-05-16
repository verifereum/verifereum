open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2814";
val tests = json_path_to_tests "../fixtures/blockchain_tests/zkevm/worst_compute/worst_keccak.json";
val defs = mapi (define_test "2814") tests;
val () = export_theory_no_docs ();
