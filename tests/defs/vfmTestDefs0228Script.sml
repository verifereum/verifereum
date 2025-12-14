open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0228";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7951_p256verify_precompiles/test_precompile_before_fork.json";
val defs = mapi (define_test "0228") tests;
val () = export_theory_no_docs ();
