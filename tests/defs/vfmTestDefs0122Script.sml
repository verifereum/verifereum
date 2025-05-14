open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0122";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/precompiles/precompiles/precompiles.json";
val defs = mapi (define_test "0122") tests;
val () = export_theory_no_docs ();
