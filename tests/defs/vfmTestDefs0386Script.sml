open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0386";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmTests/random.json";
val defs = mapi (define_test "0386") tests;
val () = export_theory_no_docs ();
