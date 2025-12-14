open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0792";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/CREATE2_Suicide.json";
val defs = mapi (define_test "0792") tests;
val () = export_theory_no_docs ();
