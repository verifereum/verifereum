open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0109";
val tests = json_path_to_tests "../fixtures/blockchain_tests/constantinople/eip1014_create2/recreate/recreate.json";
val defs = mapi (define_test "0109") tests;
val () = export_theory_no_docs ();
