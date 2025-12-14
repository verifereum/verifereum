open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0119";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/create/test_create_one_byte.json";
val defs = mapi (define_test "0119") tests;
val () = export_theory_no_docs ();
