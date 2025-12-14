open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0164";
val tests = json_path_to_tests "../fixtures/blockchain_tests/london/validation/test_invalid_header.json";
val defs = mapi (define_test "0164") tests;
val () = export_theory_no_docs ();
