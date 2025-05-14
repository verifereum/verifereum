open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0084";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip5656_mcopy/mcopy/valid_mcopy_operations.json";
val defs = mapi (define_test "0084") tests;
val () = export_theory_no_docs ();
