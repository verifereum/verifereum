open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0082";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip5656_mcopy/mcopy/mcopy_on_empty_memory.json";
val defs = mapi (define_test "0082") tests;
val () = export_theory_no_docs ();
