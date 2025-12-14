open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0090";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip5656_mcopy/test_mcopy_huge_memory_expansion.json";
val defs = mapi (define_test "0090") tests;
val () = export_theory_no_docs ();
