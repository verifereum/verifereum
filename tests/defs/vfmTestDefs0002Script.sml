open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0002";
val tests = json_path_to_tests "../fixtures/blockchain_tests/byzantium/eip198_modexp_precompile/modexp/modexp.json";
val defs = mapi (define_test "0002") tests;
val () = export_theory_no_docs ();
