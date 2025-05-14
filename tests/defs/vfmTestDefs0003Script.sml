open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0003";
val tests = json_path_to_tests "../fixtures/blockchain_tests/byzantium/eip198_modexp_precompile/modexp/modexp.json";
val defs = mapi (define_test "0003") tests;
val () = export_theory_no_docs ();
