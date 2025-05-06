open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0111";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/all_opcodes/cover_revert.json";
val defs = mapi (define_test "0111") tests;
val () = export_theory_no_docs ();
