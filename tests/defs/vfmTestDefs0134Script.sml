open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0134";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_cover_revert.json";
val defs = mapi (define_test "0134") tests;
val () = export_theory_no_docs ();
