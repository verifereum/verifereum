open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0136";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_dup.json";
val defs = mapi (define_test "0136") tests;
val () = export_theory_no_docs ();
