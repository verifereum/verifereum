open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0117";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/dup/dup.json";
val defs = mapi (define_test "0117") tests;
val () = export_theory_no_docs ();
