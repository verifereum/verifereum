open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0118";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/push/push.json";
val defs = mapi (define_test "0118") tests;
val () = export_theory_no_docs ();
