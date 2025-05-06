open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0110";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/all_opcodes/all_opcodes.json";
val defs = mapi (define_test "0110") tests;
val () = export_theory_no_docs ();
