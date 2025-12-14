open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0137";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_gas.json";
val defs = mapi (define_test "0137") tests;
val () = export_theory_no_docs ();
