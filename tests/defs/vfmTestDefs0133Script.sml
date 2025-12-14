open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0133";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_constant_gas.json";
val defs = mapi (define_test "0133") tests;
val () = export_theory_no_docs ();
