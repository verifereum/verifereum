open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0131";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_calldataload.json";
val defs = mapi (define_test "0131") tests;
val () = export_theory_no_docs ();
