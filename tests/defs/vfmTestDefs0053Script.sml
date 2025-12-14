open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0053";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_call_opcode_types.json";
val defs = mapi (define_test "0053") tests;
val () = export_theory_no_docs ();
