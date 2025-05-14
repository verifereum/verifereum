open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0107";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip7516_blobgasfee/blobgasfee_opcode/blobbasefee_stack_overflow.json";
val defs = mapi (define_test "0107") tests;
val () = export_theory_no_docs ();
