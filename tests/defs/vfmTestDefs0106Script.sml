open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0106";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip7516_blobgasfee/blobgasfee_opcode/blobbasefee_out_of_gas.json";
val defs = mapi (define_test "0106") tests;
val () = export_theory_no_docs ();
