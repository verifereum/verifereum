open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0054";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/blobhash_opcode/blobhash_gas_cost.json";
val defs = mapi (define_test "0054") tests;
val () = export_theory_no_docs ();
