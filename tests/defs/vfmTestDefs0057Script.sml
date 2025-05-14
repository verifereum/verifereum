open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0057";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/blobhash_opcode/blobhash_scenarios.json";
val defs = mapi (define_test "0057") tests;
val () = export_theory_no_docs ();
