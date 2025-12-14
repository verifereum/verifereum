open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0112";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip7516_blobgasfee/test_blobbasefee_during_fork.json";
val defs = mapi (define_test "0112") tests;
val () = export_theory_no_docs ();
