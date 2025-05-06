open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0318";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP4844_blobtransactions/opcodeBlobhashOutOfRange.json";
val defs = mapi (define_test "0318") tests;
val () = export_theory_no_docs ();
