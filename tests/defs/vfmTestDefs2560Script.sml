open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2560";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/PointAtInfinityECRecover.json";
val defs = mapi (define_test "2560") tests;
val () = export_theory_no_docs ();
