open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0151";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/validation/test_sender_balance.json";
val defs = mapi (define_test "0151") tests;
val () = export_theory_no_docs ();
