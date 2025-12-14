open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0282";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7251_consolidations/test_consolidation_requests_during_fork.json";
val defs = mapi (define_test "0282") tests;
val () = export_theory_no_docs ();
