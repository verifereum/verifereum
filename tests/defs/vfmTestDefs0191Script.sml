open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0191";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7251_consolidations/consolidations/consolidation_requests.json";
val defs = mapi (define_test "0191") tests;
val () = export_theory_no_docs ();
