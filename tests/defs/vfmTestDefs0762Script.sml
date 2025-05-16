open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0762";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE_EmptyContractAndCallIt_1wei.json";
val defs = mapi (define_test "0762") tests;
val () = export_theory_no_docs ();
