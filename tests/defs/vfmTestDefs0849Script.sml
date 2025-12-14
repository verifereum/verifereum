open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0849";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE_EmptyContractWithStorageAndCallIt_1wei.json";
val defs = mapi (define_test "0849") tests;
val () = export_theory_no_docs ();
