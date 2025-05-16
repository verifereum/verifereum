open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0749";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE_AcreateB_BSuicide_BStore.json";
val defs = mapi (define_test "0749") tests;
val () = export_theory_no_docs ();
