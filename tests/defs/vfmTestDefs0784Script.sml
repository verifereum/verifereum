open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0784";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CreateOOGafterMaxCodesize.json";
val defs = mapi (define_test "0784") tests;
val () = export_theory_no_docs ();
