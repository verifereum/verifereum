open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0901";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CreateOOGafterMaxCodesize.json";
val defs = mapi (define_test "0901") tests;
val () = export_theory_no_docs ();
