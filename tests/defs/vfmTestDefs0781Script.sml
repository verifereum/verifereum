open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0781";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CreateOOGafterInitCodeReturndataSize.json";
val defs = mapi (define_test "0781") tests;
val () = export_theory_no_docs ();
