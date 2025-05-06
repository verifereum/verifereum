open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0825";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/Create2OOGafterInitCodeRevert2.json";
val defs = mapi (define_test "0825") tests;
val () = export_theory_no_docs ();
