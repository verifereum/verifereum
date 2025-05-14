open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0859";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/returndatacopy_afterFailing_create.json";
val defs = mapi (define_test "0859") tests;
val () = export_theory_no_docs ();
