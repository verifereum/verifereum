open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0777";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CreateOOGafterInitCode.json";
val defs = mapi (define_test "0777") tests;
val () = export_theory_no_docs ();
