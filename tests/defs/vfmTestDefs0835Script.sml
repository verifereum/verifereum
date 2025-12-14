open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0835";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE2_CallData.json";
val defs = mapi (define_test "0835") tests;
val () = export_theory_no_docs ();
