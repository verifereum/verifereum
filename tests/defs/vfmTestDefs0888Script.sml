open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0888";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CodeInConstructor.json";
val defs = mapi (define_test "0888") tests;
val () = export_theory_no_docs ();
