open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0677";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/createInitFailUndefinedInstruction.json";
val defs = mapi (define_test "0677") tests;
val () = export_theory_no_docs ();
