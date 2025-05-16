open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0893";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP158Specific/EXTCODESIZE_toNonExistent.json";
val defs = mapi (define_test "0893") tests;
val () = export_theory_no_docs ();
