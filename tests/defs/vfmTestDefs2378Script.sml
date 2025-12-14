open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2378";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticFlagEnabled/CallcodeToPrecompileFromTransaction.json";
val defs = mapi (define_test "2378") tests;
val () = export_theory_no_docs ();
