open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2049";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/StaticcallToPrecompileFromTransaction.json";
val defs = mapi (define_test "2049") tests;
val () = export_theory_no_docs ();
