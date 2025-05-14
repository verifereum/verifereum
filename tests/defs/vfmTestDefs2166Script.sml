open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2166";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/StaticcallToPrecompileFromContractInitialization.json";
val defs = mapi (define_test "2166") tests;
val () = export_theory_no_docs ();
