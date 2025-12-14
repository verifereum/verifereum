open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2371";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticFlagEnabled/CallWithNOTZeroValueToPrecompileFromContractInitialization.json";
val defs = mapi (define_test "2371") tests;
val () = export_theory_no_docs ();
