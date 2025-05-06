open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2450";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticFlagEnabled/CallWithZeroValueToPrecompileFromCalledContract.json";
val defs = mapi (define_test "2450") tests;
val () = export_theory_no_docs ();
