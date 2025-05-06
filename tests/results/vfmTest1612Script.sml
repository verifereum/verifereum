open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1612Theory;
val () = new_theory "vfmTest1612";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1612") $ get_result_defs "vfmTestDefs1612";
val () = export_theory_no_docs ();
