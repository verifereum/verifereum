open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1713Theory;
val () = new_theory "vfmTest1713";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1713") $ get_result_defs "vfmTestDefs1713";
val () = export_theory_no_docs ();
