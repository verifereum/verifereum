open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1909Theory;
val () = new_theory "vfmTest1909";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1909") $ get_result_defs "vfmTestDefs1909";
val () = export_theory_no_docs ();
