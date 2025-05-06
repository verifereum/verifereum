open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1683Theory;
val () = new_theory "vfmTest1683";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1683") $ get_result_defs "vfmTestDefs1683";
val () = export_theory_no_docs ();
