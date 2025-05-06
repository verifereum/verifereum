open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2683Theory;
val () = new_theory "vfmTest2683";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2683") $ get_result_defs "vfmTestDefs2683";
val () = export_theory_no_docs ();
