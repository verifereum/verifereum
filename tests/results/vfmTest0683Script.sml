open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0683Theory;
val () = new_theory "vfmTest0683";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0683") $ get_result_defs "vfmTestDefs0683";
val () = export_theory_no_docs ();
