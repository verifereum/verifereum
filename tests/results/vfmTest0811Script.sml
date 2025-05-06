open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0811Theory;
val () = new_theory "vfmTest0811";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0811") $ get_result_defs "vfmTestDefs0811";
val () = export_theory_no_docs ();
