open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0143Theory;
val () = new_theory "vfmTest0143";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0143") $ get_result_defs "vfmTestDefs0143";
val () = export_theory_no_docs ();
