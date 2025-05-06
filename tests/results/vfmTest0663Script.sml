open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0663Theory;
val () = new_theory "vfmTest0663";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0663") $ get_result_defs "vfmTestDefs0663";
val () = export_theory_no_docs ();
