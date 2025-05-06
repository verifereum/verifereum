open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0649Theory;
val () = new_theory "vfmTest0649";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0649") $ get_result_defs "vfmTestDefs0649";
val () = export_theory_no_docs ();
