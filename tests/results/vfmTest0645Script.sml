open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0645Theory;
val () = new_theory "vfmTest0645";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0645") $ get_result_defs "vfmTestDefs0645";
val () = export_theory_no_docs ();
