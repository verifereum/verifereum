open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0507Theory;
val () = new_theory "vfmTest0507";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0507") $ get_result_defs "vfmTestDefs0507";
val () = export_theory_no_docs ();
