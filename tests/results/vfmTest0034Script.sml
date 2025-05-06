open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0034Theory;
val () = new_theory "vfmTest0034";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0034") $ get_result_defs "vfmTestDefs0034";
val () = export_theory_no_docs ();
