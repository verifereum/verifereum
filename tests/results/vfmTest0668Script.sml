open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0668Theory;
val () = new_theory "vfmTest0668";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0668") $ get_result_defs "vfmTestDefs0668";
val () = export_theory_no_docs ();
