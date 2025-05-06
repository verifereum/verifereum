open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0583Theory;
val () = new_theory "vfmTest0583";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0583") $ get_result_defs "vfmTestDefs0583";
val () = export_theory_no_docs ();
