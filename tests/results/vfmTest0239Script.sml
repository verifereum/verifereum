open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0239Theory;
val () = new_theory "vfmTest0239";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0239") $ get_result_defs "vfmTestDefs0239";
val () = export_theory_no_docs ();
