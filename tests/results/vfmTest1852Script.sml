open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1852Theory;
val () = new_theory "vfmTest1852";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1852") $ get_result_defs "vfmTestDefs1852";
val () = export_theory_no_docs ();
