open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1369Theory;
val () = new_theory "vfmTest1369";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1369") $ get_result_defs "vfmTestDefs1369";
val () = export_theory_no_docs ();
