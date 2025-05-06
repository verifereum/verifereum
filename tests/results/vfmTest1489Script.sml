open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1489Theory;
val () = new_theory "vfmTest1489";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1489") $ get_result_defs "vfmTestDefs1489";
val () = export_theory_no_docs ();
