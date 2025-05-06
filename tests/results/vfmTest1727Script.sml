open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1727Theory;
val () = new_theory "vfmTest1727";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1727") $ get_result_defs "vfmTestDefs1727";
val () = export_theory_no_docs ();
