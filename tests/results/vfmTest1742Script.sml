open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1742Theory;
val () = new_theory "vfmTest1742";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1742") $ get_result_defs "vfmTestDefs1742";
val () = export_theory_no_docs ();
