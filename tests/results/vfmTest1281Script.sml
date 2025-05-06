open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1281Theory;
val () = new_theory "vfmTest1281";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1281") $ get_result_defs "vfmTestDefs1281";
val () = export_theory_no_docs ();
