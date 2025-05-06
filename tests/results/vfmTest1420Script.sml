open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1420Theory;
val () = new_theory "vfmTest1420";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1420") $ get_result_defs "vfmTestDefs1420";
val () = export_theory_no_docs ();
