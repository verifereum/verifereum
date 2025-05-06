open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1479Theory;
val () = new_theory "vfmTest1479";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1479") $ get_result_defs "vfmTestDefs1479";
val () = export_theory_no_docs ();
