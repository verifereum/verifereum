open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1717Theory;
val () = new_theory "vfmTest1717";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1717") $ get_result_defs "vfmTestDefs1717";
val () = export_theory_no_docs ();
