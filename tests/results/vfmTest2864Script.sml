open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2864Theory;
val () = new_theory "vfmTest2864";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2864") $ get_result_defs "vfmTestDefs2864";
val () = export_theory_no_docs ();
