open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2257Theory;
val () = new_theory "vfmTest2257";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2257") $ get_result_defs "vfmTestDefs2257";
val () = export_theory_no_docs ();
