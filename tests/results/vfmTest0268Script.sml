open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0268Theory;
val () = new_theory "vfmTest0268";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0268") $ get_result_defs "vfmTestDefs0268";
val () = export_theory_no_docs ();
