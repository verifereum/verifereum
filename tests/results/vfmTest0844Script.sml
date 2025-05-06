open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0844Theory;
val () = new_theory "vfmTest0844";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0844") $ get_result_defs "vfmTestDefs0844";
val () = export_theory_no_docs ();
