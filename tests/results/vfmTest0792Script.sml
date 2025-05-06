open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0792Theory;
val () = new_theory "vfmTest0792";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0792") $ get_result_defs "vfmTestDefs0792";
val () = export_theory_no_docs ();
