open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0376Theory;
val () = new_theory "vfmTest0376";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0376") $ get_result_defs "vfmTestDefs0376";
val () = export_theory_no_docs ();
