open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0546Theory;
val () = new_theory "vfmTest0546";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0546") $ get_result_defs "vfmTestDefs0546";
val () = export_theory_no_docs ();
