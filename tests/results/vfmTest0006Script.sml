open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0006Theory;
val () = new_theory "vfmTest0006";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0006") $ get_result_defs "vfmTestDefs0006";
val () = export_theory_no_docs ();
