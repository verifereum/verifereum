open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0985Theory;
val () = new_theory "vfmTest0985";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0985") $ get_result_defs "vfmTestDefs0985";
val () = export_theory_no_docs ();
