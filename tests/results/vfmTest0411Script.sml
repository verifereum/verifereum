open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0411Theory;
val () = new_theory "vfmTest0411";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0411") $ get_result_defs "vfmTestDefs0411";
val () = export_theory_no_docs ();
