open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0486Theory;
val () = new_theory "vfmTest0486";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0486") $ get_result_defs "vfmTestDefs0486";
val () = export_theory_no_docs ();
