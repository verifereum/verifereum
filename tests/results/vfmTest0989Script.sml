open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0989Theory;
val () = new_theory "vfmTest0989";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0989") $ get_result_defs "vfmTestDefs0989";
val () = export_theory_no_docs ();
