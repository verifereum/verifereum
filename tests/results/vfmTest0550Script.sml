open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0550Theory;
val () = new_theory "vfmTest0550";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0550") $ get_result_defs "vfmTestDefs0550";
val () = export_theory_no_docs ();
