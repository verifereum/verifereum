open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0206Theory;
val () = new_theory "vfmTest0206";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0206") $ get_result_defs "vfmTestDefs0206";
val () = export_theory_no_docs ();
