open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0246Theory;
val () = new_theory "vfmTest0246";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0246") $ get_result_defs "vfmTestDefs0246";
val () = export_theory_no_docs ();
