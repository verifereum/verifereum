open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0639Theory;
val () = new_theory "vfmTest0639";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0639") $ get_result_defs "vfmTestDefs0639";
val () = export_theory_no_docs ();
