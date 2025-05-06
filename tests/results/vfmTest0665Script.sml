open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0665Theory;
val () = new_theory "vfmTest0665";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0665") $ get_result_defs "vfmTestDefs0665";
val () = export_theory_no_docs ();
