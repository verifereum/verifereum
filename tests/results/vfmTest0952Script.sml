open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0952Theory;
val () = new_theory "vfmTest0952";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0952") $ get_result_defs "vfmTestDefs0952";
val () = export_theory_no_docs ();
