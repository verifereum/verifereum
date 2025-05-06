open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0727Theory;
val () = new_theory "vfmTest0727";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0727") $ get_result_defs "vfmTestDefs0727";
val () = export_theory_no_docs ();
