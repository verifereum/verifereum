open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0420Theory;
val () = new_theory "vfmTest0420";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0420") $ get_result_defs "vfmTestDefs0420";
val () = export_theory_no_docs ();
