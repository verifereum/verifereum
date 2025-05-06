open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0488Theory;
val () = new_theory "vfmTest0488";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0488") $ get_result_defs "vfmTestDefs0488";
val () = export_theory_no_docs ();
