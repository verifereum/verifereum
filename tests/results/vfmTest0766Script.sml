open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0766Theory;
val () = new_theory "vfmTest0766";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0766") $ get_result_defs "vfmTestDefs0766";
val () = export_theory_no_docs ();
