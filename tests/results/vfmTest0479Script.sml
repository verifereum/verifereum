Theory vfmTest0479[no_sig_docs]
Ancestors vfmTestDefs0479
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0479";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
