Theory vfmTest0674[no_sig_docs]
Ancestors vfmTestDefs0674
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0674";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
