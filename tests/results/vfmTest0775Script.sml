Theory vfmTest0775[no_sig_docs]
Ancestors vfmTestDefs0775
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0775";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
