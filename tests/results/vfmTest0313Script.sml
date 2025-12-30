Theory vfmTest0313[no_sig_docs]
Ancestors vfmTestDefs0313
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0313";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
