Theory vfmTest0859[no_sig_docs]
Ancestors vfmTestDefs0859
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0859";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
