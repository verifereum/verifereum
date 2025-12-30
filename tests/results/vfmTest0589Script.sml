Theory vfmTest0589[no_sig_docs]
Ancestors vfmTestDefs0589
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0589";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
