Theory vfmTest0344[no_sig_docs]
Ancestors vfmTestDefs0344
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0344";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
