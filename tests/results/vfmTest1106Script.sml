Theory vfmTest1106[no_sig_docs]
Ancestors vfmTestDefs1106
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1106";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
