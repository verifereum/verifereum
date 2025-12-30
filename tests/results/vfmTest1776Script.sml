Theory vfmTest1776[no_sig_docs]
Ancestors vfmTestDefs1776
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1776";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
