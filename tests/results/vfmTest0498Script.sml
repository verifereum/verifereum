Theory vfmTest0498[no_sig_docs]
Ancestors vfmTestDefs0498
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0498";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
